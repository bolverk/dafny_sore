// Plain, unverified display utility: turns a Regex AST into standard regex syntax
// (Python `re`-compatible, using (?:...) non-capturing groups). This is NOT part of the
// proved core (Regex.dfy/Chain.dfy/Infer.dfy) - it carries no Dafny-level correctness
// theorem of its own. Its output is instead checked at runtime by sore.py, which
// re-parses the printed text with Python's `re` module and confirms it actually accepts
// every input string before printing anything to the user.
include "Regex.dfy"

module Print {
  import opened RegexCore

  // Escape characters that are regex metacharacters in Python's `re` syntax.
  function EscapeChar(c: char): string {
    if c == '.' || c == '^' || c == '$' || c == '*' || c == '+' || c == '?' ||
       c == '(' || c == ')' || c == '[' || c == ']' || c == '{' || c == '}' ||
       c == '|' || c == '\\'
    then "\\" + [c]
    else [c]
  }

  // True iff every leaf of r is a Sym (any nesting of Union over Sym leaves, no Concat/
  // Star/Opt/Plus/Empty/Eps anywhere inside) - such a Union prints as a bracket character
  // class ([abc]) instead of an alternation ((?:a|b|c)), which reads as one atomic unit
  // just like a single Sym does, so it needs no (?:...) wrapping either.
  function IsAllSymUnion(r: Regex): bool
    decreases r
  {
    match r
    case Sym(_) => true
    case Union(r1, r2) => IsAllSymUnion(r1) && IsAllSymUnion(r2)
    case _ => false
  }

  function CollectSyms(r: Regex): seq<char>
    decreases r
  {
    match r
    case Sym(c) => [c]
    case Union(r1, r2) => CollectSyms(r1) + CollectSyms(r2)
    case _ => []
  }

  // Escape characters that are metacharacters *inside* a [...] character class in
  // Python's `re` syntax (a different, smaller set than EscapeChar's, since most regex
  // metacharacters lose their special meaning inside a class). `^` only needs escaping
  // as the first character (where it would mean negation) but escaping it unconditionally
  // is always safe too, so that's what's done here for simplicity.
  function EscapeClassChar(c: char): string {
    if c == ']' || c == '^' || c == '-' || c == '\\' then "\\" + [c] else [c]
  }

  function PrintCharClass(cs: seq<char>): string
    decreases cs
  {
    if cs == [] then "" else EscapeClassChar(cs[0]) + PrintCharClass(cs[1..])
  }

  // Does r need (?:...) wrapping when it appears as the operand of a repetition
  // operator (Star/Plus/Opt/RepRange), or as one side of a Concat? True for anything
  // that isn't already a single atom (Sym/Eps/Empty), except an all-Sym Union - printed
  // as a bracket class, [abc] is atomic too.
  function NeedsGroup(r: Regex): bool {
    match r
    case Sym(_) => false
    case Eps => false
    case Empty => false
    case Concat(_, _) => true
    case Union(r1, r2) => !IsAllSymUnion(r)
    case Star(_) => true
    case Opt(_) => true
    case Plus(_) => true
    case RepRange(r', lo, hi) =>
      // Must track PrettyPrint's own special-cased RepRange forms below exactly: a
      // RepRange that prints as "(?!)"/""/r' itself is exactly as atomic as
      // Empty/Eps/r' would be, and only the general "...{lo,hi}"/"...?" forms need
      // wrapping like Star/Plus/Opt do.
      if lo > hi then false
      else if hi == 0 then false
      else if lo == 1 && hi == 1 then NeedsGroup(r')
      else true
  }

  // Wrap an already-printed sub-expression in (?:...) iff its AST shape needs it. Takes
  // the printed string as a plain parameter (rather than recursing into PrettyPrint
  // itself) so it composes with PrettyPrint's own recursion without becoming mutual
  // recursion on the same argument.
  function WrapIfNeeded(r: Regex, s: string): string {
    if NeedsGroup(r) then "(?:" + s + ")" else s
  }

  // Only a Union needs grouping as a Concat operand: concatenation binds tighter than
  // alternation, so an un-grouped Union inside a Concat would leak its alternation scope
  // (e.g. printing Concat(Union(a,b), c) as "a|bc" would be wrong - it must be
  // "(?:a|b)c"). Every other constructor composes safely without extra parens as a
  // Concat operand, since Concat/Star/Plus/Opt/Sym/Eps/Empty all read as a single
  // "unit" already from the left or right.
  function ConcatWrap(r: Regex, s: string): string {
    match r
    case Union(_, _) => if IsAllSymUnion(r) then s else "(?:" + s + ")"
    case _ => s
  }

  // Semantics-preserving cleanup of the redundant Empty/Eps identity elements that
  // InferGroups' fold (starting from an Empty accumulator) and ConcatAll's Eps base
  // case leave behind - e.g. Union(r, Empty) prints as just r instead of "r|(?!)". Pure
  // presentation: like PrettyPrint, this carries no Dafny-level proof of its own: its
  // correctness is that Union(r,Empty)/Concat(r,Eps)/etc. denote the same language as
  // r, which is exactly the kind of fact sore.py's runtime `re.fullmatch` check on the
  // final text is there to catch if this reasoning were ever wrong.
  function Simplify(r: Regex): Regex
    decreases r
  {
    match r
    case Concat(r1, r2) =>
      var s1 := Simplify(r1);
      var s2 := Simplify(r2);
      if s1 == Empty || s2 == Empty then Empty
      else if s1 == Eps then s2
      else if s2 == Eps then s1
      else Concat(s1, s2)
    case Union(r1, r2) =>
      var s1 := Simplify(r1);
      var s2 := Simplify(r2);
      if s1 == Empty then s2
      else if s2 == Empty then s1
      else Union(s1, s2)
    case Star(r') => Star(Simplify(r'))
    case Opt(r') =>
      var s := Simplify(r');
      if s == Eps then Eps else Opt(s)
    case Plus(r') => Plus(Simplify(r'))
    case RepRange(r', lo, hi) =>
      var s := Simplify(r');
      if lo > hi then Empty       // empty range: matches nothing, same as Empty
      else if hi == 0 then Eps    // (lo <= hi and hi == 0, so lo == 0 too): only "" matches
      else if lo == 1 && hi == 1 then s  // exactly one repetition: same as r' itself
      else RepRange(s, lo, hi)
    case _ => r
  }

  // Render a nat in ordinary decimal, for RepRange's `{lo,hi}` bounds.
  function NatToString(n: nat): string
    decreases n
  {
    if n < 10 then [('0' as int + n) as char]
    else NatToString(n / 10) + [('0' as int + n % 10) as char]
  }

  function PrettyPrint(r: Regex): string
    decreases r
  {
    match r
    case Empty => "(?!)"
    case Eps => ""
    case Sym(c) => EscapeChar(c)
    case Concat(r1, r2) => ConcatWrap(r1, PrettyPrint(r1)) + ConcatWrap(r2, PrettyPrint(r2))
    case Union(r1, r2) =>
      if IsAllSymUnion(r) then "[" + PrintCharClass(CollectSyms(r)) + "]"
      else PrettyPrint(r1) + "|" + PrettyPrint(r2)
    case Star(r') => WrapIfNeeded(r', PrettyPrint(r')) + "*"
    case Opt(r') => WrapIfNeeded(r', PrettyPrint(r')) + "?"
    case Plus(r') => WrapIfNeeded(r', PrettyPrint(r')) + "+"
    case RepRange(r', lo, hi) =>
      // Standard regex bounded-repetition syntax r{lo,hi}, with the more idiomatic
      // shorter forms substituted where they apply: an empty [lo,hi] range matches
      // nothing (same as Empty); {0,0} matches only "" (same as Eps); {1,1} is just r'
      // itself; {0,1} is exactly Opt, so it prints as r? to match Opt's own printing;
      // and {n,n} for n > 1 prints as the shorter r{n} instead of r{n,n}.
      if lo > hi then "(?!)"
      else if hi == 0 then ""
      else if lo == 1 && hi == 1 then PrettyPrint(r')
      else if lo == 0 && hi == 1 then WrapIfNeeded(r', PrettyPrint(r')) + "?"
      else if lo == hi then WrapIfNeeded(r', PrettyPrint(r')) + "{" + NatToString(lo) + "}"
      else WrapIfNeeded(r', PrettyPrint(r')) + "{" + NatToString(lo) + "," + NatToString(hi) + "}"
  }
}
