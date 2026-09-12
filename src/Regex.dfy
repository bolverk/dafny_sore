// Core regular-expression datatype, semantics, and the "single occurrence" predicate.
//
// Opt and Plus are primitive constructors (not macros desugared into Union/Concat+Star).
// This matters for single-occurrence counting: if Plus(r) were defined as
// Concat(r, Star(r)), every symbol of r would be counted twice in the underlying tree
// (once directly, once inside the Star), so "c+" would wrongly look like two
// occurrences of c. Keeping Plus/Opt as their own constructors lets Symbols(Plus(r))
// and Symbols(Opt(r)) count r's symbols exactly once, matching the standard SORE
// definition where ?, *, + are unary postfix operators on an already single-occurrence
// sub-expression.
module RegexCore {

  datatype Regex =
    | Empty
    | Eps
    | Sym(c: char)
    | Concat(r1: Regex, r2: Regex)
    | Union(r1: Regex, r2: Regex)
    | Star(r: Regex)
    | Opt(r: Regex)
    | Plus(r: Regex)

  // Structural rank used only to justify termination of Matches below. Star, Opt and
  // Plus all wrap a single sub-expression and get the same rank as each other so that
  // Plus's recursive call into Star(r') (a freshly built term, not a literal subterm of
  // Plus(r')) is recognized as "no bigger", while the |s| decrease (i>0) does the rest.
  function Rank(r: Regex): nat
    decreases r
  {
    match r
    case Empty => 0
    case Eps => 0
    case Sym(_) => 0
    case Concat(r1, r2) => 1 + Rank(r1) + Rank(r2)
    case Union(r1, r2) => 1 + Rank(r1) + Rank(r2)
    case Star(r') => 1 + Rank(r')
    case Opt(r') => 1 + Rank(r')
    case Plus(r') => 1 + Rank(r')
  }

  // Standard language semantics, executable (bounded existentials over 0<=i<=|s|).
  function Matches(r: Regex, s: string): bool
    decreases Rank(r), |s|
  {
    match r
    case Empty => false
    case Eps => s == ""
    case Sym(c) => s == [c]
    case Concat(r1, r2) =>
      exists i :: 0 <= i <= |s| && Matches(r1, s[..i]) && Matches(r2, s[i..])
    case Union(r1, r2) =>
      Matches(r1, s) || Matches(r2, s)
    case Star(r') =>
      s == "" ||
      exists i :: 0 < i <= |s| && Matches(r', s[..i]) && Matches(Star(r'), s[i..])
    case Opt(r') =>
      s == "" || Matches(r', s)
    case Plus(r') =>
      exists i :: 0 < i <= |s| && Matches(r', s[..i]) && Matches(Star(r'), s[i..])
  }

  lemma OptSound(r: Regex, s: string)
    requires Matches(r, s)
    ensures Matches(Opt(r), s)
  {
  }

  lemma OptSoundEps(r: Regex)
    ensures Matches(Opt(r), "")
  {
  }

  // A single non-empty repetition already witnesses Plus. (Requiring s != "" matters:
  // Plus's existential needs 0 < i <= |s|, so Plus(r) can never match "" at all, even
  // when r itself is nullable - e.g. Plus(Eps) matches nothing under this definition.
  // That edge case is harmless here since Plus is only ever applied to Sym(c), which
  // never matches "".)
  lemma PlusSoundOne(r: Regex, s: string)
    requires Matches(r, s)
    requires s != ""
    ensures Matches(Plus(r), s)
  {
    assert s[..|s|] == s;
    assert s[|s|..] == "";
  }

  // ---- Single-occurrence predicate ----

  // Multiset of symbols appearing as Sym leaves anywhere in r.
  function Symbols(r: Regex): multiset<char>
    decreases r
  {
    match r
    case Empty => multiset{}
    case Eps => multiset{}
    case Sym(c) => multiset{c}
    case Concat(r1, r2) => Symbols(r1) + Symbols(r2)
    case Union(r1, r2) => Symbols(r1) + Symbols(r2)
    case Star(r') => Symbols(r')
    case Opt(r') => Symbols(r')
    case Plus(r') => Symbols(r')
  }

  // Every alphabet symbol occurs at most once in the whole expression.
  function IsSore(r: Regex): bool {
    forall c :: Symbols(r)[c] <= 1
  }

  lemma SymbolsDisjointIsSore(r1: Regex, r2: Regex)
    requires IsSore(r1) && IsSore(r2)
    requires forall c :: c !in Symbols(r1) || c !in Symbols(r2)
    ensures IsSore(Concat(r1, r2))
    ensures IsSore(Union(r1, r2))
  {
    forall c ensures (Symbols(r1) + Symbols(r2))[c] <= 1 {
      if c in Symbols(r1) {
        assert Symbols(r2)[c] == 0;
      } else if c in Symbols(r2) {
        assert Symbols(r1)[c] == 0;
      }
    }
  }

  lemma StarIsSore(r: Regex)
    requires IsSore(r)
    ensures IsSore(Star(r))
  {
  }

  lemma OptIsSore(r: Regex)
    requires IsSore(r)
    ensures IsSore(Opt(r))
  {
  }

  lemma PlusIsSore(r: Regex)
    requires IsSore(r)
    ensures IsSore(Plus(r))
  {
  }

  lemma SingleSymIsSore(c: char)
    ensures IsSore(Sym(c))
  {
  }

  lemma EpsIsSore()
    ensures IsSore(Eps)
  {
  }

  lemma EmptyIsSore()
    ensures IsSore(Empty)
  {
  }
}
