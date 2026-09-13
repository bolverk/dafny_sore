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
    | RepRange(r: Regex, lo: nat, hi: nat)

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
    case RepRange(r', lo, hi) => 1 + Rank(r')
  }

  // Standard language semantics, executable (bounded existentials over 0<=i<=|s|).
  // The trailing 0 is a dummy tiebreaker with no semantic effect (every call from
  // Matches to Matches keeps it at 0, so it never affects any of the pre-existing
  // cases here): it exists solely so this decreases clause has the same shape as
  // MatchesKCopies's below, since the RepRange case below makes Matches and
  // MatchesKCopies mutually recursive and Dafny needs compatible measures to see the
  // whole cluster terminates (see the comment above MatchesKCopies).
  function Matches(r: Regex, s: string): bool
    decreases Rank(r), |s|, 0
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
    case RepRange(r', lo, hi) =>
      exists k: nat :: lo <= k <= hi && MatchesKCopies(r', s, k)
  }

  // Matches and MatchesKCopies are mutually recursive (Matches's RepRange case calls
  // MatchesKCopies, which itself calls back into Matches on the same r), so both need a
  // combined, compatible decreases measure. Rank(r) alone already decreases on the call
  // from Matches into MatchesKCopies (RepRange(r,lo,hi) has strictly bigger rank than r),
  // and the trailing k tiebreaks MatchesKCopies's calls back into Matches/itself (which
  // keep the same r, so Rank(r) ties there, but k strictly decreases).
  predicate MatchesKCopies(r: Regex, s: string, k: nat)
    decreases Rank(r), |s|, k
  {
    if k == 0 then s == ""
    else exists i :: 0 <= i <= |s| && Matches(r, s[..i]) && MatchesKCopies(r, s[i..], k - 1)
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
    case RepRange(r', lo, hi) => Symbols(r')
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

  lemma RepRangeIsSore(r: Regex, lo: nat, hi: nat)
    requires IsSore(r)
    ensures IsSore(RepRange(r, lo, hi))
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

  // ---- Bounded repetition (RepRange) ----
  //
  // RepRange(r, lo, hi) matches between lo and hi (inclusive) repetitions of r. It is
  // added as groundwork for a later effort: both downstream implementations (the tiered
  // heuristic in Chain.dfy/Infer.dfy, and the bigram-graph approach in Graph.dfy)
  // currently emit UNBOUNDED Star/Plus wherever they detect a cycle or periodic
  // structure, even though both only ever need to accept a known, FINITE set of input
  // strings - so the true number of repetitions ever needed is always computable and
  // bounded from that input set. A later round will replace those unbounded Star/Plus
  // uses with a tight, input-set-specific RepRange bound while preserving soundness.
  // (If lo > hi, the range [lo,hi] is empty, so no valid repetition count k exists in
  // Matches's existential below and RepRange matches nothing - this falls out of the
  // semantics for free, with no separate `requires lo <= hi` needed anywhere.)
  //
  // Like Opt and Plus (see the module-level comment at the top of this file), RepRange
  // is a primitive constructor rather than a macro desugared into k copies of r combined
  // with Concat/Union: desugaring would multiply r's symbols across those copies,
  // breaking the single-occurrence invariant IsSore relies on. Keeping RepRange
  // primitive lets Symbols(RepRange(r, lo, hi)) count r's symbols exactly once, exactly
  // like Symbols(Star(r))/Symbols(Opt(r))/Symbols(Plus(r)) already do.

  // Smoke test: zero repetitions of anything matches only the empty string.
  lemma RepRangeZeroZero(r: Regex, s: string)
    ensures Matches(RepRange(r, 0, 0), s) <==> s == ""
  {
    if s == "" {
      assert MatchesKCopies(r, s, 0);
      assert 0 <= 0 <= 0 && MatchesKCopies(r, s, 0);
    }
    if Matches(RepRange(r, 0, 0), s) {
      var k: nat :| 0 <= k <= 0 && MatchesKCopies(r, s, k);
      assert k == 0;
      assert MatchesKCopies(r, s, 0);
    }
  }

  // Smoke test: exactly one repetition of r is the same as r itself.
  lemma RepRangeOneOne(r: Regex, s: string)
    ensures Matches(RepRange(r, 1, 1), s) <==> Matches(r, s)
  {
    if Matches(r, s) {
      assert s[..|s|] == s && s[|s|..] == "";
      assert MatchesKCopies(r, s, 0 + 1) by {
        assert 0 <= |s| <= |s| && Matches(r, s[..|s|]) && MatchesKCopies(r, s[|s|..], 0);
      }
      assert 1 <= 1 <= 1 && MatchesKCopies(r, s, 1);
    }
    if Matches(RepRange(r, 1, 1), s) {
      var k: nat :| 1 <= k <= 1 && MatchesKCopies(r, s, k);
      assert k == 1;
      var i :| 0 <= i <= |s| && Matches(r, s[..i]) && MatchesKCopies(r, s[i..], 0);
      assert s[i..] == "";
      assert i == |s|;
      assert s[..i] == s;
    }
  }

  // ---- "k copies" reasoning, for building RepRange witnesses ----
  //
  // MatchesKCopies(r, s, k) (declared above, next to Matches, since Matches's own
  // RepRange case already depends on it) says s splits into exactly k consecutive
  // pieces each matching r - the same shape of reasoning already used informally
  // wherever Star/Plus matches are unfolded one repetition at a time in
  // Chain.dfy/Graph.dfy. The lemmas below connect it to the more explicit
  // "count + split points" view (the natural characterization of RepRange, in the same
  // style as Concat's own existential and Graph.dfy's WalkMatches) so later rounds can
  // produce a RepRange witness directly from a computed count k without caring which
  // concrete form Matches's definition happens to use internally.

  // Shift every element of a split-point sequence by a fixed offset. Used to splice a
  // "rest of the splits" witness (relative to a suffix of s) back into full-string
  // coordinates.
  function ShiftSeq(xs: seq<nat>, offset: nat): seq<nat>
    decreases xs
    ensures |ShiftSeq(xs, offset)| == |xs|
    ensures forall j :: 0 <= j < |xs| ==> ShiftSeq(xs, offset)[j] == xs[j] + offset
  {
    if |xs| == 0 then []
    else [xs[0] + offset] + ShiftSeq(xs[1..], offset)
  }

  // A slice of a suffix is a shifted slice of the original string. General fact about
  // seq slicing, needed below to relate coordinates in a suffix s[off..] back to
  // coordinates in s itself.
  lemma SliceOfSuffix(s: string, off: nat, a: nat, b: nat)
    requires off <= |s|
    requires a <= b <= |s| - off
    ensures s[off..][a..b] == s[off+a..off+b]
  {
    assert |s[off..][a..b]| == |s[off+a..off+b]|;
    forall idx | 0 <= idx < b - a
      ensures s[off..][a..b][idx] == s[off+a..off+b][idx]
    {
      assert s[off..][a..b][idx] == s[off..][a+idx];
      assert s[off..][a+idx] == s[off+a+idx];
    }
  }

  // One repetition step's property in the explicit split-point view, factored out into
  // its own named predicate purely so the foralls in MatchesKCopiesSplits below have an
  // unambiguous trigger to instantiate on (a raw `splits[i] <= splits[i+1] <= |s| &&
  // Matches(...)` body gives Dafny nothing unambiguous to trigger on and leaves the
  // quantifier effectively unusable for automatic instantiation).
  predicate KCopyStep(r: Regex, s: string, splits: seq<nat>, i: nat)
    requires i + 1 < |splits|
  {
    splits[i] <= splits[i+1] <= |s| && Matches(r, s[splits[i]..splits[i+1]])
  }

  // Constructs the explicit split-point witness that characterizes RepRange's semantics
  // (count + split points, in the same style as Concat's own existential and Graph.dfy's
  // WalkMatches), from a MatchesKCopies fact, by induction on k: peel one repetition off
  // the front and shift the recursively-built rest of the splits into full-string
  // coordinates. (Matches's own RepRange case is instead phrased directly in terms of
  // MatchesKCopies - see the comment above MatchesKCopiesImpliesRepRange for why - but
  // this lemma shows the two views agree, and is the reusable piece of "proof
  // engineering" a later round can call to go from a computed count k straight to an
  // explicit split-point witness if it wants one.)
  lemma MatchesKCopiesSplits(r: Regex, s: string, k: nat) returns (splits: seq<nat>)
    requires MatchesKCopies(r, s, k)
    ensures |splits| == k + 1
    ensures splits[0] == 0 && splits[k] == |s|
    ensures forall i :: 0 <= i < k ==> KCopyStep(r, s, splits, i)
    decreases k
  {
    if k == 0 {
      splits := [0];
    } else {
      var i :| 0 <= i <= |s| && Matches(r, s[..i]) && MatchesKCopies(r, s[i..], k - 1);
      var rest := MatchesKCopiesSplits(r, s[i..], k - 1);
      splits := [0] + ShiftSeq(rest, i);

      assert |splits| == k + 1;
      assert splits[0] == 0;
      assert splits[1] == rest[0] + i == i;
      assert splits[k] == rest[k-1] + i == |s[i..]| + i == |s|;

      forall j | 0 <= j < k
        ensures KCopyStep(r, s, splits, j)
      {
        if j == 0 {
          assert splits[0] == 0 && splits[1] == i;
          assert s[splits[0]..splits[1]] == s[..i];
        } else {
          assert splits[j] == rest[j-1] + i;
          assert splits[j+1] == rest[j] + i;
          assert KCopyStep(r, s[i..], rest, j-1);
          SliceOfSuffix(s, i, rest[j-1], rest[j]);
          assert s[splits[j]..splits[j+1]] == s[i..][rest[j-1]..rest[j]];
        }
      }
    }
  }

  // The lemma downstream implementations will actually use: once a caller has computed
  // a repetition count k (with lo <= k <= hi) and shown s decomposes into k copies of r,
  // that's enough to conclude the RepRange(r, lo, hi) regex matches s. This holds
  // immediately from Matches's own RepRange case, which is defined directly as
  // `exists k :: lo <= k <= hi && MatchesKCopies(r, s, k)` (rather than the literal
  // "count + split points" existential, which Dafny cannot compile - see
  // MatchesKCopiesSplits above for the equivalent explicit-splits view, proved as a
  // separate lemma instead of baked into Matches's definition).
  lemma MatchesKCopiesImpliesRepRange(r: Regex, lo: nat, hi: nat, k: nat, s: string)
    requires lo <= k <= hi
    requires MatchesKCopies(r, s, k)
    ensures Matches(RepRange(r, lo, hi), s)
  {
  }
}
