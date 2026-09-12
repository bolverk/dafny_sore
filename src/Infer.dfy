// Top-level SORE inference: given a finite set of sample strings, build a
// single-occurrence regex that is *sound* (accepts every sample). This is a
// certifying-algorithm design: a cheap heuristic (MergeString) proposes a candidate
// symbol order, an independent, easy-to-verify checker (CheckOrderAll/NoDup) confirms
// whether that candidate actually works for every sample, and only if it does do we
// build the chain regex from it (proved sound and single-occurrence via Chain.dfy). If
// the checker rejects the candidate for any reason, we fall back to the trivial but
// always sound and always single-occurrence Star-of-union-of-symbols regex over the
// sample alphabet.
//
// Infer is a `method`, not a `function`: converting the input `set<string>` into some
// concrete enumeration order requires an assign-such-that (`x :| x in rem`) pick, and
// Dafny only allows compiling that inside methods (a compiled `function` would need a
// *uniquely determined* witness, which an arbitrary set element obviously isn't).
// Infer's `ensures` clauses below are exactly the soundness and single-occurrence
// theorems; Dafny verifies them as ordinary method postconditions.
include "Regex.dfy"
include "Chain.dfy"

module SoreInfer {
  import opened RegexCore
  import opened Chain

  // ---- Deterministic set-to-seq conversion via canonical sorted extraction. ----
  //
  // The old version of this helper used a bare `var x :| x in rem` (assign-such-that)
  // to pick "some" element of the remaining set on each iteration. Dafny deliberately
  // leaves that pick unspecified, and the Python backend materializes it via Python's
  // own set/frozenset iteration order, which is hash-randomized per process by default
  // - so the exact same input set could enumerate in a different order on every fresh
  // `python3` invocation, which then fed into every tier's heuristics (affecting which
  // candidate chain/split/period got tried) and into how alphabets got laid out into
  // character classes. Repeatedly extracting the MINIMUM remaining element (by a fixed
  // total order) instead of "any" element makes the result canonical: two equal sets
  // always sort to the same sequence, regardless of how the underlying runtime
  // representation happens to iterate. This is the only place in the whole development
  // that needs an assign-such-that pick at all (inside FindMinChar/FindMinString's own
  // scan, see below) - hence the only reason anything here has to be a method instead
  // of a function.
  //
  // char's native `<` is already a total order (backed by Unicode code points), so no
  // separate comparator is needed for it - only strings need one defined below.

  predicate StringLess(a: string, b: string)
    decreases |a|
  {
    if a == "" then b != ""
    else if b == "" then false
    else if a[0] != b[0] then a[0] < b[0]
    else StringLess(a[1..], b[1..])
  }

  lemma StringLessTrichotomy(a: string, b: string)
    ensures a == b || StringLess(a, b) || StringLess(b, a)
    decreases |a|
  {
    if a == "" || b == "" {
    } else if a[0] != b[0] {
    } else {
      StringLessTrichotomy(a[1..], b[1..]);
    }
  }

  lemma StringLessIrreflexive(a: string)
    ensures !StringLess(a, a)
    decreases |a|
  {
    if a == "" {
    } else {
      StringLessIrreflexive(a[1..]);
    }
  }

  lemma StringLessTransitive(a: string, b: string, c: string)
    requires StringLess(a, b) && StringLess(b, c)
    ensures StringLess(a, c)
    decreases |a|
  {
    if a == "" {
      // StringLess(b, c) with b != "" (from StringLess(a,b) needing b != "" when a == "")
      // forces c != "", which is exactly StringLess(a, c) when a == "".
    } else if b == "" || c == "" {
      // StringLess(x, "") is always false, contradicting a hypothesis.
      assert !StringLess(b, c) || b != "";
    } else if a[0] != b[0] {
      // a,b,c all nonempty here. StringLess(a,b) gives a[0] < b[0]. StringLess(b,c)
      // gives either b[0] < c[0] or (b[0] == c[0] and the tails compare), either way
      // b[0] <= c[0], so a[0] < b[0] <= c[0] forces a[0] < c[0].
      if b[0] != c[0] {
        assert b[0] < c[0];
      } else {
        assert b[0] == c[0];
      }
    } else {
      // a[0] == b[0]; StringLess(b,c) must go through b[0] == c[0] too (else a[0] !=
      // b[0] < c[0] would be required, contradicting a[0] == b[0]... actually b[0]
      // could still differ from c[0] here, handled below).
      if b[0] != c[0] {
        assert a[0] < c[0];
      } else {
        StringLessTransitive(a[1..], b[1..], c[1..]);
      }
    }
  }

  // FindMinChar/FindMinString: recursive scan that provably returns the UNIQUE minimum
  // of a nonempty set. These are `method`s (not `function`s) specifically because
  // their bodies use `:|` to grab "some" starting candidate `x` at each recursive
  // step, and Dafny only allows compiling `:|` inside methods (a compiled function
  // needs a *uniquely determined* witness, which an arbitrary set element isn't). This
  // does NOT make the RESULT nondeterministic: the `ensures` clause pins the answer
  // down as the true minimum (the smallest element, by definition independent of scan
  // order), so regardless of which `x` the runtime set iteration happens to hand back
  // first, the recursive min-comparison converges to the same final value every time.
  // Only the *output* needs to be deterministic - not every internal computation path.
  method FindMinChar(S: set<char>) returns (m: char)
    requires S != {}
    ensures m in S
    ensures forall x :: x in S ==> m == x || m < x
    decreases |S|
  {
    var x :| x in S;
    var rest := S - {x};
    if rest == {} {
      assert S == {x};
      m := x;
    } else {
      var m' := FindMinChar(rest);
      assert S == rest + {x};
      if x < m' {
        m := x;
      } else {
        m := m';
        forall y | y in S ensures m == y || m < y {
          if y != x { assert y in rest; }
        }
      }
    }
  }

  method FindMinString(S: set<string>) returns (m: string)
    requires S != {}
    ensures m in S
    ensures forall x :: x in S ==> m == x || StringLess(m, x)
    decreases |S|
  {
    var x :| x in S;
    var rest := S - {x};
    if rest == {} {
      assert S == {x};
      m := x;
    } else {
      var m' := FindMinString(rest);
      assert S == rest + {x};
      StringLessTrichotomy(x, m');
      if x == m' {
        m := x;
        forall y | y in S ensures m == y || StringLess(m, y) {
          if y != x { assert y in rest; }
        }
      } else if StringLess(x, m') {
        m := x;
        forall y | y in S ensures m == y || StringLess(m, y) {
          if y != x {
            assert y in rest;
            if y != m' { StringLessTransitive(x, m', y); }
          }
        }
      } else {
        m := m';
        forall y | y in S ensures m == y || StringLess(m, y) {
          if y != x { assert y in rest; }
        }
      }
    }
  }

  method SortedCharSeq(S: set<char>) returns (r: seq<char>)
    ensures multiset(r) == multiset(S)
    ensures forall i, j :: 0 <= i < j < |r| ==> r[i] < r[j]
    ensures NoDup(r)
  {
    r := [];
    var rem := S;
    while rem != {}
      invariant multiset(r) + multiset(rem) == multiset(S)
      invariant forall i, j :: 0 <= i < j < |r| ==> r[i] < r[j]
      invariant forall x, y :: x in r && y in rem ==> x < y
      decreases rem
    {
      var m := FindMinChar(rem);
      var rOld := r;
      assert forall i :: 0 <= i < |rOld| ==> rOld[i] < m by {
        forall i | 0 <= i < |rOld| ensures rOld[i] < m {
          assert rOld[i] in rOld;
        }
      }
      r := rOld + [m];
      assert forall i, j :: 0 <= i < j < |r| ==> r[i] < r[j] by {
        forall i, j | 0 <= i < j < |r| ensures r[i] < r[j] {
          if j < |rOld| {
          } else {
            assert j == |rOld|;
            assert r[j] == m;
            assert r[i] == rOld[i];
          }
        }
      }
      rem := rem - {m};
    }
    forall i, j | 0 <= i < |r| && 0 <= j < |r| && i != j ensures r[i] != r[j] {
      if i < j { assert r[i] < r[j]; } else { assert r[j] < r[i]; }
    }
  }

  method SortedStringSeq(S: set<string>) returns (r: seq<string>)
    ensures multiset(r) == multiset(S)
    ensures forall i, j :: 0 <= i < j < |r| ==> StringLess(r[i], r[j])
    ensures forall i, j :: 0 <= i < |r| && 0 <= j < |r| && i != j ==> r[i] != r[j]
  {
    r := [];
    var rem := S;
    while rem != {}
      invariant multiset(r) + multiset(rem) == multiset(S)
      invariant forall i, j :: 0 <= i < j < |r| ==> StringLess(r[i], r[j])
      invariant forall x, y :: x in r && y in rem ==> StringLess(x, y)
      decreases rem
    {
      var m := FindMinString(rem);
      var rOld := r;
      assert forall i :: 0 <= i < |rOld| ==> StringLess(rOld[i], m) by {
        forall i | 0 <= i < |rOld| ensures StringLess(rOld[i], m) {
          assert rOld[i] in rOld;
        }
      }
      r := rOld + [m];
      assert forall i, j :: 0 <= i < j < |r| ==> StringLess(r[i], r[j]) by {
        forall i, j | 0 <= i < j < |r| ensures StringLess(r[i], r[j]) {
          if j < |rOld| {
          } else {
            assert j == |rOld|;
            assert r[j] == m;
            assert r[i] == rOld[i];
          }
        }
      }
      rem := rem - {m};
    }
    forall i, j | 0 <= i < |r| && 0 <= j < |r| && i != j ensures r[i] != r[j] {
      if i < j { assert StringLess(r[i], r[j]); } else { assert StringLess(r[j], r[i]); }
      if r[i] == r[j] { StringLessIrreflexive(r[i]); }
    }
  }

  lemma SeqSetMembership<T>(sq: seq<T>, st: set<T>, x: T)
    requires multiset(sq) == multiset(st)
    ensures x in sq <==> x in st
  {
    assert x in sq <==> x in multiset(sq);
    assert x in st <==> x in multiset(st);
  }

  // ---- Heuristic candidate-order construction ----

  // Tries to extend `order` so that the whole of `t` fits it (using RunLength/Fits'
  // greedy shape): repeatedly peel the maximal run of the front symbol, matching it
  // against the front of `order` if `order` already starts with that symbol, or
  // prepending a fresh symbol to `order` otherwise. Fails (returns ok=false) if a
  // symbol would need to be used twice non-consecutively, since that can never fit a
  // single-occurrence chain. This function is a pure heuristic: its only job is to
  // terminate and propose *some* order; its output is always re-checked below, so
  // MergeString itself carries no correctness burden.
  function MergeString(order: seq<char>, t: string): (seq<char>, bool)
    decreases |t|
  {
    if t == "" then (order, true)
    else
      var c := t[0];
      var m := RunLength(t, c);
      assert m <= |t| by { RunLengthBound(t, c); }
      var rest := t[m..];
      if c in rest then
        (order, false)
      else if |order| > 0 && order[0] == c then
        var (restOrder, ok) := MergeString(order[1..], rest);
        ([order[0]] + restOrder, ok)
      else if c !in order then
        var (newOrder, ok) := MergeString(order, rest);
        ([c] + newOrder, ok)
      else
        (order, false)
  }

  function MergeAll(strs: seq<string>, order: seq<char>): seq<char>
    decreases strs
  {
    if strs == [] then order
    else
      var (order', ok) := MergeString(order, strs[0]);
      if ok then MergeAll(strs[1..], order') else order'
  }

  // ---- Certifying checker: the only thing soundness actually depends on ----

  function CheckOrderAll(strs: seq<string>, order: seq<char>): bool
    decreases strs
  {
    strs == [] || (Fits(strs[0], order) && CheckOrderAll(strs[1..], order))
  }

  lemma CheckOrderAllSound(strs: seq<string>, order: seq<char>, t: string)
    requires CheckOrderAll(strs, order)
    requires t in strs
    ensures Fits(t, order)
    decreases strs
  {
    if strs[0] == t {
    } else {
      CheckOrderAllSound(strs[1..], order, t);
    }
  }

  // ---- Tier 2: periodic block *with a per-position choice* + certifying checker ----
  //
  // Reached only after tier 1 (the global chain) has already failed on some sample.
  // Proposes a single candidate period p (found by directly re-checking each candidate
  // length against every sample, see FindPeriodChoice below - there's no cheap
  // necessary-but-not-sufficient pre-filter here worth using, since e.g. "does p divide
  // every sample's length" is satisfied by p=1 for literally everything, which would
  // short-circuit before ever trying a real period) together with, for each of the p
  // positions within one repetition, the set of characters actually observed there
  // across every sample (PositionAlphabetSeq/BuildSigmas) - then independently checks
  // the whole thing against every sample via CheckPeriodChoiceAll. The heuristic itself
  // carries no correctness burden beyond terminating with *some* period and alphabets;
  // e.g. for {"abab","acac"}, p=2 with position-0 alphabet {a} and position-1 alphabet
  // {b,c} gives (?:a(?:b|c))+ instead of a full wildcard. Reduces to the old literal-only
  // behavior exactly when every position's alphabet happens to be a singleton.

  // The first non-empty string in strs, if any.
  function FirstNonEmpty(strs: seq<string>): string
    decreases strs
  {
    if strs == [] then ""
    else if strs[0] != "" then strs[0]
    else FirstNonEmpty(strs[1..])
  }

  lemma FirstNonEmptyFound(strs: seq<string>)
    ensures FirstNonEmpty(strs) != "" ==> FirstNonEmpty(strs) in strs
    decreases strs
  {
    if strs == [] {
    } else if strs[0] != "" {
    } else {
      FirstNonEmptyFound(strs[1..]);
    }
  }

  function CheckPeriodChoiceAll(strs: seq<string>, p: nat, Sigmas: seq<seq<char>>): bool
    decreases strs
  {
    strs == [] || ((strs[0] == "" || FitsPeriodChoice(strs[0], p, Sigmas)) && CheckPeriodChoiceAll(strs[1..], p, Sigmas))
  }

  lemma CheckPeriodChoiceAllSound(strs: seq<string>, p: nat, Sigmas: seq<seq<char>>, t: string)
    requires CheckPeriodChoiceAll(strs, p, Sigmas)
    requires t in strs
    ensures t == "" || FitsPeriodChoice(t, p, Sigmas)
    decreases strs
  {
    if strs[0] == t {
    } else {
      CheckPeriodChoiceAllSound(strs[1..], p, Sigmas, t);
    }
  }

  // The (deduplicated) set of characters observed at position i, across every sample
  // long enough to have one.
  function PositionAlphabetSeq(strs: seq<string>, i: nat): seq<char>
    decreases strs
  {
    if strs == [] then []
    else
      var rest := PositionAlphabetSeq(strs[1..], i);
      if i < |strs[0]| && strs[0][i] !in rest then [strs[0][i]] + rest
      else rest
  }

  lemma PositionAlphabetSeqSound(strs: seq<string>, i: nat, t: string)
    requires t in strs
    requires i < |t|
    ensures t[i] in PositionAlphabetSeq(strs, i)
    decreases strs
  {
    if strs[0] == t {
    } else {
      PositionAlphabetSeqSound(strs[1..], i, t);
    }
  }

  lemma PositionAlphabetSeqNoDup(strs: seq<string>, i: nat)
    ensures NoDup(PositionAlphabetSeq(strs, i))
    decreases strs
  {
    if strs == [] {
    } else {
      PositionAlphabetSeqNoDup(strs[1..], i);
    }
  }

  lemma PositionAlphabetSeqInAlphabetAll(strs: seq<string>, i: nat, c: char)
    requires c in PositionAlphabetSeq(strs, i)
    ensures c in AlphabetAll(strs)
    decreases strs
  {
    if strs == [] {
    } else {
      var rest := PositionAlphabetSeq(strs[1..], i);
      if i < |strs[0]| && strs[0][i] !in rest {
        if c == strs[0][i] {
          StringAlphabetSound(strs[0], i);
        } else {
          PositionAlphabetSeqInAlphabetAll(strs[1..], i, c);
        }
      } else {
        PositionAlphabetSeqInAlphabetAll(strs[1..], i, c);
      }
    }
  }

  function BuildSigmas(strs: seq<string>, p: nat, i: nat): seq<seq<char>>
    requires i <= p
    decreases p - i
  {
    if i >= p then []
    else [PositionAlphabetSeq(strs, i)] + BuildSigmas(strs, p, i + 1)
  }

  lemma BuildSigmasLength(strs: seq<string>, p: nat, i: nat)
    requires i <= p
    ensures |BuildSigmas(strs, p, i)| == p - i
    decreases p - i
  {
    if i >= p {
    } else {
      BuildSigmasLength(strs, p, i + 1);
    }
  }

  lemma BuildSigmasNoDup(strs: seq<string>, p: nat, i: nat)
    requires i <= p
    ensures forall j :: 0 <= j < |BuildSigmas(strs, p, i)| ==> NoDup(BuildSigmas(strs, p, i)[j])
    decreases p - i
  {
    if i >= p {
    } else {
      PositionAlphabetSeqNoDup(strs, i);
      BuildSigmasNoDup(strs, p, i + 1);
    }
  }

  lemma BuildSigmasAlphabetAll(strs: seq<string>, p: nat, i: nat, j: nat, c: char)
    requires i <= p
    requires 0 <= j < |BuildSigmas(strs, p, i)|
    requires c in BuildSigmas(strs, p, i)[j]
    ensures c in AlphabetAll(strs)
    decreases p - i
  {
    if j == 0 {
      PositionAlphabetSeqInAlphabetAll(strs, i, c);
    } else {
      BuildSigmasAlphabetAll(strs, p, i + 1, j - 1, c);
    }
  }

  // Try candidate period lengths 1, 2, ..., |t0| in increasing order; return the first
  // one for which the resulting per-position alphabets actually check out against every
  // sample. |t0| itself is always reached by this search (whether or not it ultimately
  // checks out - the caller re-verifies before trusting anything, same as every other
  // heuristic in this file).
  function FindPeriodChoice(strs: seq<string>, t0: string, p: nat): nat
    requires 1 <= p
    decreases |t0| - p
  {
    if p >= |t0| then p
    else if CheckPeriodChoiceAll(strs, p, BuildSigmas(strs, p, 0)) then p
    else FindPeriodChoice(strs, t0, p + 1)
  }

  function CandidatePeriod(strs: seq<string>): nat
  {
    var t0 := FirstNonEmpty(strs);
    if t0 == "" then 0 else FindPeriodChoice(strs, t0, 1)
  }

  // ---- Alphabet ----

  function StringAlphabet(t: string): set<char>
    decreases |t|
  {
    if t == "" then {} else {t[0]} + StringAlphabet(t[1..])
  }

  lemma StringAlphabetSound(t: string, i: nat)
    requires i < |t|
    ensures t[i] in StringAlphabet(t)
    decreases |t|
  {
    if i == 0 {
    } else {
      StringAlphabetSound(t[1..], i - 1);
    }
  }

  // If every character of t (by position) is in S, so is t's whole alphabet.
  lemma StringAlphabetSubsetIfAllIn(t: string, S: set<char>)
    requires forall i :: 0 <= i < |t| ==> t[i] in S
    ensures StringAlphabet(t) <= S
    decreases |t|
  {
    if t == "" {
    } else {
      forall i | 0 <= i < |t[1..]| ensures t[1..][i] in S {
        assert t[1..][i] == t[i + 1];
      }
      StringAlphabetSubsetIfAllIn(t[1..], S);
    }
  }

  function AlphabetAll(strs: seq<string>): set<char>
    decreases strs
  {
    if strs == [] then {} else StringAlphabet(strs[0]) + AlphabetAll(strs[1..])
  }

  lemma AlphabetAllSound(strs: seq<string>, t: string, i: nat)
    requires t in strs
    requires i < |t|
    ensures t[i] in AlphabetAll(strs)
    decreases strs
  {
    if strs[0] == t {
      StringAlphabetSound(t, i);
    } else {
      AlphabetAllSound(strs[1..], t, i);
    }
  }

  lemma StringAlphabetInAlphabetAll(strs: seq<string>, t: string)
    requires t in strs
    ensures StringAlphabet(t) <= AlphabetAll(strs)
    decreases strs
  {
    if strs[0] == t {
    } else {
      StringAlphabetInAlphabetAll(strs[1..], t);
    }
  }

  // ---- Alphabet-subset facts. These let us prove that whatever Infer/InferGroup
  // produces from a batch of strings only ever uses characters drawn from that batch's
  // own alphabet - never characters "borrowed" from elsewhere. That containment is what
  // licenses combining separate groups' regexes with Union later: two groups built from
  // disjoint alphabets produce regexes with disjoint symbol sets, so SymbolsDisjointIsSore
  // applies. ----

  lemma StringAlphabetSuffix(t: string, m: nat)
    requires m <= |t|
    ensures StringAlphabet(t[m..]) <= StringAlphabet(t)
    decreases m
  {
    if m == 0 {
      assert t[0..] == t;
    } else {
      assert t != "";
      assert t[m..] == t[1..][m - 1..];
      StringAlphabetSuffix(t[1..], m - 1);
      assert StringAlphabet(t) == {t[0]} + StringAlphabet(t[1..]);
    }
  }

  lemma StringAlphabetPrefix(t: string, p: nat)
    requires p <= |t|
    ensures StringAlphabet(t[..p]) <= StringAlphabet(t)
    decreases p
  {
    if p == 0 {
      assert t[..0] == "";
    } else {
      assert t != "";
      assert t[..p][0] == t[0];
      assert t[..p][1..] == t[1..][..p - 1];
      StringAlphabetPrefix(t[1..], p - 1);
      assert StringAlphabet(t[..p]) == {t[..p][0]} + StringAlphabet(t[..p][1..]);
      assert StringAlphabet(t) == {t[0]} + StringAlphabet(t[1..]);
    }
  }

  // MergeString never introduces a character absent from both the incoming order and t
  // itself - it only ever rearranges/copies characters it already saw.
  lemma MergeStringChars(order: seq<char>, t: string)
    ensures StringAlphabet(MergeString(order, t).0) <= StringAlphabet(order) + StringAlphabet(t)
    decreases |t|
  {
    if t == "" {
    } else {
      var c := t[0];
      var m := RunLength(t, c);
      assert m <= |t| by { RunLengthBound(t, c); }
      var rest := t[m..];
      StringAlphabetSuffix(t, m);
      StringAlphabetSound(t, 0);
      assert c in StringAlphabet(t);
      assert StringAlphabet(rest) <= StringAlphabet(t);
      if c in rest {
      } else if |order| > 0 && order[0] == c {
        MergeStringChars(order[1..], rest);
        assert StringAlphabet(order) == {order[0]} + StringAlphabet(order[1..]);
      } else if c !in order {
        MergeStringChars(order, rest);
      } else {
      }
    }
  }

  lemma MergeAllChars(strs: seq<string>, order: seq<char>)
    ensures StringAlphabet(MergeAll(strs, order)) <= StringAlphabet(order) + AlphabetAll(strs)
    decreases strs
  {
    if strs == [] {
    } else {
      var (order', ok) := MergeString(order, strs[0]);
      MergeStringChars(order, strs[0]);
      assert StringAlphabet(order') <= StringAlphabet(order) + StringAlphabet(strs[0]);
      if ok {
        MergeAllChars(strs[1..], order');
        assert StringAlphabet(MergeAll(strs[1..], order')) <= StringAlphabet(order') + AlphabetAll(strs[1..]);
      }
      assert AlphabetAll(strs) == StringAlphabet(strs[0]) + AlphabetAll(strs[1..]);
    }
  }

  // ---- Tier 0: common-prefix/common-suffix literal alternation, e.g.
  // "SABE"/"SXYE" -> S(?:AB|XY)E. Tried before tier 1 (the per-character chain, with its
  // own choice-slot refinement): decomposes every sample as (common prefix P) (a middle
  // block, one of finitely many mutually-exclusive whole-block alternatives) (common
  // suffix Q). Like every other heuristic in this file, LCP/LCS carry no correctness
  // burden of their own beyond terminating with *some* candidate; actual soundness rests
  // entirely on independently re-checking the proposed (P, Q) against every sample (see
  // CheckPrefixSuffixAll below), the same certifying-algorithm pattern used throughout. ----

  function LCP2(a: string, b: string): string
    decreases |a|
  {
    if a == "" || b == "" || a[0] != b[0] then ""
    else [a[0]] + LCP2(a[1..], b[1..])
  }

  lemma LCP2IsPrefix(a: string, b: string)
    ensures var m := |LCP2(a, b)|; m <= |a| && m <= |b| && a[..m] == LCP2(a, b) && b[..m] == LCP2(a, b)
    decreases |a|
  {
    if a == "" || b == "" || a[0] != b[0] {
      assert a[..0] == "";
      assert b[..0] == "";
    } else {
      LCP2IsPrefix(a[1..], b[1..]);
      var m' := |LCP2(a[1..], b[1..])|;
      assert a[..m' + 1] == [a[0]] + a[1..][..m'];
      assert b[..m' + 1] == [b[0]] + b[1..][..m'];
    }
  }

  function LCP(strs: seq<string>): string
    decreases strs
  {
    if strs == [] then ""
    else if |strs| == 1 then strs[0]
    else LCP2(strs[0], LCP(strs[1..]))
  }

  lemma LCPIsPrefix(strs: seq<string>, t: string)
    requires t in strs
    ensures |LCP(strs)| <= |t| && t[..|LCP(strs)|] == LCP(strs)
    decreases strs
  {
    if |strs| == 1 {
      assert t == strs[0];
    } else if strs[0] == t {
      LCP2IsPrefix(strs[0], LCP(strs[1..]));
    } else {
      LCPIsPrefix(strs[1..], t);
      LCP2IsPrefix(strs[0], LCP(strs[1..]));
      var len2 := |LCP2(strs[0], LCP(strs[1..]))|;
      var lenRest := |LCP(strs[1..])|;
      assert len2 <= lenRest;
      assert t[..lenRest] == LCP(strs[1..]);
      assert t[..lenRest][..len2] == t[..len2];
      assert LCP(strs[1..])[..len2] == LCP2(strs[0], LCP(strs[1..]));
    }
  }

  function LCS2(a: string, b: string): string
    decreases |a|
  {
    if a == "" || b == "" || a[|a| - 1] != b[|b| - 1] then ""
    else LCS2(a[..|a| - 1], b[..|b| - 1]) + [a[|a| - 1]]
  }

  lemma LCS2IsSuffix(a: string, b: string)
    ensures var m := |LCS2(a, b)|;
            m <= |a| && m <= |b| && a[|a| - m..] == LCS2(a, b) && b[|b| - m..] == LCS2(a, b)
    decreases |a|
  {
    if a == "" || b == "" || a[|a| - 1] != b[|b| - 1] {
      assert a[|a|..] == "";
      assert b[|b|..] == "";
    } else {
      LCS2IsSuffix(a[..|a| - 1], b[..|b| - 1]);
      var m' := |LCS2(a[..|a| - 1], b[..|b| - 1])|;
      assert a[..|a| - 1][|a| - 1 - m'..] == LCS2(a[..|a| - 1], b[..|b| - 1]);
      assert a[|a| - (m' + 1)..] == a[..|a| - 1][|a| - 1 - m'..] + [a[|a| - 1]];
      assert b[|b| - (m' + 1)..] == b[..|b| - 1][|b| - 1 - m'..] + [b[|b| - 1]];
    }
  }

  function LCS(strs: seq<string>): string
    decreases strs
  {
    if strs == [] then ""
    else if |strs| == 1 then strs[0]
    else LCS2(strs[0], LCS(strs[1..]))
  }

  lemma LCSIsSuffix(strs: seq<string>, t: string)
    requires t in strs
    ensures |LCS(strs)| <= |t| && t[|t| - |LCS(strs)|..] == LCS(strs)
    decreases strs
  {
    if |strs| == 1 {
      assert t == strs[0];
    } else if strs[0] == t {
      LCS2IsSuffix(strs[0], LCS(strs[1..]));
    } else {
      LCSIsSuffix(strs[1..], t);
      LCS2IsSuffix(strs[0], LCS(strs[1..]));
      var len2 := |LCS2(strs[0], LCS(strs[1..]))|;
      var lenRest := |LCS(strs[1..])|;
      assert len2 <= lenRest;
      assert t[|t| - lenRest..] == LCS(strs[1..]);
      assert t[|t| - lenRest..][lenRest - len2..] == t[|t| - len2..];
      assert LCS(strs[1..])[lenRest - len2..] == LCS2(strs[0], LCS(strs[1..]));
    }
  }

  // Total (no requires): only ever trusted for t/p/q where the caller has separately
  // established |p|+|q| <= |t|, t[..|p|] == p, t[|t|-|q|..] == q (see
  // CheckPrefixSuffixAll) - otherwise this is just some string, never used.
  function Middle(t: string, p: string, q: string): string {
    if |p| + |q| > |t| then "" else t[|p|..|t| - |q|]
  }

  lemma MiddleReconstructs(t: string, p: string, q: string)
    requires |p| + |q| <= |t|
    requires t[..|p|] == p
    requires t[|t| - |q|..] == q
    ensures t == p + Middle(t, p, q) + q
  {
    assert Middle(t, p, q) == t[|p|..|t| - |q|];
    assert t == t[..|p|] + t[|p|..|t| - |q|] + t[|t| - |q|..];
  }

  // ---- Certifying check: does every sample in strs actually admit prefix P / suffix Q? ----

  function CheckPrefixSuffixAll(strs: seq<string>, P: string, Q: string): bool
    decreases strs
  {
    strs == [] ||
    (|P| + |Q| <= |strs[0]| && strs[0][..|P|] == P && strs[0][|strs[0]| - |Q|..] == Q &&
     CheckPrefixSuffixAll(strs[1..], P, Q))
  }

  lemma CheckPrefixSuffixAllSound(strs: seq<string>, P: string, Q: string, t: string)
    requires CheckPrefixSuffixAll(strs, P, Q)
    requires t in strs
    ensures |P| + |Q| <= |t| && t[..|P|] == P && t[|t| - |Q|..] == Q
    decreases strs
  {
    if strs[0] == t {
    } else {
      CheckPrefixSuffixAllSound(strs[1..], P, Q, t);
    }
  }

  function AllMiddles(strs: seq<string>, P: string, Q: string): seq<string>
    decreases strs
  {
    if strs == [] then [] else [Middle(strs[0], P, Q)] + AllMiddles(strs[1..], P, Q)
  }

  lemma AllMiddlesMem(strs: seq<string>, P: string, Q: string, t: string)
    requires t in strs
    ensures Middle(t, P, Q) in AllMiddles(strs, P, Q)
    decreases strs
  {
    if strs[0] == t {
    } else {
      AllMiddlesMem(strs[1..], P, Q, t);
    }
  }

  lemma AllMiddlesSound(strs: seq<string>, P: string, Q: string, m: string)
    requires m in AllMiddles(strs, P, Q)
    ensures exists t :: t in strs && m == Middle(t, P, Q)
    decreases strs
  {
    if AllMiddles(strs, P, Q)[0] == m {
      assert strs[0] in strs && m == Middle(strs[0], P, Q);
    } else {
      AllMiddlesSound(strs[1..], P, Q, m);
    }
  }

  // The characters of a "middle" slice t[p..|t|-q] are a subset of t's own alphabet.
  lemma StringAlphabetMiddle(t: string, p: nat, q: nat)
    requires p + q <= |t|
    ensures StringAlphabet(t[p..|t| - q]) <= StringAlphabet(t)
  {
    StringAlphabetSuffix(t, p);
    StringAlphabetPrefix(t[p..], |t| - q - p);
    assert t[p..][..|t| - q - p] == t[p..|t| - q];
  }

  // First-occurrence deduplication: keeps membership (as a set) while giving a
  // duplicate-free (as strings) list, so distinct middles never get double-listed (and,
  // once recursed into via BuildGroups/InferGroups below, never double-solved) just
  // because two samples happen to produce the identical middle.
  function Dedup(ms: seq<string>): seq<string>
    decreases ms
  {
    if ms == [] then []
    else if ms[0] in ms[1..] then Dedup(ms[1..])
    else [ms[0]] + Dedup(ms[1..])
  }

  lemma DedupMem(ms: seq<string>, m: string)
    ensures m in Dedup(ms) <==> m in ms
    decreases ms
  {
    if ms == [] {
    } else {
      DedupMem(ms[1..], m);
    }
  }

  lemma DedupNoDup(ms: seq<string>)
    ensures forall i, j :: 0 <= i < |Dedup(ms)| && 0 <= j < |Dedup(ms)| && i != j ==> Dedup(ms)[i] != Dedup(ms)[j]
    decreases ms
  {
    if ms == [] {
    } else {
      DedupNoDup(ms[1..]);
      if ms[0] !in ms[1..] {
        DedupMem(ms[1..], ms[0]);
      }
    }
  }

  lemma DedupTotalLength(ms: seq<string>)
    ensures TotalLength(Dedup(ms)) <= TotalLength(ms)
    decreases ms
  {
    if ms == [] {
    } else {
      DedupTotalLength(ms[1..]);
    }
  }

  // ---- Sum of string lengths: the metric that makes tier 0's recursion into InferGroups
  // (see below) provably terminating - stripping a nonempty prefix/suffix from every
  // sample always strictly shrinks the total, however BuildGroups then regroups them. ----

  function TotalLength(strs: seq<string>): nat
    decreases strs
  {
    if strs == [] then 0 else |strs[0]| + TotalLength(strs[1..])
  }

  lemma TotalLengthAppend(a: seq<string>, b: seq<string>)
    ensures TotalLength(a + b) == TotalLength(a) + TotalLength(b)
    decreases a
  {
    if a == [] {
      assert a + b == b;
    } else {
      assert (a + b)[0] == a[0];
      assert (a + b)[1..] == a[1..] + b;
      TotalLengthAppend(a[1..], b);
    }
  }

  // Exact bookkeeping fact used to show tier 0's recursive call strictly shrinks: summed
  // over every sample, stripping a length-(|P|+|Q|) prefix+suffix removes exactly
  // |strs| * (|P|+|Q|) characters in total.
  lemma AllMiddlesTotalLength(strs: seq<string>, P: string, Q: string)
    requires CheckPrefixSuffixAll(strs, P, Q)
    ensures TotalLength(AllMiddles(strs, P, Q)) + |strs| * (|P| + |Q|) == TotalLength(strs)
    decreases strs
  {
    if strs == [] {
    } else {
      assert CheckPrefixSuffixAll(strs[1..], P, Q);
      AllMiddlesTotalLength(strs[1..], P, Q);
      assert |P| + |Q| <= |strs[0]|;
      assert |Middle(strs[0], P, Q)| == |strs[0]| - |P| - |Q|;
      assert AllMiddles(strs, P, Q) == [Middle(strs[0], P, Q)] + AllMiddles(strs[1..], P, Q);
      TotalLengthAppend([Middle(strs[0], P, Q)], AllMiddles(strs[1..], P, Q));
      assert TotalLength([Middle(strs[0], P, Q)]) == |Middle(strs[0], P, Q)|;
      assert (|strs| - 1) * (|P| + |Q|) == |strs[1..]| * (|P| + |Q|);
    }
  }

  // ---- Certifying checker for the Slot refinement (tier 1's tighter alternative to
  // plain ConcatAll - see Chain.dfy's BuildSlots) ----

  function CheckSlotsAll(strs: seq<string>, slots: seq<Slot>): bool
    decreases strs
  {
    strs == [] || (FitsSlots(strs[0], slots) && CheckSlotsAll(strs[1..], slots))
  }

  lemma CheckSlotsAllSound(strs: seq<string>, slots: seq<Slot>, t: string)
    requires CheckSlotsAll(strs, slots)
    requires t in strs
    ensures FitsSlots(t, slots)
    decreases strs
  {
    if strs[0] == t {
    } else {
      CheckSlotsAllSound(strs[1..], slots, t);
    }
  }

  // c in a seq iff c in its StringAlphabet (StringAlphabet is just "the set of elements",
  // spelled for seq<char> - Dafny's `string` and `seq<char>` are the same type). Moved
  // above InferGroup (from its previous position after it) since InferGroup's new
  // Slot-symbols reasoning needs it too.
  lemma StringAlphabetMem(cs: seq<char>, c: char)
    ensures c in cs <==> c in StringAlphabet(cs)
    decreases cs
  {
    if cs == [] {
    } else {
      StringAlphabetMem(cs[1..], c);
    }
  }

  // ---- Per-group inference: the original three-tier construction (global chain,
  // periodic block, wildcard), now scoped to a single batch of strings that all share
  // one connected co-occurrence component of the alphabet (see BuildGroups below). The
  // logic (the character-level chain/periodic-block/wildcard tiers, in InferGroupFallback)
  // is unchanged from before groups existed. Tier 0 above it, though, is itself now
  // recursive: after stripping a common prefix/suffix it partitions the leftover middles
  // by co-occurrence and calls back into InferGroups, so InferGroup and InferGroups below
  // are mutually recursive (see the termination comment on InferGroup). Empty strings
  // never appear in `strs` here - "" is handled once, at the very top of Infer, since it
  // belongs to no co-occurrence group. ----

  // ---- Alphabet-based split (tried after tier 0, before tier 1/2/3): generalizes an
  // earlier, more restrictive version of this tier that required a *fixed* index/length
  // on (at least) one side of every sample. Here the split point for each sample isn't a
  // shared numeric index at all - it's wherever that sample's own maximal leading (resp.
  // trailing) run of characters drawn from a candidate alphabet ends. This is what's
  // needed for e.g. {"ax","ayyy","bbx","bbyyy"}: axis 1 is {"a","bb"}, axis 2 is
  // {"x","yyy"} - neither axis has a fixed *length* ("a" vs "bb", "x" vs "yyy"), so the
  // old fixed-length tier couldn't touch it, but axis 1's characters ({a,b}) are exactly
  // a leading run, disjoint from axis 2's characters ({x,y}), in every sample. The
  // natural candidate alphabet is simply "every character ever seen as some sample's
  // first (resp. last) character" - which trivially guarantees every sample's own first
  // (resp. last) character is itself in the candidate set, and that's exactly what makes
  // the "always shrinks" half of the termination argument below unconditional. ----

  // Length of the maximal prefix of t drawn entirely from `chars`.
  function MaximalPrefixInSet(t: string, chars: set<char>): nat
    decreases |t|
  {
    if t == "" || t[0] !in chars then 0 else 1 + MaximalPrefixInSet(t[1..], chars)
  }

  lemma MaximalPrefixInSetBound(t: string, chars: set<char>)
    ensures MaximalPrefixInSet(t, chars) <= |t|
    decreases |t|
  {
    if t == "" || t[0] !in chars {
    } else {
      MaximalPrefixInSetBound(t[1..], chars);
    }
  }

  // The run is genuinely nonempty whenever t itself starts with a `chars`-character.
  lemma MaximalPrefixInSetAtLeastOne(t: string, chars: set<char>)
    requires t != "" && t[0] in chars
    ensures MaximalPrefixInSet(t, chars) >= 1
  {
  }

  // Every character strictly inside the maximal run is itself in `chars` - what makes
  // the run's own alphabet a subset of `chars`.
  lemma MaximalPrefixInSetAllIn(t: string, chars: set<char>, i: nat)
    requires i < MaximalPrefixInSet(t, chars)
    ensures i < |t| && t[i] in chars
    decreases |t|
  {
    if i == 0 {
    } else {
      MaximalPrefixInSetAllIn(t[1..], chars, i - 1);
    }
  }

  // Total (never out-of-bounds) split of t into its maximal `chars`-prefix and the rest -
  // clamped exactly like the old TakePrefix/TakeSuffix, though (per the bound lemma
  // above) the clamp is never actually triggered wherever these are used.
  function TakeFrontRun(t: string, chars: set<char>): string {
    var m := MaximalPrefixInSet(t, chars);
    if m <= |t| then t[..m] else t
  }

  function DropFrontRun(t: string, chars: set<char>): string {
    var m := MaximalPrefixInSet(t, chars);
    if m <= |t| then t[m..] else ""
  }

  lemma TakeFrontRunSplitReconstructs(t: string, chars: set<char>)
    ensures t == TakeFrontRun(t, chars) + DropFrontRun(t, chars)
  {
    MaximalPrefixInSetBound(t, chars);
  }

  function TakeFrontRuns(strs: seq<string>, chars: set<char>): seq<string>
    decreases strs
  {
    if strs == [] then [] else [TakeFrontRun(strs[0], chars)] + TakeFrontRuns(strs[1..], chars)
  }

  function DropFrontRuns(strs: seq<string>, chars: set<char>): seq<string>
    decreases strs
  {
    if strs == [] then [] else [DropFrontRun(strs[0], chars)] + DropFrontRuns(strs[1..], chars)
  }

  lemma TakeFrontRunsMem(strs: seq<string>, chars: set<char>, t: string)
    requires t in strs
    ensures TakeFrontRun(t, chars) in TakeFrontRuns(strs, chars)
    decreases strs
  {
    if strs[0] == t {
    } else {
      TakeFrontRunsMem(strs[1..], chars, t);
    }
  }

  lemma DropFrontRunsMem(strs: seq<string>, chars: set<char>, t: string)
    requires t in strs
    ensures DropFrontRun(t, chars) in DropFrontRuns(strs, chars)
    decreases strs
  {
    if strs[0] == t {
    } else {
      DropFrontRunsMem(strs[1..], chars, t);
    }
  }

  lemma TakeFrontRunsSound(strs: seq<string>, chars: set<char>, p: string)
    requires p in TakeFrontRuns(strs, chars)
    ensures exists t :: t in strs && p == TakeFrontRun(t, chars)
    decreases strs
  {
    if TakeFrontRuns(strs, chars)[0] == p {
      assert strs[0] in strs && p == TakeFrontRun(strs[0], chars);
    } else {
      TakeFrontRunsSound(strs[1..], chars, p);
    }
  }

  lemma DropFrontRunsSound(strs: seq<string>, chars: set<char>, p: string)
    requires p in DropFrontRuns(strs, chars)
    ensures exists t :: t in strs && p == DropFrontRun(t, chars)
    decreases strs
  {
    if DropFrontRuns(strs, chars)[0] == p {
      assert strs[0] in strs && p == DropFrontRun(strs[0], chars);
    } else {
      DropFrontRunsSound(strs[1..], chars, p);
    }
  }

  // The two pieces of every sample exactly account for its whole length, additively -
  // used to derive the (existential-witness-gated) strict decrease on the "run" side
  // from the unconditional strict decrease on the "rest" side below, without needing its
  // own separate case-by-case induction.
  lemma FrontRunsTotalLengthSum(strs: seq<string>, chars: set<char>)
    ensures TotalLength(TakeFrontRuns(strs, chars)) + TotalLength(DropFrontRuns(strs, chars)) == TotalLength(strs)
    decreases strs
  {
    if strs == [] {
    } else {
      TakeFrontRunSplitReconstructs(strs[0], chars);
      FrontRunsTotalLengthSum(strs[1..], chars);
    }
  }

  // Unconditional: true as soon as every sample starts with a `chars`-character, so its
  // own maximal run is at least 1 (MaximalPrefixInSetAtLeastOne), hence the "rest" is
  // strictly shorter than the sample itself.
  lemma DropFrontRunsTotalLengthLess(strs: seq<string>, chars: set<char>)
    requires strs != []
    requires forall t :: t in strs ==> t != "" && t[0] in chars
    ensures TotalLength(DropFrontRuns(strs, chars)) < TotalLength(strs)
    decreases strs
  {
    assert strs[0] in strs;
    MaximalPrefixInSetAtLeastOne(strs[0], chars);
    MaximalPrefixInSetBound(strs[0], chars);
    TakeFrontRunSplitReconstructs(strs[0], chars);
    assert |DropFrontRun(strs[0], chars)| < |strs[0]|;
    if |strs| == 1 {
    } else {
      forall t | t in strs[1..] ensures t != "" && t[0] in chars {
        assert t in strs;
      }
      DropFrontRunsTotalLengthLess(strs[1..], chars);
    }
  }

  // A list containing some nonempty element has positive total length.
  lemma SomeNonEmptyTotalLengthPos(strs: seq<string>, t0: string)
    requires t0 in strs && t0 != ""
    ensures TotalLength(strs) >= 1
    decreases strs
  {
    if strs[0] == t0 {
    } else {
      SomeNonEmptyTotalLengthPos(strs[1..], t0);
    }
  }

  // Gated on a single non-degeneracy witness t0 (some sample whose maximal `chars`-run
  // doesn't consume the whole string) rather than a uniform per-element bound, since -
  // unlike the "rest" side above - the "run" side only shrinks in total once *something*
  // is actually left over *somewhere* in the batch. Derived from the exact sum identity
  // above plus "some element of DropFrontRuns is that witness's own nonempty leftover".
  lemma TakeFrontRunsTotalLengthLess(strs: seq<string>, chars: set<char>, t0: string)
    requires t0 in strs
    requires MaximalPrefixInSet(t0, chars) < |t0|
    ensures TotalLength(TakeFrontRuns(strs, chars)) < TotalLength(strs)
  {
    FrontRunsTotalLengthSum(strs, chars);
    TakeFrontRunSplitReconstructs(t0, chars);
    assert DropFrontRun(t0, chars) != "";
    DropFrontRunsMem(strs, chars, t0);
    SomeNonEmptyTotalLengthPos(DropFrontRuns(strs, chars), DropFrontRun(t0, chars));
  }

  // Heuristic search for a non-degeneracy witness (some sample whose maximal `chars`-run
  // doesn't consume it entirely) - no correctness burden beyond terminating and (on
  // success) actually exhibiting that witness, proved as an ordinary postcondition.
  function FindNonDegenerateWitness(strs: seq<string>, chars: set<char>): (bool, string)
    decreases strs
    ensures FindNonDegenerateWitness(strs, chars).0 ==>
      FindNonDegenerateWitness(strs, chars).1 in strs &&
      MaximalPrefixInSet(FindNonDegenerateWitness(strs, chars).1, chars) < |FindNonDegenerateWitness(strs, chars).1|
  {
    if strs == [] then (false, "")
    else if MaximalPrefixInSet(strs[0], chars) < |strs[0]| then (true, strs[0])
    else FindNonDegenerateWitness(strs[1..], chars)
  }

  // "Every character ever seen as some sample's first character" - the front-split's
  // candidate alphabet.
  function FrontAlphabet(strs: seq<string>): set<char>
    requires "" !in strs
    decreases strs
  {
    if strs == [] then {} else {strs[0][0]} + FrontAlphabet(strs[1..])
  }

  lemma FrontAlphabetMem(strs: seq<string>, t: string)
    requires "" !in strs
    requires t in strs
    ensures t[0] in FrontAlphabet(strs)
    decreases strs
  {
    if strs[0] == t {
    } else {
      FrontAlphabetMem(strs[1..], t);
    }
  }

  // Every candidate-alphabet character really does come from strs's own alphabet.
  lemma FrontAlphabetInAlphabetAll(strs: seq<string>)
    requires "" !in strs
    ensures FrontAlphabet(strs) <= AlphabetAll(strs)
    decreases strs
  {
    if strs == [] {
    } else {
      FrontAlphabetInAlphabetAll(strs[1..]);
      StringAlphabetSound(strs[0], 0);
    }
  }

  // ---- The mirror-image variant: split on the maximal *trailing* run of a candidate
  // "last characters seen" alphabet instead - e.g. {"xa","xb","yya","yyb"}. ----

  function MaximalSuffixInSet(t: string, chars: set<char>): nat
    decreases |t|
  {
    if t == "" || t[|t| - 1] !in chars then 0 else 1 + MaximalSuffixInSet(t[..|t| - 1], chars)
  }

  lemma MaximalSuffixInSetBound(t: string, chars: set<char>)
    ensures MaximalSuffixInSet(t, chars) <= |t|
    decreases |t|
  {
    if t == "" || t[|t| - 1] !in chars {
    } else {
      MaximalSuffixInSetBound(t[..|t| - 1], chars);
    }
  }

  lemma MaximalSuffixInSetAtLeastOne(t: string, chars: set<char>)
    requires t != "" && t[|t| - 1] in chars
    ensures MaximalSuffixInSet(t, chars) >= 1
  {
  }

  // Every character strictly inside the maximal (trailing) run is itself in `chars`.
  lemma MaximalSuffixInSetAllIn(t: string, chars: set<char>, i: nat)
    requires |t| - MaximalSuffixInSet(t, chars) <= i < |t|
    ensures t[i] in chars
    decreases |t|
  {
    if t == "" || t[|t| - 1] !in chars {
    } else if i == |t| - 1 {
    } else {
      MaximalSuffixInSetAllIn(t[..|t| - 1], chars, i);
    }
  }

  function TakeBackRun(t: string, chars: set<char>): string {
    var m := MaximalSuffixInSet(t, chars);
    if m <= |t| then t[|t| - m..] else t
  }

  function DropBackRun(t: string, chars: set<char>): string {
    var m := MaximalSuffixInSet(t, chars);
    if m <= |t| then t[..|t| - m] else ""
  }

  lemma TakeBackRunSplitReconstructs(t: string, chars: set<char>)
    ensures t == DropBackRun(t, chars) + TakeBackRun(t, chars)
  {
    MaximalSuffixInSetBound(t, chars);
  }

  function TakeBackRuns(strs: seq<string>, chars: set<char>): seq<string>
    decreases strs
  {
    if strs == [] then [] else [TakeBackRun(strs[0], chars)] + TakeBackRuns(strs[1..], chars)
  }

  function DropBackRuns(strs: seq<string>, chars: set<char>): seq<string>
    decreases strs
  {
    if strs == [] then [] else [DropBackRun(strs[0], chars)] + DropBackRuns(strs[1..], chars)
  }

  lemma TakeBackRunsMem(strs: seq<string>, chars: set<char>, t: string)
    requires t in strs
    ensures TakeBackRun(t, chars) in TakeBackRuns(strs, chars)
    decreases strs
  {
    if strs[0] == t {
    } else {
      TakeBackRunsMem(strs[1..], chars, t);
    }
  }

  lemma DropBackRunsMem(strs: seq<string>, chars: set<char>, t: string)
    requires t in strs
    ensures DropBackRun(t, chars) in DropBackRuns(strs, chars)
    decreases strs
  {
    if strs[0] == t {
    } else {
      DropBackRunsMem(strs[1..], chars, t);
    }
  }

  lemma TakeBackRunsSound(strs: seq<string>, chars: set<char>, p: string)
    requires p in TakeBackRuns(strs, chars)
    ensures exists t :: t in strs && p == TakeBackRun(t, chars)
    decreases strs
  {
    if TakeBackRuns(strs, chars)[0] == p {
      assert strs[0] in strs && p == TakeBackRun(strs[0], chars);
    } else {
      TakeBackRunsSound(strs[1..], chars, p);
    }
  }

  lemma DropBackRunsSound(strs: seq<string>, chars: set<char>, p: string)
    requires p in DropBackRuns(strs, chars)
    ensures exists t :: t in strs && p == DropBackRun(t, chars)
    decreases strs
  {
    if DropBackRuns(strs, chars)[0] == p {
      assert strs[0] in strs && p == DropBackRun(strs[0], chars);
    } else {
      DropBackRunsSound(strs[1..], chars, p);
    }
  }

  lemma BackRunsTotalLengthSum(strs: seq<string>, chars: set<char>)
    ensures TotalLength(DropBackRuns(strs, chars)) + TotalLength(TakeBackRuns(strs, chars)) == TotalLength(strs)
    decreases strs
  {
    if strs == [] {
    } else {
      TakeBackRunSplitReconstructs(strs[0], chars);
      BackRunsTotalLengthSum(strs[1..], chars);
    }
  }

  // Unconditional: true as soon as every sample ends with a `chars`-character, so its
  // own maximal trailing run is at least 1 (MaximalSuffixInSetAtLeastOne), hence the
  // leading remainder before it is strictly shorter than the sample itself.
  // Derived from the exact sum identity (BackRunsTotalLengthSum) rather than its own
  // per-element induction: some element's trailing run is nonempty (any element, given
  // every sample ends with a `chars`-character), so TakeBackRuns' total is positive,
  // hence DropBackRuns' total is strictly less than the whole.
  lemma DropBackRunsTotalLengthLess(strs: seq<string>, chars: set<char>)
    requires strs != []
    requires forall t :: t in strs ==> t != "" && t[|t| - 1] in chars
    ensures TotalLength(DropBackRuns(strs, chars)) < TotalLength(strs)
  {
    BackRunsTotalLengthSum(strs, chars);
    assert strs[0] in strs;
    MaximalSuffixInSetAtLeastOne(strs[0], chars);
    TakeBackRunSplitReconstructs(strs[0], chars);
    assert TakeBackRun(strs[0], chars) != "";
    TakeBackRunsMem(strs, chars, strs[0]);
    SomeNonEmptyTotalLengthPos(TakeBackRuns(strs, chars), TakeBackRun(strs[0], chars));
  }

  // Gated on a non-degeneracy witness (mirrors TakeFrontRunsTotalLengthLess): the
  // trailing run itself only shrinks in total once *something* is left over somewhere
  // in the batch.
  lemma TakeBackRunsTotalLengthLess(strs: seq<string>, chars: set<char>, t0: string)
    requires t0 in strs
    requires MaximalSuffixInSet(t0, chars) < |t0|
    ensures TotalLength(TakeBackRuns(strs, chars)) < TotalLength(strs)
  {
    BackRunsTotalLengthSum(strs, chars);
    TakeBackRunSplitReconstructs(t0, chars);
    assert DropBackRun(t0, chars) != "";
    DropBackRunsMem(strs, chars, t0);
    SomeNonEmptyTotalLengthPos(DropBackRuns(strs, chars), DropBackRun(t0, chars));
  }

  function FindNonDegenerateWitnessBack(strs: seq<string>, chars: set<char>): (bool, string)
    decreases strs
    ensures FindNonDegenerateWitnessBack(strs, chars).0 ==>
      FindNonDegenerateWitnessBack(strs, chars).1 in strs &&
      MaximalSuffixInSet(FindNonDegenerateWitnessBack(strs, chars).1, chars) < |FindNonDegenerateWitnessBack(strs, chars).1|
  {
    if strs == [] then (false, "")
    else if MaximalSuffixInSet(strs[0], chars) < |strs[0]| then (true, strs[0])
    else FindNonDegenerateWitnessBack(strs[1..], chars)
  }

  function BackAlphabet(strs: seq<string>): set<char>
    requires "" !in strs
    decreases strs
  {
    if strs == [] then {} else {strs[0][|strs[0]| - 1]} + BackAlphabet(strs[1..])
  }

  lemma BackAlphabetMem(strs: seq<string>, t: string)
    requires "" !in strs
    requires t in strs
    ensures t[|t| - 1] in BackAlphabet(strs)
    decreases strs
  {
    if strs[0] == t {
    } else {
      BackAlphabetMem(strs[1..], t);
    }
  }

  lemma BackAlphabetInAlphabetAll(strs: seq<string>)
    requires "" !in strs
    ensures BackAlphabet(strs) <= AlphabetAll(strs)
    decreases strs
  {
    if strs == [] {
    } else {
      BackAlphabetInAlphabetAll(strs[1..]);
      StringAlphabetSound(strs[0], |strs[0]| - 1);
    }
  }

  // Tier 0's regex, spelled once so the lemmas below and InferGroup all mean the same
  // thing by "r". `rMid` is whatever the recursive partition-and-solve step (BuildGroups
  // + InferGroups, or Opt of that if one of the middles was "") produced for the
  // "distinctMiddles" - this function itself doesn't care how rMid was built.
  function Tier0Regex(P: string, Q: string, rMid: Regex): Regex {
    Concat(ConcatLiteral(P), Concat(rMid, ConcatLiteral(Q)))
  }

  // Generalized over an arbitrary middle-regex rMid (rather than baking in
  // UnionOfLiterals): tier 0 is now recursive (see InferGroup below), so the "regex for
  // the middles" can itself be an arbitrary Union of sub-group regexes, not just a flat
  // union of literal blocks. All this lemma needs from rMid is that it's already known
  // sound/single-occurrence and that its symbols stay within distinctMiddles' alphabet.
  lemma Tier0IsSoreOf(P: string, Q: string, distinctMiddles: seq<string>, rMid: Regex)
    requires NoDup(P) && NoDup(Q) && NoDup(P + Q)
    requires IsSore(rMid)
    requires forall c :: c in Symbols(rMid) ==> c in AlphabetAll(distinctMiddles)
    requires StringAlphabet(P) * AlphabetAll(distinctMiddles) == {}
    requires StringAlphabet(Q) * AlphabetAll(distinctMiddles) == {}
    ensures IsSore(Tier0Regex(P, Q, rMid))
  {
    if P == "" { assert ConcatLiteral(P) == Eps; EpsIsSore(); } else { NoDupImpliesConcatLiteralSore(P); }
    if Q == "" { assert ConcatLiteral(Q) == Eps; EpsIsSore(); } else { NoDupImpliesConcatLiteralSore(Q); }
    ConcatLiteralSymbols(P);
    ConcatLiteralSymbols(Q);

    forall c ensures c !in Symbols(rMid) || c !in Symbols(ConcatLiteral(Q)) {
      if c in Symbols(rMid) {
        assert c in AlphabetAll(distinctMiddles);
        if c in Symbols(ConcatLiteral(Q)) {
          assert c in multiset(Q);
          assert c in Q;
          assert c in StringAlphabet(Q) by { StringAlphabetMem(Q, c); }
          assert false;
        }
      }
    }
    SymbolsDisjointIsSore(rMid, ConcatLiteral(Q));

    forall c ensures c !in Symbols(ConcatLiteral(P)) || c !in Symbols(Concat(rMid, ConcatLiteral(Q))) {
      if c in Symbols(ConcatLiteral(P)) && c in Symbols(Concat(rMid, ConcatLiteral(Q))) {
        assert c in multiset(P);
        assert c in P;
        assert c in StringAlphabet(P) by { StringAlphabetMem(P, c); }
        if c in Symbols(rMid) {
          assert c in AlphabetAll(distinctMiddles);
          assert false;
        } else {
          assert c in Symbols(ConcatLiteral(Q));
          assert c in multiset(Q);
          assert c in Q;
          NoDupConcatDisjoint(P, Q);
          assert false;
        }
      }
    }
    SymbolsDisjointIsSore(ConcatLiteral(P), Concat(rMid, ConcatLiteral(Q)));
  }

  lemma Tier0SoundOf(strs: seq<string>, P: string, Q: string, middles: seq<string>, distinctMiddles: seq<string>, rMid: Regex, t: string)
    requires CheckPrefixSuffixAll(strs, P, Q)
    requires middles == AllMiddles(strs, P, Q)
    requires distinctMiddles == Dedup(middles)
    requires t in strs
    requires Matches(rMid, Middle(t, P, Q))
    ensures Matches(Tier0Regex(P, Q, rMid), t)
  {
    var r := Tier0Regex(P, Q, rMid);
    CheckPrefixSuffixAllSound(strs, P, Q, t);
    var mid := Middle(t, P, Q);
    MiddleReconstructs(t, P, Q);
    assert t == P + mid + Q;
    assert Matches(rMid, mid);
    if Q == "" { assert ConcatLiteral(Q) == Eps; } else { ConcatLiteralMatchesBlock(Q); }
    assert Matches(ConcatLiteral(Q), Q);
    assert (mid + Q)[..|mid|] == mid;
    assert (mid + Q)[|mid|..] == Q;
    assert Matches(Concat(rMid, ConcatLiteral(Q)), mid + Q) by {
      assert 0 <= |mid| <= |mid + Q| &&
        Matches(rMid, (mid + Q)[..|mid|]) &&
        Matches(ConcatLiteral(Q), (mid + Q)[|mid|..]);
    }
    if P == "" { assert ConcatLiteral(P) == Eps; } else { ConcatLiteralMatchesBlock(P); }
    assert Matches(ConcatLiteral(P), P);
    assert (P + (mid + Q))[..|P|] == P;
    assert (P + (mid + Q))[|P|..] == mid + Q;
    assert t == P + (mid + Q);
    assert Matches(r, t) by {
      assert 0 <= |P| <= |t| &&
        Matches(ConcatLiteral(P), t[..|P|]) &&
        Matches(Concat(rMid, ConcatLiteral(Q)), t[|P|..]);
    }
  }

  // Every distinct middle's characters come from some actual sample in strs.
  lemma DistinctMiddlesAlphabetInStrs(strs: seq<string>, P: string, Q: string, middles: seq<string>, distinctMiddles: seq<string>, m: string)
    requires CheckPrefixSuffixAll(strs, P, Q)
    requires middles == AllMiddles(strs, P, Q)
    requires distinctMiddles == Dedup(middles)
    requires m in distinctMiddles
    ensures StringAlphabet(m) <= AlphabetAll(strs)
  {
    DedupMem(middles, m);
    AllMiddlesSound(strs, P, Q, m);
    var t :| t in strs && m == Middle(t, P, Q);
    CheckPrefixSuffixAllSound(strs, P, Q, t);
    StringAlphabetMiddle(t, |P|, |Q|);
    StringAlphabetInAlphabetAll(strs, t);
    assert m == t[|P|..|t| - |Q|];
  }

  // Termination: InferGroup and InferGroups (below) are mutually recursive - tier 0 here
  // hands the leftover "middles" to InferGroups, which in turn calls back into
  // InferGroup for each of ITS partition's members. The two edges behave differently:
  //   - InferGroup -> InferGroups(midGroups): always strictly shrinks TotalLength, since
  //     tier 0 only recurses when something nonempty (P and/or Q) was actually stripped
  //     from every sample (see the `strs != [] && (P != "" || Q != "")` guard below).
  //   - InferGroups(groups) -> InferGroup(groups[0].1): can be a NO-OP in terms of total
  //     length - BuildGroups may partition a batch of strings into a single group
  //     covering all of them (e.g. {"opt1","opt2"}, which share {o,p,t} and can't be
  //     split further by co-occurrence alone), so groups[0].1 can have the same total
  //     length as the batch InferGroups was given.
  // A lexicographic (TotalLength, tag) pair resolves this: InferGroupPositionalSplit's
  // tag is 0, InferGroup's tag is 1, InferGroups' tag is 2, so every "always-safe" edge
  // (any recursive call whose TotalLength strictly shrinks) is licensed by TotalLength
  // alone, and every "no-shrink tie" edge (InferGroup -> InferGroupPositionalSplit with
  // the very same strs, and InferGroups -> InferGroup when BuildGroups doesn't split a
  // batch at all) is licensed by the tag order alone (0 < 1 < 2).
  method {:timeLimitMultiplier 4} InferGroup(strs: seq<string>) returns (r: Regex)
    requires "" !in strs
    ensures forall t :: t in strs ==> Matches(r, t)
    ensures IsSore(r)
    ensures forall c :: c in Symbols(r) ==> c in AlphabetAll(strs)
    decreases TotalLength(strs), 1
  {
    // Tier 0: common-prefix/common-suffix alternation (e.g. "SABE"/"SXYE" -> S(?:AB|XY)E),
    // now RECURSIVE - after stripping the longest common prefix P and suffix Q, the
    // leftover "middles" are partitioned by co-occurrence (BuildGroups) and each
    // resulting sub-batch solved by recursing into InferGroups, rather than requiring the
    // middles to already be pairwise alphabet-disjoint up front. This is what lets e.g.
    // {"Xreq","Xopt1","Xopt2"} recurse a second time on {"opt1","opt2"} (after peeling "X"
    // and finding "req" already disjoint from them) to notice they share a further common
    // prefix "opt" and disjoint single-character tails "1"/"2". Falls through to the
    // existing tier-1/tier-2/tier-3 construction (InferGroupFallback), completely
    // unchanged, if its own independent checks fail - or if there's nothing to strip at
    // all (P == "" && Q == ""), since recursing on the very same batch of strings would
    // make no progress.
    var P := LCP(strs);
    var Q := LCS(strs);

    if strs != [] && (P != "" || Q != "") &&
       CheckPrefixSuffixAll(strs, P, Q) && NoDup(P) && NoDup(Q) && NoDup(P + Q) {
      var middles := AllMiddles(strs, P, Q);
      var distinctMiddles := Dedup(middles);

      if StringAlphabet(P) * AlphabetAll(distinctMiddles) == {} &&
         StringAlphabet(Q) * AlphabetAll(distinctMiddles) == {} {
        // Termination for this call: AllMiddles strips a nonempty |P|+|Q| from every one
        // of the (>= 1, since strs != []) samples, so the middles' total length is
        // strictly less than strs's; Dedup only ever removes further; BuildGroups just
        // regroups strings without changing their total length.
        AllMiddlesTotalLength(strs, P, Q);
        DedupTotalLength(middles);
        assert TotalLength(distinctMiddles) < TotalLength(strs);

        var midGroups := BuildGroups(distinctMiddles, []);
        BuildGroupsDisjoint(distinctMiddles, []);
        BuildGroupsContained(distinctMiddles, []);
        BuildGroupsNoEmpty(distinctMiddles, []);
        BuildGroupsTotalLength(distinctMiddles, []);
        assert TotalLength(ConcatMembers(midGroups)) == TotalLength(distinctMiddles);

        var rMid0 := InferGroups(midGroups);

        BuildGroupsAlphaBound(distinctMiddles, []);
        assert UnionAlphas(midGroups) <= AlphabetAll(distinctMiddles);
        forall c | c in Symbols(rMid0) ensures c in AlphabetAll(distinctMiddles) {
          assert c in UnionAlphas(midGroups);
        }

        var rMid: Regex;
        if "" in distinctMiddles {
          rMid := Opt(rMid0);
          OptIsSore(rMid0);
        } else {
          rMid := rMid0;
        }
        assert Symbols(rMid) == Symbols(rMid0);

        Tier0IsSoreOf(P, Q, distinctMiddles, rMid);
        r := Tier0Regex(P, Q, rMid);

        forall t | t in strs ensures Matches(r, t) {
          CheckPrefixSuffixAllSound(strs, P, Q, t);
          var mid := Middle(t, P, Q);
          MiddleReconstructs(t, P, Q);
          AllMiddlesMem(strs, P, Q, t);
          DedupMem(middles, mid);
          assert mid in distinctMiddles;
          if mid == "" {
            OptSoundEps(rMid0);
          } else {
            StringAlphabetSound(mid, 0);
            assert StringAlphabet(mid) != {};
            BuildGroupsCoversAll(distinctMiddles, mid);
            assert mid in ConcatMembers(midGroups);
            if "" in distinctMiddles {
              OptSound(rMid0, mid);
            }
          }
          assert Matches(rMid, mid);
          Tier0SoundOf(strs, P, Q, middles, distinctMiddles, rMid, t);
        }

        forall m | m in distinctMiddles ensures StringAlphabet(m) <= AlphabetAll(strs) {
          DistinctMiddlesAlphabetInStrs(strs, P, Q, middles, distinctMiddles, m);
        }
        MembersContainedImpliesAlphabetAll(distinctMiddles, AlphabetAll(strs));
        assert AlphabetAll(distinctMiddles) <= AlphabetAll(strs);

        forall c | c in Symbols(r) ensures c in AlphabetAll(strs) {
          ConcatLiteralSymbols(P);
          ConcatLiteralSymbols(Q);
          assert Symbols(r) == Symbols(ConcatLiteral(P)) + Symbols(Concat(rMid, ConcatLiteral(Q)));
          assert Symbols(Concat(rMid, ConcatLiteral(Q))) == Symbols(rMid) + Symbols(ConcatLiteral(Q));
          if c in multiset(P) {
            assert c in P;
            LCPIsPrefix(strs, strs[0]);
            StringAlphabetPrefix(strs[0], |P|);
            StringAlphabetInAlphabetAll(strs, strs[0]);
            assert c in StringAlphabet(strs[0][..|P|]) by { StringAlphabetMem(P, c); }
          } else if c in multiset(Q) {
            assert c in Q;
            LCSIsSuffix(strs, strs[0]);
            StringAlphabetSuffix(strs[0], |strs[0]| - |Q|);
            StringAlphabetInAlphabetAll(strs, strs[0]);
            assert c in StringAlphabet(strs[0][|strs[0]| - |Q|..]) by { StringAlphabetMem(Q, c); }
          } else {
            assert c in Symbols(rMid);
            assert c in Symbols(rMid0);
            assert c in AlphabetAll(distinctMiddles);
          }
        }
      } else {
        r := InferGroupPositionalSplit(strs);
      }
    } else {
      r := InferGroupPositionalSplit(strs);
    }
  }

  // See the block comment above InferGroup for the termination scheme (tags 0/1/2).
  method InferGroupPositionalSplit(strs: seq<string>) returns (r: Regex)
    requires "" !in strs
    ensures forall t :: t in strs ==> Matches(r, t)
    ensures IsSore(r)
    ensures forall c :: c in Symbols(r) ==> c in AlphabetAll(strs)
    decreases TotalLength(strs), 0
  {
    if strs == [] {
      r := InferGroupFallback(strs);
      return;
    }

    var Sigma1 := FrontAlphabet(strs);
    var (found1, t0) := FindNonDegenerateWitness(strs, Sigma1);

    if found1 && AlphabetAll(Dedup(DropFrontRuns(strs, Sigma1))) * Sigma1 == {} {
      forall t | t in strs ensures t[0] in Sigma1 {
        FrontAlphabetMem(strs, t);
      }

      var Prefixes := Dedup(TakeFrontRuns(strs, Sigma1));
      var Suffixes := Dedup(DropFrontRuns(strs, Sigma1));

      TakeFrontRunsTotalLengthLess(strs, Sigma1, t0);
      DedupTotalLength(TakeFrontRuns(strs, Sigma1));
      assert TotalLength(Prefixes) < TotalLength(strs);

      DropFrontRunsTotalLengthLess(strs, Sigma1);
      DedupTotalLength(DropFrontRuns(strs, Sigma1));
      assert TotalLength(Suffixes) < TotalLength(strs);

      assert "" !in Prefixes by {
        forall p | p in Prefixes ensures p != "" {
          DedupMem(TakeFrontRuns(strs, Sigma1), p);
          TakeFrontRunsSound(strs, Sigma1, p);
          var t :| t in strs && p == TakeFrontRun(t, Sigma1);
          MaximalPrefixInSetAtLeastOne(t, Sigma1);
        }
      }

      var prefGroups := BuildGroups(Prefixes, []);
      BuildGroupsDisjoint(Prefixes, []);
      BuildGroupsContained(Prefixes, []);
      BuildGroupsNoEmpty(Prefixes, []);
      BuildGroupsTotalLength(Prefixes, []);
      assert TotalLength(ConcatMembers(prefGroups)) == TotalLength(Prefixes);

      var sufGroups := BuildGroups(Suffixes, []);
      BuildGroupsDisjoint(Suffixes, []);
      BuildGroupsContained(Suffixes, []);
      BuildGroupsNoEmpty(Suffixes, []);
      BuildGroupsTotalLength(Suffixes, []);
      assert TotalLength(ConcatMembers(sufGroups)) == TotalLength(Suffixes);

      var rPre := InferGroups(prefGroups);
      var rSuf0 := InferGroups(sufGroups);

      var rSuf: Regex;
      if "" in Suffixes {
        rSuf := Opt(rSuf0);
        OptIsSore(rSuf0);
      } else {
        rSuf := rSuf0;
      }
      assert Symbols(rSuf) == Symbols(rSuf0);

      BuildGroupsAlphaBound(Prefixes, []);
      assert UnionAlphas(prefGroups) <= AlphabetAll(Prefixes);
      BuildGroupsAlphaBound(Suffixes, []);
      assert UnionAlphas(sufGroups) <= AlphabetAll(Suffixes);

      assert AlphabetAll(Prefixes) <= Sigma1 by {
        forall p | p in Prefixes ensures StringAlphabet(p) <= Sigma1 {
          DedupMem(TakeFrontRuns(strs, Sigma1), p);
          TakeFrontRunsSound(strs, Sigma1, p);
          var t :| t in strs && p == TakeFrontRun(t, Sigma1);
          MaximalPrefixInSetBound(t, Sigma1);
          assert p == t[..MaximalPrefixInSet(t, Sigma1)];
          forall i | 0 <= i < |p| ensures p[i] in Sigma1 {
            assert p[i] == t[i];
            MaximalPrefixInSetAllIn(t, Sigma1, i);
          }
          StringAlphabetSubsetIfAllIn(p, Sigma1);
        }
        MembersContainedImpliesAlphabetAll(Prefixes, Sigma1);
      }

      assert AlphabetAll(Prefixes) * AlphabetAll(Suffixes) == {};

      forall c | c in Symbols(rPre) ensures c !in Symbols(rSuf) {
        assert c in AlphabetAll(Prefixes);
        if c in Symbols(rSuf) {
          assert c in AlphabetAll(Suffixes);
          assert false;
        }
      }
      SymbolsDisjointIsSore(rPre, rSuf);
      r := Concat(rPre, rSuf);

      forall t | t in strs ensures Matches(r, t) {
        TakeFrontRunSplitReconstructs(t, Sigma1);
        assert t == TakeFrontRun(t, Sigma1) + DropFrontRun(t, Sigma1);

        TakeFrontRunsMem(strs, Sigma1, t);
        DedupMem(TakeFrontRuns(strs, Sigma1), TakeFrontRun(t, Sigma1));
        assert TakeFrontRun(t, Sigma1) in Prefixes;

        DropFrontRunsMem(strs, Sigma1, t);
        DedupMem(DropFrontRuns(strs, Sigma1), DropFrontRun(t, Sigma1));
        assert DropFrontRun(t, Sigma1) in Suffixes;

        assert TakeFrontRun(t, Sigma1) != "";
        StringAlphabetSound(TakeFrontRun(t, Sigma1), 0);
        assert StringAlphabet(TakeFrontRun(t, Sigma1)) != {};
        BuildGroupsCoversAll(Prefixes, TakeFrontRun(t, Sigma1));
        assert TakeFrontRun(t, Sigma1) in ConcatMembers(prefGroups);
        assert Matches(rPre, TakeFrontRun(t, Sigma1));

        if DropFrontRun(t, Sigma1) == "" {
          OptSoundEps(rSuf0);
        } else {
          StringAlphabetSound(DropFrontRun(t, Sigma1), 0);
          assert StringAlphabet(DropFrontRun(t, Sigma1)) != {};
          BuildGroupsCoversAll(Suffixes, DropFrontRun(t, Sigma1));
          assert DropFrontRun(t, Sigma1) in ConcatMembers(sufGroups);
          if "" in Suffixes {
            OptSound(rSuf0, DropFrontRun(t, Sigma1));
          }
        }
        assert Matches(rSuf, DropFrontRun(t, Sigma1));

        MaximalPrefixInSetBound(t, Sigma1);
        assert t[..MaximalPrefixInSet(t, Sigma1)] == TakeFrontRun(t, Sigma1);
        assert t[MaximalPrefixInSet(t, Sigma1)..] == DropFrontRun(t, Sigma1);
        assert Matches(r, t) by {
          assert 0 <= MaximalPrefixInSet(t, Sigma1) <= |t| &&
            Matches(rPre, t[..MaximalPrefixInSet(t, Sigma1)]) &&
            Matches(rSuf, t[MaximalPrefixInSet(t, Sigma1)..]);
        }
      }

      FrontAlphabetInAlphabetAll(strs);
      assert Sigma1 <= AlphabetAll(strs);

      forall p | p in Suffixes ensures StringAlphabet(p) <= AlphabetAll(strs) {
        DedupMem(DropFrontRuns(strs, Sigma1), p);
        DropFrontRunsSound(strs, Sigma1, p);
        var t :| t in strs && p == DropFrontRun(t, Sigma1);
        MaximalPrefixInSetBound(t, Sigma1);
        assert p == t[MaximalPrefixInSet(t, Sigma1)..];
        StringAlphabetSuffix(t, MaximalPrefixInSet(t, Sigma1));
        StringAlphabetInAlphabetAll(strs, t);
      }
      MembersContainedImpliesAlphabetAll(Suffixes, AlphabetAll(strs));
      assert AlphabetAll(Suffixes) <= AlphabetAll(strs);

      forall c | c in Symbols(r) ensures c in AlphabetAll(strs) {
        if c in Symbols(rPre) {
          assert c in AlphabetAll(Prefixes);
          assert c in Sigma1;
        } else {
          assert c in Symbols(rSuf);
          assert c in Symbols(rSuf0);
          assert c in AlphabetAll(Suffixes);
        }
      }
    } else {
      // Mirror-image variant: split on the maximal *trailing* run of the "last
      // characters seen" alphabet instead - e.g. {"xa","xb","yya","yyb"}. Tried only
      // after the front-alphabet variant above fails to find any usable split.
      var Sigma2 := BackAlphabet(strs);
      var (found2, t1) := FindNonDegenerateWitnessBack(strs, Sigma2);

      if found2 && AlphabetAll(Dedup(DropBackRuns(strs, Sigma2))) * Sigma2 == {} {
        forall t | t in strs ensures t[|t| - 1] in Sigma2 {
          BackAlphabetMem(strs, t);
        }

        var Prefixes := Dedup(DropBackRuns(strs, Sigma2));
        var Suffixes := Dedup(TakeBackRuns(strs, Sigma2));

        DropBackRunsTotalLengthLess(strs, Sigma2);
        DedupTotalLength(DropBackRuns(strs, Sigma2));
        assert TotalLength(Prefixes) < TotalLength(strs);

        TakeBackRunsTotalLengthLess(strs, Sigma2, t1);
        DedupTotalLength(TakeBackRuns(strs, Sigma2));
        assert TotalLength(Suffixes) < TotalLength(strs);

        assert "" !in Suffixes by {
          forall p | p in Suffixes ensures p != "" {
            DedupMem(TakeBackRuns(strs, Sigma2), p);
            TakeBackRunsSound(strs, Sigma2, p);
            var t :| t in strs && p == TakeBackRun(t, Sigma2);
            MaximalSuffixInSetAtLeastOne(t, Sigma2);
          }
        }

        var prefGroups := BuildGroups(Prefixes, []);
        BuildGroupsDisjoint(Prefixes, []);
        BuildGroupsContained(Prefixes, []);
        BuildGroupsNoEmpty(Prefixes, []);
        BuildGroupsTotalLength(Prefixes, []);
        assert TotalLength(ConcatMembers(prefGroups)) == TotalLength(Prefixes);

        var sufGroups := BuildGroups(Suffixes, []);
        BuildGroupsDisjoint(Suffixes, []);
        BuildGroupsContained(Suffixes, []);
        BuildGroupsNoEmpty(Suffixes, []);
        BuildGroupsTotalLength(Suffixes, []);
        assert TotalLength(ConcatMembers(sufGroups)) == TotalLength(Suffixes);

        var rPre0 := InferGroups(prefGroups);
        var rSuf := InferGroups(sufGroups);

        var rPre: Regex;
        if "" in Prefixes {
          rPre := Opt(rPre0);
          OptIsSore(rPre0);
        } else {
          rPre := rPre0;
        }
        assert Symbols(rPre) == Symbols(rPre0);

        BuildGroupsAlphaBound(Prefixes, []);
        assert UnionAlphas(prefGroups) <= AlphabetAll(Prefixes);
        BuildGroupsAlphaBound(Suffixes, []);
        assert UnionAlphas(sufGroups) <= AlphabetAll(Suffixes);

        assert AlphabetAll(Suffixes) <= Sigma2 by {
          forall p | p in Suffixes ensures StringAlphabet(p) <= Sigma2 {
            DedupMem(TakeBackRuns(strs, Sigma2), p);
            TakeBackRunsSound(strs, Sigma2, p);
            var t :| t in strs && p == TakeBackRun(t, Sigma2);
            MaximalSuffixInSetBound(t, Sigma2);
            assert p == t[|t| - MaximalSuffixInSet(t, Sigma2)..];
            forall i | 0 <= i < |p| ensures p[i] in Sigma2 {
              assert p[i] == t[|t| - MaximalSuffixInSet(t, Sigma2) + i];
              MaximalSuffixInSetAllIn(t, Sigma2, |t| - MaximalSuffixInSet(t, Sigma2) + i);
            }
            StringAlphabetSubsetIfAllIn(p, Sigma2);
          }
          MembersContainedImpliesAlphabetAll(Suffixes, Sigma2);
        }

        assert AlphabetAll(Prefixes) * AlphabetAll(Suffixes) == {};

        forall c | c in Symbols(rSuf) ensures c !in Symbols(rPre) {
          assert c in AlphabetAll(Suffixes);
          if c in Symbols(rPre) {
            assert c in AlphabetAll(Prefixes);
            assert false;
          }
        }
        SymbolsDisjointIsSore(rPre, rSuf);
        r := Concat(rPre, rSuf);

        forall t | t in strs ensures Matches(r, t) {
          TakeBackRunSplitReconstructs(t, Sigma2);
          assert t == DropBackRun(t, Sigma2) + TakeBackRun(t, Sigma2);

          DropBackRunsMem(strs, Sigma2, t);
          DedupMem(DropBackRuns(strs, Sigma2), DropBackRun(t, Sigma2));
          assert DropBackRun(t, Sigma2) in Prefixes;

          TakeBackRunsMem(strs, Sigma2, t);
          DedupMem(TakeBackRuns(strs, Sigma2), TakeBackRun(t, Sigma2));
          assert TakeBackRun(t, Sigma2) in Suffixes;

          assert TakeBackRun(t, Sigma2) != "";
          StringAlphabetSound(TakeBackRun(t, Sigma2), 0);
          assert StringAlphabet(TakeBackRun(t, Sigma2)) != {};
          BuildGroupsCoversAll(Suffixes, TakeBackRun(t, Sigma2));
          assert TakeBackRun(t, Sigma2) in ConcatMembers(sufGroups);
          assert Matches(rSuf, TakeBackRun(t, Sigma2));

          if DropBackRun(t, Sigma2) == "" {
            OptSoundEps(rPre0);
          } else {
            StringAlphabetSound(DropBackRun(t, Sigma2), 0);
            assert StringAlphabet(DropBackRun(t, Sigma2)) != {};
            BuildGroupsCoversAll(Prefixes, DropBackRun(t, Sigma2));
            assert DropBackRun(t, Sigma2) in ConcatMembers(prefGroups);
            if "" in Prefixes {
              OptSound(rPre0, DropBackRun(t, Sigma2));
            }
          }
          assert Matches(rPre, DropBackRun(t, Sigma2));

          MaximalSuffixInSetBound(t, Sigma2);
          assert t[..|t| - MaximalSuffixInSet(t, Sigma2)] == DropBackRun(t, Sigma2);
          assert t[|t| - MaximalSuffixInSet(t, Sigma2)..] == TakeBackRun(t, Sigma2);
          assert Matches(r, t) by {
            assert 0 <= |t| - MaximalSuffixInSet(t, Sigma2) <= |t| &&
              Matches(rPre, t[..|t| - MaximalSuffixInSet(t, Sigma2)]) &&
              Matches(rSuf, t[|t| - MaximalSuffixInSet(t, Sigma2)..]);
          }
        }

        BackAlphabetInAlphabetAll(strs);
        assert Sigma2 <= AlphabetAll(strs);

        forall p | p in Prefixes ensures StringAlphabet(p) <= AlphabetAll(strs) {
          DedupMem(DropBackRuns(strs, Sigma2), p);
          DropBackRunsSound(strs, Sigma2, p);
          var t :| t in strs && p == DropBackRun(t, Sigma2);
          MaximalSuffixInSetBound(t, Sigma2);
          assert p == t[..|t| - MaximalSuffixInSet(t, Sigma2)];
          StringAlphabetPrefix(t, |t| - MaximalSuffixInSet(t, Sigma2));
          StringAlphabetInAlphabetAll(strs, t);
        }
        MembersContainedImpliesAlphabetAll(Prefixes, AlphabetAll(strs));
        assert AlphabetAll(Prefixes) <= AlphabetAll(strs);

        forall c | c in Symbols(r) ensures c in AlphabetAll(strs) {
          if c in Symbols(rSuf) {
            assert c in AlphabetAll(Suffixes);
            assert c in Sigma2;
          } else {
            assert c in Symbols(rPre);
            assert c in Symbols(rPre0);
            assert c in AlphabetAll(Prefixes);
          }
        }
      } else {
        r := InferGroupFallback(strs);
      }
    }
  }

  // Two sequences with the same set of elements have the same AlphabetAll, regardless
  // of order or duplicates - used to bridge InferGroupFallback's sorting wrapper back to
  // its caller-facing `strs` parameter.
  lemma AlphabetAllSubsetByMembership(xs: seq<string>, ys: seq<string>)
    requires forall t :: t in xs ==> t in ys
    ensures AlphabetAll(xs) <= AlphabetAll(ys)
    decreases xs
  {
    if xs == [] {
    } else {
      AlphabetAllSubsetByMembership(xs[1..], ys);
      assert xs[0] in ys;
      StringAlphabetInAlphabetAll(ys, xs[0]);
    }
  }

  // Reorders strs into canonical sorted order, then runs the actual tier-1/tier-2/tier-3
  // construction (InferGroupFallbackCore, unchanged) on that sorted order.
  //
  // Why this matters: MergeString's greedy, single-pass heuristic can commit to a wrong
  // relative placement when two characters haven't co-occurred yet in any sample it's
  // seen so far. For example, given {"B", "C", "BC"} in that literal order: merging "B"
  // then "C" independently (neither has any established relationship to the other yet)
  // arbitrarily places C before B in the candidate order; by the time "BC" arrives
  // (establishing B-before-C) the order is already committed and conflicts with it,
  // CheckOrderAll correctly rejects the resulting order, and the construction falls
  // through to a much looser fallback (observed: `[CB]+` instead of the correct `B?C?`)
  // - not because B and C can't be told apart (the choice-slot merge logic's
  // CoOccursWithAny check would correctly keep them separate slots, given the chance),
  // but because the chain tier never got a valid order to hand it in the first place.
  // Processing in sorted order avoids this specific failure: sorted, {"B","C","BC"}
  // becomes ["B","BC","C"], and merging "BC" right after "B" establishes B-before-C
  // before "C" alone ever gets a chance to be placed arbitrarily.
  //
  // This is purely a heuristic-quality improvement, not a new correctness mechanism:
  // MergeString carries no correctness burden of its own (the actual soundness gate,
  // CheckOrderAll/CheckSlotsAll/etc., is checked independently inside
  // InferGroupFallbackCore regardless of what order it's fed), so sorting here cannot
  // introduce unsoundness - it can only change which (always-safe) construction gets
  // picked. It does not make the heuristic complete (some order-sensitivity elsewhere in
  // this file's recursive tiers may still exist), but it fixes this concrete case and is
  // a strict, cheap, well-justified improvement everywhere else that feeds
  // InferGroupFallback a batch of strings whose order was an incidental byproduct of
  // some other construction (e.g. Dedup, which preserves first-occurrence order, not a
  // canonical one) rather than the top-level's own already-sorted input.
  method InferGroupFallback(strs: seq<string>) returns (r: Regex)
    requires "" !in strs
    ensures forall t :: t in strs ==> Matches(r, t)
    ensures IsSore(r)
    ensures forall c :: c in Symbols(r) ==> c in AlphabetAll(strs)
  {
    var strsSet := set t | t in strs;
    var sortedStrs := SortedStringSeq(strsSet);

    forall t | t in strs ensures t in sortedStrs {
      assert t in strsSet;
      assert t in multiset(strsSet);
      assert t in multiset(sortedStrs);
    }
    forall t | t in sortedStrs ensures t in strs {
      assert t in multiset(sortedStrs);
      assert t in multiset(strsSet);
      assert t in strsSet;
    }

    assert "" !in sortedStrs;

    r := InferGroupFallbackCore(sortedStrs);

    AlphabetAllSubsetByMembership(sortedStrs, strs);
  }

  // The original tier-1/tier-2/tier-3 construction, unchanged - reached (via the sorting
  // wrapper InferGroupFallback above) whenever tier 0 and the positional split don't
  // apply.
  method InferGroupFallbackCore(strs: seq<string>) returns (r: Regex)
    requires "" !in strs
    ensures forall t :: t in strs ==> Matches(r, t)
    ensures IsSore(r)
    ensures forall c :: c in Symbols(r) ==> c in AlphabetAll(strs)
  {
    var order := MergeAll(strs, []);

    if NoDup(order) && CheckOrderAll(strs, order) {
      MergeAllChars(strs, []);
      assert StringAlphabet([]) == {};
      assert StringAlphabet(MergeAll(strs, [])) <= AlphabetAll(strs);
      assert StringAlphabet(order) <= AlphabetAll(strs);

      // Tier-1 refinement: try the tighter mandatory/repeat/choice-slot construction
      // first (e.g. "abc"/"adc" -> a(?:b|d)c instead of a?b?d?c?); fall back to the
      // already-proven plain ConcatAll(order) if its own independent check fails. The
      // refinement carries no correctness burden of its own beyond CheckSlotsAll
      // passing - same certifying-algorithm pattern as everywhere else in this file.
      var slots := BuildSlots(order, strs);
      if CheckSlotsAll(strs, slots) {
        r := SlotsRegex(slots);

        SlotsRegexSymbols(slots);
        BuildSlotsAtSymbols(order, strs);
        assert Symbols(r) == multiset(order);
        NoDupMultisetBound(order);

        forall t | t in strs ensures Matches(r, t) {
          CheckSlotsAllSound(strs, slots, t);
          FitsSlotsSound(t, slots);
        }

        forall c | c in Symbols(r) ensures c in AlphabetAll(strs) {
          assert c in multiset(order);
          assert c in order;
          StringAlphabetMem(order, c);
        }
      } else {
        r := ConcatAll(order);
        NoDupImpliesSore(order);

        forall t | t in strs ensures Matches(r, t) {
          CheckOrderAllSound(strs, order, t);
          FitsSound(t, order);
        }

        ConcatAllSymbols(order);
        forall c | c in Symbols(r) ensures c in AlphabetAll(strs) {
          assert c in multiset(order);
          assert c in order;
          StringAlphabetMem(order, c);
        }
      }
    } else {
      var p := CandidatePeriod(strs);
      var Sigmas := BuildSigmas(strs, p, 0);

      if p >= 1 && CheckPeriodChoiceAll(strs, p, Sigmas) && SigmasPairwiseDisjoint(Sigmas) {
        r := Plus(BlockPieces(Sigmas));

        BuildSigmasLength(strs, p, 0);
        assert |Sigmas| == p;
        BuildSigmasNoDup(strs, p, 0);
        assert forall j :: 0 <= j < |Sigmas| ==> NoDup(Sigmas[j]);
        PeriodicChoiceIsSore(Sigmas);

        forall t | t in strs ensures Matches(r, t) {
          CheckPeriodChoiceAllSound(strs, p, Sigmas, t);
          assert t != "";
          FitsPeriodChoiceSound(t, p, Sigmas);
        }

        BlockPiecesSymbols(Sigmas);
        forall c | c in Symbols(r) ensures c in AlphabetAll(strs) {
          assert Symbols(r) == SigmasSymbols(Sigmas);
          assert SigmasSymbols(Sigmas)[c] > 0;
          SigmasSymbolsMem(Sigmas, c);
          var j :| 0 <= j < |Sigmas| && c in Sigmas[j];
          BuildSigmasAlphabetAll(strs, p, 0, j, c);
        }
      } else {
        var alpha := AlphabetAll(strs);
        var cs := SortedCharSeq(alpha);
        r := Star(UnionAll(cs));

        UnionAllIsSore(cs);
        StarIsSore(UnionAll(cs));

        forall t | t in strs ensures Matches(r, t) {
          forall i | 0 <= i < |t| ensures t[i] in alpha {
            AlphabetAllSound(strs, t, i);
          }
          UnionStarSound(cs, alpha, t);
        }

        UnionAllSymbolsMultiset(cs);
        forall c | c in Symbols(r) ensures c in AlphabetAll(strs) {
          assert c in multiset(cs);
          assert c in cs;
          SeqSetMembership(cs, alpha, c);
        }
      }
    }
  }

  // ---- Alphabet partitioning ("grouping"): connected components of the co-occurrence
  // relation (two characters are related if some sample string contains both). Solving
  // each component's samples independently and combining the per-component regexes with
  // Union means any wildcard that's still needed only ever spans the minimal alphabet
  // subset that actually requires it, rather than the whole input's alphabet. Unlike the
  // tier-1/tier-2 heuristics, this partitioning is not a "propose then certify" heuristic:
  // connected components are canonical, so the construction is proved correct directly
  // (pairwise-disjoint alphabets, and every sample ends up a member of some group). ----

  // A group pairs an alphabet with the (order-preserving) list of samples assigned to it.
  type Group = (set<char>, seq<string>)

  predicate AllDisjointFrom(alpha: set<char>, groups: seq<Group>)
    decreases groups
  {
    groups == [] || (alpha * groups[0].0 == {} && AllDisjointFrom(alpha, groups[1..]))
  }

  predicate PairwiseDisjoint(groups: seq<Group>)
    decreases groups
  {
    groups == [] || (AllDisjointFrom(groups[0].0, groups[1..]) && PairwiseDisjoint(groups[1..]))
  }

  predicate Contained(groups: seq<Group>)
    decreases groups
  {
    groups == [] ||
    ((forall t :: t in groups[0].1 ==> StringAlphabet(t) <= groups[0].0) && Contained(groups[1..]))
  }

  // No group ever gets "" as a member - MergeOneString leaves groups untouched when
  // C == StringAlphabet(t) == {} (which happens exactly when t == ""), so "" can never
  // be threaded into any mergedMembers list. Needed so InferGroup (which never has to
  // deal with "") can be called on any group's member list.
  predicate NoEmptyMembers(groups: seq<Group>)
    decreases groups
  {
    groups == [] || ((forall t :: t in groups[0].1 ==> t != "") && NoEmptyMembers(groups[1..]))
  }

  function FilterTouching(groups: seq<Group>, C: set<char>): seq<Group>
    decreases groups
  {
    if groups == [] then []
    else if groups[0].0 * C != {} then [groups[0]] + FilterTouching(groups[1..], C)
    else FilterTouching(groups[1..], C)
  }

  function FilterNotTouching(groups: seq<Group>, C: set<char>): seq<Group>
    decreases groups
  {
    if groups == [] then []
    else if groups[0].0 * C == {} then [groups[0]] + FilterNotTouching(groups[1..], C)
    else FilterNotTouching(groups[1..], C)
  }

  function UnionAlphas(groups: seq<Group>): set<char>
    decreases groups
  {
    if groups == [] then {} else groups[0].0 + UnionAlphas(groups[1..])
  }

  function ConcatMembers(groups: seq<Group>): seq<string>
    decreases groups
  {
    if groups == [] then [] else groups[0].1 + ConcatMembers(groups[1..])
  }

  // Absorb t into whichever existing groups its alphabet touches, merging them all
  // (plus t itself) into one new group; groups untouched by t's alphabet are left as-is.
  function MergeOneString(groups: seq<Group>, t: string): seq<Group>
  {
    var C := StringAlphabet(t);
    if C == {} then groups
    else
      var touching := FilterTouching(groups, C);
      var rest := FilterNotTouching(groups, C);
      rest + [(C + UnionAlphas(touching), [t] + ConcatMembers(touching))]
  }

  function BuildGroups(strs: seq<string>, groups: seq<Group>): seq<Group>
    decreases strs
  {
    if strs == [] then groups else BuildGroups(strs[1..], MergeOneString(groups, strs[0]))
  }

  // ---- Filter preserves the two structural invariants ----

  lemma AllDisjointFromFilterPreserved(alpha: set<char>, groups: seq<Group>, C: set<char>)
    requires AllDisjointFrom(alpha, groups)
    ensures AllDisjointFrom(alpha, FilterNotTouching(groups, C))
    ensures AllDisjointFrom(alpha, FilterTouching(groups, C))
    decreases groups
  {
    if groups == [] {
    } else {
      AllDisjointFromFilterPreserved(alpha, groups[1..], C);
    }
  }

  lemma ContainedFilterPreserved(groups: seq<Group>, C: set<char>)
    requires Contained(groups)
    ensures Contained(FilterNotTouching(groups, C))
    ensures Contained(FilterTouching(groups, C))
    decreases groups
  {
    if groups == [] {
    } else {
      ContainedFilterPreserved(groups[1..], C);
    }
  }

  lemma NoEmptyMembersFilterPreserved(groups: seq<Group>, C: set<char>)
    requires NoEmptyMembers(groups)
    ensures NoEmptyMembers(FilterNotTouching(groups, C))
    ensures NoEmptyMembers(FilterTouching(groups, C))
    decreases groups
  {
    if groups == [] {
    } else {
      NoEmptyMembersFilterPreserved(groups[1..], C);
    }
  }

  lemma PairwiseDisjointFilterPreserved(groups: seq<Group>, C: set<char>)
    requires PairwiseDisjoint(groups)
    ensures PairwiseDisjoint(FilterNotTouching(groups, C))
    decreases groups
  {
    if groups == [] {
    } else {
      PairwiseDisjointFilterPreserved(groups[1..], C);
      AllDisjointFromFilterPreserved(groups[0].0, groups[1..], C);
    }
  }

  // ---- Small algebraic helpers on AllDisjointFrom ----

  lemma AllDisjointFromUnion(alpha: set<char>, groups: seq<Group>)
    requires AllDisjointFrom(alpha, groups)
    ensures alpha * UnionAlphas(groups) == {}
    decreases groups
  {
    if groups == [] {
    } else {
      AllDisjointFromUnion(alpha, groups[1..]);
    }
  }

  lemma UnionAlphasDisjointDistributes(a1: set<char>, a2: set<char>, groups: seq<Group>)
    requires AllDisjointFrom(a1, groups)
    requires AllDisjointFrom(a2, groups)
    ensures AllDisjointFrom(a1 + a2, groups)
    decreases groups
  {
    if groups == [] {
    } else {
      UnionAlphasDisjointDistributes(a1, a2, groups[1..]);
    }
  }

  lemma FilterNotTouchingDisjointFromC(groups: seq<Group>, C: set<char>)
    ensures AllDisjointFrom(C, FilterNotTouching(groups, C))
    decreases groups
  {
    if groups == [] {
    } else {
      FilterNotTouchingDisjointFromC(groups[1..], C);
    }
  }

  // The alphabets that end up combined into one merged group (C plus every touching
  // group's alphabet) are disjoint from every group left in `rest` - the crux fact that
  // makes the merge step preserve pairwise-disjointness.
  lemma FilterSplitDisjoint(groups: seq<Group>, C: set<char>)
    requires PairwiseDisjoint(groups)
    ensures AllDisjointFrom(UnionAlphas(FilterTouching(groups, C)), FilterNotTouching(groups, C))
    decreases groups
  {
    if groups == [] {
    } else {
      FilterSplitDisjoint(groups[1..], C);
      if groups[0].0 * C != {} {
        AllDisjointFromFilterPreserved(groups[0].0, groups[1..], C);
        UnionAlphasDisjointDistributes(
          groups[0].0, UnionAlphas(FilterTouching(groups[1..], C)), FilterNotTouching(groups[1..], C));
      } else {
        AllDisjointFromFilterPreserved(groups[0].0, groups[1..], C);
        AllDisjointFromUnion(groups[0].0, FilterTouching(groups[1..], C));
        assert UnionAlphas(FilterTouching(groups[1..], C)) * groups[0].0 == {};
      }
    }
  }

  // ---- Appending one freshly-built group at the end preserves both invariants ----

  lemma AllDisjointFromAppend(alpha: set<char>, groups: seq<Group>, newAlpha: set<char>, newMembers: seq<string>)
    requires AllDisjointFrom(alpha, groups)
    requires alpha * newAlpha == {}
    ensures AllDisjointFrom(alpha, groups + [(newAlpha, newMembers)])
    decreases groups
  {
    if groups == [] {
      assert groups + [(newAlpha, newMembers)] == [(newAlpha, newMembers)];
    } else {
      AllDisjointFromAppend(alpha, groups[1..], newAlpha, newMembers);
      assert (groups + [(newAlpha, newMembers)])[0] == groups[0];
      assert (groups + [(newAlpha, newMembers)])[1..] == groups[1..] + [(newAlpha, newMembers)];
    }
  }

  lemma AppendPreservesPairwiseDisjoint(groups: seq<Group>, newAlpha: set<char>, newMembers: seq<string>)
    requires PairwiseDisjoint(groups)
    requires AllDisjointFrom(newAlpha, groups)
    ensures PairwiseDisjoint(groups + [(newAlpha, newMembers)])
    decreases groups
  {
    if groups == [] {
      assert groups + [(newAlpha, newMembers)] == [(newAlpha, newMembers)];
    } else {
      AppendPreservesPairwiseDisjoint(groups[1..], newAlpha, newMembers);
      AllDisjointFromAppend(groups[0].0, groups[1..], newAlpha, newMembers);
      assert (groups + [(newAlpha, newMembers)])[0] == groups[0];
      assert (groups + [(newAlpha, newMembers)])[1..] == groups[1..] + [(newAlpha, newMembers)];
    }
  }

  lemma AppendPreservesContained(groups: seq<Group>, newAlpha: set<char>, newMembers: seq<string>)
    requires Contained(groups)
    requires forall s :: s in newMembers ==> StringAlphabet(s) <= newAlpha
    ensures Contained(groups + [(newAlpha, newMembers)])
    decreases groups
  {
    if groups == [] {
      assert groups + [(newAlpha, newMembers)] == [(newAlpha, newMembers)];
    } else {
      AppendPreservesContained(groups[1..], newAlpha, newMembers);
      assert (groups + [(newAlpha, newMembers)])[0] == groups[0];
      assert (groups + [(newAlpha, newMembers)])[1..] == groups[1..] + [(newAlpha, newMembers)];
    }
  }

  lemma AppendPreservesNoEmptyMembers(groups: seq<Group>, newAlpha: set<char>, newMembers: seq<string>)
    requires NoEmptyMembers(groups)
    requires forall s :: s in newMembers ==> s != ""
    ensures NoEmptyMembers(groups + [(newAlpha, newMembers)])
    decreases groups
  {
    if groups == [] {
      assert groups + [(newAlpha, newMembers)] == [(newAlpha, newMembers)];
    } else {
      AppendPreservesNoEmptyMembers(groups[1..], newAlpha, newMembers);
      assert (groups + [(newAlpha, newMembers)])[0] == groups[0];
      assert (groups + [(newAlpha, newMembers)])[1..] == groups[1..] + [(newAlpha, newMembers)];
    }
  }

  lemma ConcatMembersAppend(gs1: seq<Group>, gs2: seq<Group>)
    ensures ConcatMembers(gs1 + gs2) == ConcatMembers(gs1) + ConcatMembers(gs2)
    decreases gs1
  {
    if gs1 == [] {
      assert gs1 + gs2 == gs2;
    } else {
      assert (gs1 + gs2)[0] == gs1[0];
      assert (gs1 + gs2)[1..] == gs1[1..] + gs2;
      ConcatMembersAppend(gs1[1..], gs2);
    }
  }

  lemma UnionAlphasAppend(gs1: seq<Group>, gs2: seq<Group>)
    ensures UnionAlphas(gs1 + gs2) == UnionAlphas(gs1) + UnionAlphas(gs2)
    decreases gs1
  {
    if gs1 == [] {
      assert gs1 + gs2 == gs2;
    } else {
      assert (gs1 + gs2)[0] == gs1[0];
      assert (gs1 + gs2)[1..] == gs1[1..] + gs2;
      UnionAlphasAppend(gs1[1..], gs2);
    }
  }

  // ---- Bookkeeping needed for tier 0's recursive call: how UnionAlphas / TotalLength-of-
  // ConcatMembers behave under FilterTouching/FilterNotTouching, MergeOneString and
  // BuildGroups. Each mirrors the shape of the existing Disjoint/Contained/NoEmpty
  // preservation triple, just tracking a different fact. ----

  lemma FilterUnionAlphasSplit(groups: seq<Group>, C: set<char>)
    ensures UnionAlphas(FilterTouching(groups, C)) + UnionAlphas(FilterNotTouching(groups, C)) == UnionAlphas(groups)
    decreases groups
  {
    if groups == [] {
    } else {
      FilterUnionAlphasSplit(groups[1..], C);
    }
  }

  lemma FilterConcatMembersTotalLengthSplit(groups: seq<Group>, C: set<char>)
    ensures TotalLength(ConcatMembers(FilterTouching(groups, C))) + TotalLength(ConcatMembers(FilterNotTouching(groups, C)))
         == TotalLength(ConcatMembers(groups))
    decreases groups
  {
    if groups == [] {
    } else {
      FilterConcatMembersTotalLengthSplit(groups[1..], C);
      assert ConcatMembers(groups) == groups[0].1 + ConcatMembers(groups[1..]);
      TotalLengthAppend(groups[0].1, ConcatMembers(groups[1..]));
      if groups[0].0 * C != {} {
        assert FilterTouching(groups, C) == [groups[0]] + FilterTouching(groups[1..], C);
        assert FilterNotTouching(groups, C) == FilterNotTouching(groups[1..], C);
        ConcatMembersAppend([groups[0]], FilterTouching(groups[1..], C));
        assert ConcatMembers([groups[0]]) == groups[0].1;
        TotalLengthAppend(groups[0].1, ConcatMembers(FilterTouching(groups[1..], C)));
      } else {
        assert FilterTouching(groups, C) == FilterTouching(groups[1..], C);
        assert FilterNotTouching(groups, C) == [groups[0]] + FilterNotTouching(groups[1..], C);
        ConcatMembersAppend([groups[0]], FilterNotTouching(groups[1..], C));
        assert ConcatMembers([groups[0]]) == groups[0].1;
        TotalLengthAppend(groups[0].1, ConcatMembers(FilterNotTouching(groups[1..], C)));
      }
    }
  }

  lemma MergeOneStringAlphaBound(groups: seq<Group>, t: string)
    ensures UnionAlphas(MergeOneString(groups, t)) <= StringAlphabet(t) + UnionAlphas(groups)
  {
    var C := StringAlphabet(t);
    if C == {} {
    } else {
      var touching := FilterTouching(groups, C);
      var rest := FilterNotTouching(groups, C);
      FilterUnionAlphasSplit(groups, C);
      UnionAlphasAppend(rest, [(C + UnionAlphas(touching), [t] + ConcatMembers(touching))]);
      assert UnionAlphas([(C + UnionAlphas(touching), [t] + ConcatMembers(touching))]) == C + UnionAlphas(touching);
    }
  }

  lemma MergeOneStringTotalLength(groups: seq<Group>, t: string)
    ensures TotalLength(ConcatMembers(MergeOneString(groups, t))) == |t| + TotalLength(ConcatMembers(groups))
  {
    var C := StringAlphabet(t);
    if C == {} {
      if t != "" {
        StringAlphabetSound(t, 0);
        assert t[0] in StringAlphabet(t);
      }
      assert t == "";
    } else {
      var touching := FilterTouching(groups, C);
      var rest := FilterNotTouching(groups, C);
      FilterConcatMembersTotalLengthSplit(groups, C);
      ConcatMembersAppend(rest, [(C + UnionAlphas(touching), [t] + ConcatMembers(touching))]);
      assert ConcatMembers([(C + UnionAlphas(touching), [t] + ConcatMembers(touching))]) == [t] + ConcatMembers(touching);
      TotalLengthAppend(ConcatMembers(rest), [t] + ConcatMembers(touching));
      TotalLengthAppend([t], ConcatMembers(touching));
      assert TotalLength([t]) == |t|;
    }
  }

  lemma BuildGroupsAlphaBound(strs: seq<string>, groups: seq<Group>)
    ensures UnionAlphas(BuildGroups(strs, groups)) <= AlphabetAll(strs) + UnionAlphas(groups)
    decreases strs
  {
    if strs == [] {
    } else {
      MergeOneStringAlphaBound(groups, strs[0]);
      BuildGroupsAlphaBound(strs[1..], MergeOneString(groups, strs[0]));
    }
  }

  lemma BuildGroupsTotalLength(strs: seq<string>, groups: seq<Group>)
    ensures TotalLength(ConcatMembers(BuildGroups(strs, groups))) == TotalLength(strs) + TotalLength(ConcatMembers(groups))
    decreases strs
  {
    if strs == [] {
    } else {
      MergeOneStringTotalLength(groups, strs[0]);
      BuildGroupsTotalLength(strs[1..], MergeOneString(groups, strs[0]));
    }
  }

  lemma ContainedImpliesConcatMembersAlphabet(groups: seq<Group>, s: string)
    requires Contained(groups)
    requires s in ConcatMembers(groups)
    ensures StringAlphabet(s) <= UnionAlphas(groups)
    decreases groups
  {
    if s in groups[0].1 {
    } else {
      ContainedImpliesConcatMembersAlphabet(groups[1..], s);
    }
  }

  lemma ContainedNewGroup(touching: seq<Group>, t: string)
    requires Contained(touching)
    ensures forall s :: s in ([t] + ConcatMembers(touching)) ==>
      StringAlphabet(s) <= (StringAlphabet(t) + UnionAlphas(touching))
  {
    forall s | s in ([t] + ConcatMembers(touching))
      ensures StringAlphabet(s) <= (StringAlphabet(t) + UnionAlphas(touching)) {
      if s != t {
        assert s in ConcatMembers(touching);
        ContainedImpliesConcatMembersAlphabet(touching, s);
      }
    }
  }

  lemma NoEmptyMembersImpliesConcatMembers(groups: seq<Group>, s: string)
    requires NoEmptyMembers(groups)
    requires s in ConcatMembers(groups)
    ensures s != ""
    decreases groups
  {
    if s in groups[0].1 {
    } else {
      NoEmptyMembersImpliesConcatMembers(groups[1..], s);
    }
  }

  // ---- One merge step preserves both invariants ----

  lemma MergeOneStringDisjoint(groups: seq<Group>, t: string)
    requires PairwiseDisjoint(groups)
    ensures PairwiseDisjoint(MergeOneString(groups, t))
  {
    var C := StringAlphabet(t);
    if C == {} {
    } else {
      var touching := FilterTouching(groups, C);
      var rest := FilterNotTouching(groups, C);
      FilterSplitDisjoint(groups, C);
      FilterNotTouchingDisjointFromC(groups, C);
      UnionAlphasDisjointDistributes(C, UnionAlphas(touching), rest);
      PairwiseDisjointFilterPreserved(groups, C);
      AppendPreservesPairwiseDisjoint(rest, C + UnionAlphas(touching), [t] + ConcatMembers(touching));
    }
  }

  lemma MergeOneStringContained(groups: seq<Group>, t: string)
    requires Contained(groups)
    ensures Contained(MergeOneString(groups, t))
  {
    var C := StringAlphabet(t);
    if C == {} {
    } else {
      var touching := FilterTouching(groups, C);
      var rest := FilterNotTouching(groups, C);
      ContainedFilterPreserved(groups, C);
      ContainedNewGroup(touching, t);
      AppendPreservesContained(rest, C + UnionAlphas(touching), [t] + ConcatMembers(touching));
    }
  }

  lemma MergeOneStringNoEmpty(groups: seq<Group>, t: string)
    requires NoEmptyMembers(groups)
    ensures NoEmptyMembers(MergeOneString(groups, t))
  {
    var C := StringAlphabet(t);
    if C == {} {
    } else {
      if t == "" {
        assert StringAlphabet(t) == {};
        assert false;
      }
      var touching := FilterTouching(groups, C);
      var rest := FilterNotTouching(groups, C);
      NoEmptyMembersFilterPreserved(groups, C);
      forall s | s in ([t] + ConcatMembers(touching)) ensures s != "" {
        if s != t {
          assert s in ConcatMembers(touching);
          NoEmptyMembersImpliesConcatMembers(touching, s);
        }
      }
      AppendPreservesNoEmptyMembers(rest, C + UnionAlphas(touching), [t] + ConcatMembers(touching));
    }
  }

  // ---- The full fold preserves both invariants, starting from groups == [] ----

  lemma BuildGroupsDisjoint(strs: seq<string>, groups: seq<Group>)
    requires PairwiseDisjoint(groups)
    ensures PairwiseDisjoint(BuildGroups(strs, groups))
    decreases strs
  {
    if strs == [] {
    } else {
      MergeOneStringDisjoint(groups, strs[0]);
      BuildGroupsDisjoint(strs[1..], MergeOneString(groups, strs[0]));
    }
  }

  lemma BuildGroupsContained(strs: seq<string>, groups: seq<Group>)
    requires Contained(groups)
    ensures Contained(BuildGroups(strs, groups))
    decreases strs
  {
    if strs == [] {
    } else {
      MergeOneStringContained(groups, strs[0]);
      BuildGroupsContained(strs[1..], MergeOneString(groups, strs[0]));
    }
  }

  lemma BuildGroupsNoEmpty(strs: seq<string>, groups: seq<Group>)
    requires NoEmptyMembers(groups)
    ensures NoEmptyMembers(BuildGroups(strs, groups))
    decreases strs
  {
    if strs == [] {
    } else {
      MergeOneStringNoEmpty(groups, strs[0]);
      BuildGroupsNoEmpty(strs[1..], MergeOneString(groups, strs[0]));
    }
  }

  // ---- Coverage: every non-empty-alphabet sample ends up a member of some group ----

  lemma MergeOneStringAddsSelf(groups: seq<Group>, t: string)
    requires StringAlphabet(t) != {}
    ensures t in ConcatMembers(MergeOneString(groups, t))
  {
    var C := StringAlphabet(t);
    var touching := FilterTouching(groups, C);
    var rest := FilterNotTouching(groups, C);
    ConcatMembersAppend(rest, [(C + UnionAlphas(touching), [t] + ConcatMembers(touching))]);
  }

  lemma FilterPartitionsConcatMembers(groups: seq<Group>, C: set<char>, t: string)
    requires t in ConcatMembers(groups)
    ensures t in ConcatMembers(FilterTouching(groups, C)) || t in ConcatMembers(FilterNotTouching(groups, C))
    decreases groups
  {
    if t in groups[0].1 {
      if groups[0].0 * C != {} {
        assert ConcatMembers(FilterTouching(groups, C)) ==
          groups[0].1 + ConcatMembers(FilterTouching(groups[1..], C));
      } else {
        assert ConcatMembers(FilterNotTouching(groups, C)) ==
          groups[0].1 + ConcatMembers(FilterNotTouching(groups[1..], C));
      }
    } else {
      assert t in ConcatMembers(groups[1..]);
      FilterPartitionsConcatMembers(groups[1..], C, t);
    }
  }

  lemma MergeOneStringPreservesMembership(groups: seq<Group>, t0: string, t: string)
    requires t in ConcatMembers(groups)
    ensures t in ConcatMembers(MergeOneString(groups, t0))
  {
    var C := StringAlphabet(t0);
    if C == {} {
    } else {
      var touching := FilterTouching(groups, C);
      var rest := FilterNotTouching(groups, C);
      FilterPartitionsConcatMembers(groups, C, t);
      ConcatMembersAppend(rest, [(C + UnionAlphas(touching), [t0] + ConcatMembers(touching))]);
    }
  }

  lemma BuildGroupsCoverage(strs: seq<string>, groups: seq<Group>, t: string)
    requires t in ConcatMembers(groups)
    ensures t in ConcatMembers(BuildGroups(strs, groups))
    decreases strs
  {
    if strs == [] {
    } else {
      MergeOneStringPreservesMembership(groups, strs[0], t);
      BuildGroupsCoverage(strs[1..], MergeOneString(groups, strs[0]), t);
    }
  }

  lemma BuildGroupsAppend(a: seq<string>, b: seq<string>, groups: seq<Group>)
    ensures BuildGroups(a + b, groups) == BuildGroups(b, BuildGroups(a, groups))
    decreases a
  {
    if a == [] {
      assert a + b == b;
    } else {
      assert (a + b)[0] == a[0];
      assert (a + b)[1..] == a[1..] + b;
      BuildGroupsAppend(a[1..], b, MergeOneString(groups, a[0]));
    }
  }

  lemma BuildGroupsCoversAll(strs: seq<string>, t: string)
    requires t in strs
    requires StringAlphabet(t) != {}
    ensures t in ConcatMembers(BuildGroups(strs, []))
  {
    var k :| 0 <= k < |strs| && strs[k] == t;
    assert strs == strs[..k] + ([t] + strs[k + 1..]);
    var G := BuildGroups(strs[..k], []);
    BuildGroupsAppend(strs[..k], [t] + strs[k + 1..], []);
    assert BuildGroups(strs, []) == BuildGroups([t] + strs[k + 1..], G);
    BuildGroupsAppend([t], strs[k + 1..], G);
    assert BuildGroups([t] + strs[k + 1..], G) == BuildGroups(strs[k + 1..], BuildGroups([t], G));
    assert [t][1..] == [];
    assert [t][0] == t;
    assert BuildGroups([t], G) == MergeOneString(G, t);
    assert BuildGroups(strs, []) == BuildGroups(strs[k + 1..], MergeOneString(G, t));
    MergeOneStringAddsSelf(G, t);
    BuildGroupsCoverage(strs[k + 1..], MergeOneString(G, t), t);
  }

  // ---- Combine every group's regex via Union ----

  lemma MembersContainedImpliesAlphabetAll(members: seq<string>, alpha: set<char>)
    requires forall s :: s in members ==> StringAlphabet(s) <= alpha
    ensures AlphabetAll(members) <= alpha
    decreases members
  {
    if members == [] {
    } else {
      MembersContainedImpliesAlphabetAll(members[1..], alpha);
    }
  }

  method InferGroups(groups: seq<Group>) returns (r: Regex)
    requires PairwiseDisjoint(groups)
    requires Contained(groups)
    requires NoEmptyMembers(groups)
    ensures forall t :: t in ConcatMembers(groups) ==> Matches(r, t)
    ensures IsSore(r)
    ensures forall c :: c in Symbols(r) ==> c in UnionAlphas(groups)
    decreases TotalLength(ConcatMembers(groups)), 2, |groups|
  {
    if groups == [] {
      r := Empty;
      EmptyIsSore();
    } else {
      assert "" !in groups[0].1;
      assert ConcatMembers(groups) == groups[0].1 + ConcatMembers(groups[1..]);
      TotalLengthAppend(groups[0].1, ConcatMembers(groups[1..]));
      assert TotalLength(ConcatMembers(groups)) == TotalLength(groups[0].1) + TotalLength(ConcatMembers(groups[1..]));
      var rFirst := InferGroup(groups[0].1);
      var rRest := InferGroups(groups[1..]);

      MembersContainedImpliesAlphabetAll(groups[0].1, groups[0].0);
      AllDisjointFromUnion(groups[0].0, groups[1..]);

      forall c | c in Symbols(rFirst) ensures c !in Symbols(rRest) {
        assert c in AlphabetAll(groups[0].1);
        assert c in groups[0].0;
        if c in Symbols(rRest) {
          assert c in UnionAlphas(groups[1..]);
          assert c in groups[0].0 * UnionAlphas(groups[1..]);
          assert false;
        }
      }

      SymbolsDisjointIsSore(rFirst, rRest);
      r := Union(rFirst, rRest);

      forall t | t in ConcatMembers(groups) ensures Matches(r, t) {
        assert ConcatMembers(groups) == groups[0].1 + ConcatMembers(groups[1..]);
      }

      forall c | c in Symbols(r) ensures c in UnionAlphas(groups) {
        assert UnionAlphas(groups) == groups[0].0 + UnionAlphas(groups[1..]);
      }
    }
  }

  // ---- Top-level inference ----

  method Infer(S: set<string>) returns (r: Regex)
    ensures forall t :: t in S ==> Matches(r, t)
    ensures IsSore(r)
  {
    var S' := S - {""};
    var strs := SortedStringSeq(S');
    assert "" !in strs by { SeqSetMembership(strs, S', ""); }

    var groups := BuildGroups(strs, []);
    BuildGroupsDisjoint(strs, []);
    BuildGroupsContained(strs, []);
    BuildGroupsNoEmpty(strs, []);
    var base := InferGroups(groups);

    if "" in S {
      r := Opt(base);
      OptIsSore(base);
    } else {
      r := base;
    }

    forall t | t in S ensures Matches(r, t) {
      if t == "" {
        OptSoundEps(base);
      } else {
        assert t in S';
        SeqSetMembership(strs, S', t);
        assert t in strs;
        assert StringAlphabet(t) != {} by { StringAlphabetSound(t, 0); }
        BuildGroupsCoversAll(strs, t);
        assert t in ConcatMembers(groups);
        if "" in S {
          OptSound(base, t);
        }
      }
    }
  }
}
