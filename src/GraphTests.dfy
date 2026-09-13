// Executable tests for InferViaBigramGraph (Graph.dfy's BigramGraph module) - the
// standalone, bigram-graph-based alternative to Chain.dfy/Infer.dfy's tiered
// heuristic. This file is intentionally standalone: it imports only Regex.dfy and
// Graph.dfy, never Chain.dfy/Infer.dfy/Tests.dfy, matching the "separate, unrelated
// implementation" stance Graph.dfy's own header comment insists on throughout.
//
// InferViaBigramGraph's own `ensures` clauses are already the soundness
// (forall w in S, Matches(r, w)) and single-occurrence (IsSore(r)) theorems, proved
// statically. These tests exist to sanity-check the executable behavior end to end -
// that it actually runs, terminates, and produces the results its postconditions
// promise - via runtime `expect` checks (not `assert`, which Dafny would try, and
// fail, to prove statically for arbitrary computed data). A small standalone
// executable helper (CountSym/CheckSingleOccurrence, mirroring in spirit - but not
// importing - Tests.dfy's own helpers of the same name for the other implementation)
// checks IsSore at runtime, since IsSore itself quantifies over all of Dafny's (huge)
// `char` domain and so is not directly executable.
include "Regex.dfy"
include "Graph.dfy"

module GraphTests {
  import opened RegexCore
  import opened BigramGraph

  // ---- Small executable helpers for the tests themselves ----

  function CountSym(r: Regex, c: char): nat
    decreases r
  {
    match r
    case Empty => 0
    case Eps => 0
    case Sym(c') => if c == c' then 1 else 0
    case Concat(r1, r2) => CountSym(r1, c) + CountSym(r2, c)
    case Union(r1, r2) => CountSym(r1, c) + CountSym(r2, c)
    case Star(r') => CountSym(r', c)
    case Opt(r') => CountSym(r', c)
    case Plus(r') => CountSym(r', c)
    case RepRange(r', lo, hi) => CountSym(r', c)
  }

  function AllCharsOf(t: string): seq<char>
    decreases |t|
  {
    if t == "" then [] else [t[0]] + AllCharsOf(t[1..])
  }

  method CheckSingleOccurrence(r: Regex, alphabet: seq<char>) returns (ok: bool)
  {
    ok := true;
    var i := 0;
    while i < |alphabet|
      invariant 0 <= i <= |alphabet|
    {
      if CountSym(r, alphabet[i]) > 1 {
        ok := false;
      }
      i := i + 1;
    }
  }

  method CheckAllAccepted(r: Regex, strs: seq<string>) returns (ok: bool)
  {
    ok := true;
    var i := 0;
    while i < |strs|
      invariant 0 <= i <= |strs|
    {
      if !Matches(r, strs[i]) {
        ok := false;
      }
      i := i + 1;
    }
  }

  method SetToSeqOfStrings(S: set<string>) returns (strs: seq<string>)
  {
    strs := [];
    var rem := S;
    while rem != {}
      decreases rem
    {
      var x :| x in rem;
      strs := strs + [x];
      rem := rem - {x};
    }
  }

  method CheckOneSet(S: set<string>, caseName: string) returns (r: Regex)
  {
    r := InferViaBigramGraph(S);

    var strs := SetToSeqOfStrings(S);

    var accepted := CheckAllAccepted(r, strs);
    expect accepted, "InferViaBigramGraph result rejected an input string for case: " + caseName;

    var alphabet: seq<char> := [];
    var j := 0;
    while j < |strs|
      invariant 0 <= j <= |strs|
    {
      alphabet := alphabet + AllCharsOf(strs[j]);
      j := j + 1;
    }
    var sore := CheckSingleOccurrence(r, alphabet);
    expect sore, "InferViaBigramGraph result was not single-occurrence for case: " + caseName;
  }

  // ---- Required example cases ----

  method {:test} TestCatCarCab() {
    var r := CheckOneSet({"cat", "car", "cab"}, "cat/car/cab");
    expect Matches(r, "cat") && Matches(r, "car") && Matches(r, "cab");
  }

  method {:test} TestAbab() {
    var r := CheckOneSet({"abab"}, "abab");
    expect Matches(r, "abab");
  }

  method {:test} TestAbBa() {
    var r := CheckOneSet({"ab", "ba"}, "ab/ba");
    expect Matches(r, "ab") && Matches(r, "ba");
  }

  method {:test} TestEmptySet() {
    var r := CheckOneSet({}, "empty set");
  }

  method {:test} TestEmptyString() {
    var r := CheckOneSet({""}, "empty string");
    expect Matches(r, "");
  }

  // Distinguishes Graph.dfy's Round 10 (exact-overlap merge, tried before the bare/lossy
  // CanMergeAny search) from the behavior it replaces. In this input's bigram graph,
  // 'b' and 'd' have identical predecessor sets ({a}) and identical successor sets
  // ({c}); before Round 10, FindMergePair's unprioritized search could just as easily
  // merge 'a' and 'c' first (also a valid, but structurally arbitrary, CanMergeAny
  // pair), destroying the a-then-c ordering and cascading into a full wildcard over
  // {a,b,c,d} - confirmed empirically to wrongly accept "ac", "abdc", and "abbc". After
  // Round 10, FindExactMergePair fires on 'b'/'d' first, producing an a(b|d)c-shaped
  // result that correctly rejects all three (see Graph.dfy's Round 10 header comment).
  method {:test} TestAbcAdc() {
    var r := CheckOneSet({"abc", "adc"}, "abc/adc");
    expect Matches(r, "abc") && Matches(r, "adc");
    expect !Matches(r, "ac");
    expect !Matches(r, "abdc");
    expect !Matches(r, "abbc");
  }

  // ---- A few more, for extra confidence ----

  method {:test} TestSingleChar() {
    var r := CheckOneSet({"a"}, "single char a");
    expect Matches(r, "a");
  }

  method {:test} TestRepeatedChar() {
    // "aa": forces a self-loop on the 'a' node in the raw bigram graph - exercises the
    // self-loop-canonicalization step of the finishing logic.
    var r := CheckOneSet({"aa"}, "repeated char aa");
    expect Matches(r, "aa");
  }

  method {:test} TestEmptyPlusNonEmpty() {
    // "" alongside non-empty samples - forces a direct start->end bypass edge
    // alongside real structure, exercising the bypass-canonicalization step.
    var r := CheckOneSet({"", "a", "aa"}, "empty plus repeats of a");
    expect Matches(r, "") && Matches(r, "a") && Matches(r, "aa");
  }

  method {:test} TestDisjointAlphabets() {
    var r := CheckOneSet({"ab", "xy"}, "disjoint alphabets ab/xy");
    expect Matches(r, "ab") && Matches(r, "xy");
  }

  method {:test} TestMixedLengthChain() {
    var r := CheckOneSet({"aabbcc", "abc", "aabc", "abbcc"}, "mixed-length chain over a*b*c*");
    expect Matches(r, "aabbcc") && Matches(r, "abc") && Matches(r, "aabc") && Matches(r, "abbcc");
  }

  // Distinguishes Graph.dfy's Round 8 (real, reachability-based SCC detection, tried
  // before the CollapseAll wildcard fallback) from the Round 7 behavior it replaces.
  // "xab"/"xba": x always precedes a genuine 2-cycle between 'a' and 'b' (both a->b and
  // b->a arise, one from each string's ordering), and every pair of the three interior
  // nodes is directly connected by some edge, so the earlier, much more aggressive
  // general OR-merge rule (which fires on any two NON-adjacent nodes) never applies here
  // either - unlike this file's {"abab"} case (whose entire interior IS the cycle,
  // leaving no room to tighten anything), this input's interior has real non-cyclic
  // structure (the leading x) around the cycle for the new SCC step to isolate, letting
  // the rest of the graph keep contracting normally afterwards. Empirically confirmed
  // (see Graph.dfy's Round 8 header comment): before this round, InferViaBigramGraph
  // produced the full wildcard Star(Union(Sym(x),Union(Sym(a),Sym(b)))) - i.e. (x|a|b)*
  // - which wrongly accepts "ax" (x appearing after the cycle instead of before it);
  // after this round it instead produces Concat(Sym(x),Star(Union(Sym(a),Sym(b)))) -
  // i.e. x(a|b)* - which correctly rejects "ax" (and "bx"), a full wildcard's language
  // strictly containing this tighter one's.
  method {:test} TestNontrivialSCCTightening() {
    var r := CheckOneSet({"xab", "xba"}, "xab/xba nontrivial SCC tightening");
    expect Matches(r, "xab") && Matches(r, "xba");
    expect Matches(r, "x") && Matches(r, "xaabb") && Matches(r, "xababab");
    expect !Matches(r, "ax");
    expect !Matches(r, "bx");
  }

  // Distinguishes Graph.dfy's Round 9 (self-loop-to-Plus contraction) from the behavior
  // it replaces. "bb" in "bbx"/"bbyyy" forces a self-loop on the 'b' node; before Round 9
  // that self-loop had no small rule that applied to it, so the driver fell through to
  // CollapseAllGraph and wildcarded the ENTIRE remaining interior (including the
  // completely unrelated 'a'/'x'/'y' nodes) into Star(Union(Union(Union(Sym('a'),Sym('x')),
  // Sym('y')),Sym('b'))) - i.e. [axyb]*, wrongly accepting "a" alone, "x" alone, and "abbx"
  // (mixing 'a' with 'bb'). After Round 9, InferViaBigramGraph produces
  // Concat(Union(Sym('a'),Plus(Sym('b'))),Union(Sym('x'),Plus(Sym('y')))) - i.e.
  // (a|b+)(x|y+) - confirmed empirically (see Graph.dfy's Round 9 header comment) - which
  // still accepts every sample but correctly rejects "a", "x" and "abbx".
  method {:test} TestSelfLoopToPlusTightening() {
    var r := CheckOneSet({"ax", "ayyy", "bbx", "bbyyy"}, "ax/ayyy/bbx/bbyyy self-loop-to-Plus tightening");
    expect Matches(r, "ax");
    expect Matches(r, "bbx");
    expect Matches(r, "ayyy");
    expect Matches(r, "bbyyy");
    expect !Matches(r, "a");
    expect !Matches(r, "x");
    expect !Matches(r, "abbx");
  }

  // Distinguishes Graph.dfy's Round 11 (topological chain-wrap, replacing CollapseAllGraph
  // as the near-final step) from the behavior it replaces. This input's bigram graph has
  // node B with children {C, end} and node C with parents {start, B}; the direct edge
  // B->C blocks MergeAny, C's two parents block simple-path contraction, and there is no
  // LITERAL start->end bypass edge (since "" was never a sample) even though start->C->end
  // provides the same bypass semantically - so every rule through Round 10 got stuck and
  // fell all the way to CollapseAllGraph, producing the full wildcard
  // Star(Union(Sym('B'),Sym('C'))) - i.e. [BC]* - wrongly accepting "CB". After Round 11,
  // InferViaBigramGraph instead produces Concat(Opt(Sym('B')),Concat(Opt(Sym('C')),Eps)) -
  // i.e. B?C? - matching the tight result this project's OTHER, unrelated tiered
  // implementation gets for this same input, and correctly rejecting "CB".
  method {:test} TestBCChainWrapTightening() {
    var r := CheckOneSet({"B", "C", "BC"}, "B/C/BC chain-wrap tightening");
    expect Matches(r, "B") && Matches(r, "C") && Matches(r, "BC");
    expect !Matches(r, "CB");
  }

  // A second Round 11 case, with more structure: this input's bigram graph has no pair of
  // nodes with identical predecessor/successor sets (so FindExactMergePair never applies)
  // and no cycle at all, so before Round 11 it fell through to the demoted FindMergePair/
  // CollapseAllGraph and produced something close to a full wildcard over {A,B,C,D,E}.
  // After Round 11, InferViaBigramGraph produces Concat(Opt(Sym('A')),Concat(Opt(Sym('B')),
  // Concat(Opt(Concat(Sym('C'),Sym('D'))),Concat(Opt(Sym('E')),Eps)))) - i.e. A?B?(CD)?E? -
  // confirmed empirically via a scratch comparison probe (not byte-identical to the OTHER
  // implementation's tighter AB?C?D?E for this same input, which treats A and E as
  // mandatory - this round's chain-wrap always wraps EVERY remaining node in Opt, a known
  // conservative simplification - but still a dramatic tightening versus the wildcard it
  // replaces).
  method {:test} TestAbcdeChainWrapTightening() {
    var r := CheckOneSet({"ABCDE", "ACDE", "ABE"}, "ABCDE/ACDE/ABE chain-wrap tightening");
    expect Matches(r, "ABCDE") && Matches(r, "ACDE") && Matches(r, "ABE");
    expect !Matches(r, "ACBDE");
    expect !Matches(r, "ABCDEX");
    expect !Matches(r, "ABCE");
    expect !Matches(r, "ACDBE");
  }
}
