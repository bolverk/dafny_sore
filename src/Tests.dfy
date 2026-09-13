// Executable tests for Infer: a handful of hardcoded cases plus a small in-Dafny fuzz
// loop, all checked with runtime `expect` (not `assert`, which Dafny would try - and
// fail - to prove statically for arbitrary generated data). The actual theorems
// (soundness, single-occurrence-ness) are already proved statically as Infer's
// `ensures` clauses in Infer.dfy; these tests exist to sanity-check the executable
// behavior (e.g. that Infer actually takes the precise chain path on the cases it's
// meant to, not just the always-safe wildcard fallback) and to fuzz for crashes /
// unexpected disagreement between the matcher and the checked properties.
include "Regex.dfy"
include "Chain.dfy"
include "Infer.dfy"

module Tests {
  import opened RegexCore
  import opened Chain
  import opened SoreInfer

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

  method CheckOneSet(S: set<string>, caseName: string)
  {
    var r := Infer(S);

    var strs: seq<string> := [];
    var rem := S;
    while rem != {}
      decreases rem
    {
      var x :| x in rem;
      strs := strs + [x];
      rem := rem - {x};
    }

    var accepted := CheckAllAccepted(r, strs);
    expect accepted, "Infer result rejected an input string for case: " + caseName;

    var alphabet: seq<char> := [];
    var j := 0;
    while j < |strs|
      invariant 0 <= j <= |strs|
    {
      alphabet := alphabet + AllCharsOf(strs[j]);
      j := j + 1;
    }
    var sore := CheckSingleOccurrence(r, alphabet);
    expect sore, "Infer result was not single-occurrence for case: " + caseName;
  }

  // ---- Hardcoded example cases ----

  method {:test} TestCommonPrefix() {
    CheckOneSet({"cat", "car", "cab"}, "common-prefix cat/car/cab");
    // Distinguish the precise chain path from the always-safe wildcard fallback: a
    // wildcard over {c,a,t,r,b} would happily accept "catcat" (repeats every symbol),
    // but the chain regex built from these samples enforces each symbol's run appears
    // at most once in this relative order, so it must reject "catcat".
    var r := Infer({"cat", "car", "cab"});
    expect !Matches(r, "catcat"), "expected the precise chain regex, not the wildcard fallback";
  }

  method {:test} TestConflictingOrderFallsBackToWildcard() {
    CheckOneSet({"ab", "ba"}, "conflicting order ab/ba");
    // "ab" and "ba" disagree on the relative order of a and b, so no single-occurrence
    // chain can fit both - Infer falls through to tier 2's periodic-block construction,
    // which here degenerates to period p=1 (a trivial one-position "block" whose only
    // choice is the whole alphabet {a,b}), i.e. a bounded (?:[ab]){1,2} rather than an
    // unbounded (?:[ab])+ - so it still accepts strings outside the two original
    // samples, like "aa" (an over-generalization within the observed length bound), but
    // no longer "aabb": both samples are length 2, so maxK=2 and "aabb" would need 4
    // one-character repetitions, past the tight bound.
    var r := Infer({"ab", "ba"});
    expect Matches(r, "aa"), "expected the local wildcard-like fallback to still over-generalize within the observed length bound";
    expect !Matches(r, "aabb"), "expected the tight bound to reject aabb (needs 4 reps, more than any sample's 2)";
  }

  method {:test} TestEmptyAndRepeats() {
    CheckOneSet({"", "a", "aa"}, "empty plus repeats of a");
  }

  method {:test} TestDisjointAlphabets() {
    CheckOneSet({"ab", "xy"}, "disjoint alphabets ab/xy");
  }

  method {:test} TestEmptySetInput() {
    CheckOneSet({}, "empty set of strings");
  }

  method {:test} TestSingleString() {
    CheckOneSet({"hello"}, "single string hello");
  }

  method {:test} TestNonConsecutiveRepeat() {
    // "abab" repeats 'a' and 'b' non-consecutively, so tier 1 (the per-symbol chain)
    // can't fit it - but it IS a periodic block ("ab" repeated), so tier 2 should catch
    // it and produce (ab){1,2} - the single sample "abab" has exactly 2 repetitions of
    // "ab" (maxK = 4/2 = 2), so that's the tightest bound that still accepts it, not the
    // old unbounded (ab)+.
    CheckOneSet({"abab"}, "periodic block abab = (ab){1,2}");
    var r := Infer({"abab"});
    expect Matches(r, "ab"), "(ab){1,2} should still accept a single repetition, within the tight bound";
    expect !Matches(r, "ababab"), "expected the tight bound to reject a 3rd repetition, more than any sample ever showed";
    expect !Matches(r, "aabb"), "expected the precise block regex, not the wildcard fallback";
    expect !Matches(r, "ba"), "expected the block regex to reject a wrong-phase rotation";
    expect !Matches(r, "aba"), "expected the block regex to reject an incomplete trailing block";
  }

  method {:test} TestMultipleSamplesSameBlock() {
    // Several samples that are all powers of the same block "ab": should still take the
    // tier-2 block path, not the wildcard. The longest sample, "ababab", has 3
    // repetitions, so maxK=3 - tight enough to accept every sample but reject a 4th
    // repetition nothing in the input ever showed.
    CheckOneSet({"ab", "abab", "ababab"}, "multiple samples, shared block ab");
    var r := Infer({"ab", "abab", "ababab"});
    expect !Matches(r, "aabb"), "expected the precise block regex, not the wildcard fallback";
    expect !Matches(r, "abababab"), "expected the tight bound (maxK=3) to reject a 4th repetition";
  }

  method {:test} TestPeriodicBlockWithChoice() {
    // "abab"/"acac": both periodic with period 2, sharing 'a' at even positions but
    // differing (b vs c) at odd positions. Tier 2 now allows a per-position choice
    // within the repeated block, not just a fixed literal, so this should produce
    // (?:a(?:b|c)){1,2} - both samples have exactly 2 repetitions, so maxK=2 - rather
    // than falling all the way to a full wildcard over {a,b,c}, or the old unbounded
    // (?:a(?:b|c))+.
    CheckOneSet({"abab", "acac"}, "periodic block with internal choice: abab/acac");
    var r := Infer({"abab", "acac"});
    expect Matches(r, "abab"), "expected abab to still be accepted";
    expect Matches(r, "acac"), "expected acac to still be accepted";
    expect Matches(r, "abac"), "expected mixing the two alternatives across the 2 observed repetitions to be accepted";
    expect !Matches(r, "ababac"), "expected the tight bound (maxK=2) to reject a 3rd repetition";
    expect !Matches(r, "bb"), "expected the block regex to reject a run without the shared 'a'";
    expect !Matches(r, "ca"), "expected the block regex to reject a wrong-phase rotation";
    expect !Matches(r, "aabb"), "expected the precise block regex, not the wildcard fallback";
    expect !Matches(r, "a"), "expected the block regex to reject an incomplete trailing block";
  }

  method {:test} TestPeriodicBlockWithThreeWayChoice() {
    // Same shape as above but with three mutually exclusive alternatives at the varying
    // position: abab/acac/adad -> (?:a(?:b|c|d)){1,2}, since every sample has exactly 2
    // repetitions (maxK=2).
    CheckOneSet({"abab", "acac", "adad"}, "periodic block with three-way internal choice");
    var r := Infer({"abab", "acac", "adad"});
    expect Matches(r, "abab");
    expect Matches(r, "acac");
    expect Matches(r, "adad");
    expect Matches(r, "abac"), "expected mixing two of the three alternatives across the 2 observed repetitions to be accepted";
    expect !Matches(r, "abacad"), "expected the tight bound (maxK=2) to reject a 3rd repetition";
    expect !Matches(r, "bb"), "expected the block regex to reject a run without the shared 'a'";
    expect !Matches(r, "aabb"), "expected the precise block regex, not the wildcard fallback";
  }

  method {:test} TestConsecutiveRepeatGetsTightChain() {
    // "aab" has 'a' repeating, but consecutively (one run of "aa" then "b") - so it was
    // always tier-1-chain-compatible (order=[a,b]), never actually needing tier 2 or the
    // wildcard. The Slot refinement detects that 'a' repeats but 'b' never does in this
    // one sample, producing a{1,2}b - 'a' bounded by the tightest run actually observed
    // (maxRun=2, from "aab"'s own "aa"), not the old unbounded a+ - so "aabb" (a repeated
    // trailing b) is rejected, and so is a 3rd 'a' (past the tight bound).
    CheckOneSet({"aab"}, "consecutive repeat: aab");
    var r := Infer({"aab"});
    expect Matches(r, "ab"), "expected a{1,2}b to still accept a single a";
    expect !Matches(r, "aaab"), "expected the tight bound (maxRun=2) to reject a 3rd a";
    expect !Matches(r, "aabb"), "expected the tightened chain regex to reject a repeated trailing b";
  }

  method {:test} TestChoiceSlotMergesMutuallyExclusiveAlternatives() {
    // "abc"/"adc": a and c are mandatory and never repeat; b and d never co-occur and
    // exactly one of them is present in every sample, so the Slot refinement should
    // collapse them into one mandatory choice instead of two independent optional slots
    // (which would also wrongly accept "abdc", mixing both).
    CheckOneSet({"abc", "adc"}, "choice slot: abc/adc");
    var r := Infer({"abc", "adc"});
    expect Matches(r, "abc"), "expected abc to still be accepted";
    expect Matches(r, "adc"), "expected adc to still be accepted";
    expect !Matches(r, "abdc"), "expected the choice slot to forbid mixing both alternatives";
    expect !Matches(r, "ac"), "expected the choice slot to be mandatory, not skippable";
    expect !Matches(r, "abbc"), "expected the choice slot to forbid repeating an alternative";
  }

  method {:test} TestThreeWayChoiceSlot() {
    // "cat"/"car"/"cab": c and a are mandatory; t/r/b never co-occur and exactly one is
    // always present, so they should collapse into one mandatory 3-way choice slot.
    CheckOneSet({"cat", "car", "cab"}, "three-way choice slot: cat/car/cab");
    var r := Infer({"cat", "car", "cab"});
    expect Matches(r, "cat");
    expect Matches(r, "car");
    expect Matches(r, "cab");
    expect !Matches(r, "ca"), "expected the choice slot to be mandatory, not skippable";
    expect !Matches(r, "catr"), "expected the choice slot to forbid two alternatives at once";
  }

  method {:test} TestMixedLengthChain() {
    CheckOneSet({"aabbcc", "abc", "aabc", "abbcc"}, "mixed-length chain over a*b*c*");
  }

  method {:test} TestPrefixSuffixLiteralAlternation() {
    // "SABE"/"SXYE": common prefix "S", common suffix "E", and two entirely disjoint
    // two-character middles "AB"/"XY" that are mutually exclusive as whole blocks - tier
    // 0 should produce S(?:AB|XY)E, not decompose per-character (which would wrongly
    // allow mixing pieces of the two alternatives, e.g. "SAYE" or "SXBE").
    CheckOneSet({"SABE", "SXYE"}, "prefix/suffix literal alternation: SABE/SXYE");
    var r := Infer({"SABE", "SXYE"});
    expect Matches(r, "SABE");
    expect Matches(r, "SXYE");
    expect !Matches(r, "SAYE"), "expected no mixing of pieces across the two alternatives";
    expect !Matches(r, "SXBE"), "expected no mixing of pieces across the two alternatives";
    expect !Matches(r, "SABXYE"), "expected only one whole middle block, not both";
    expect !Matches(r, "SE"), "expected the middle block to be mandatory, not skippable";
  }

  method {:test} TestPrefixSuffixThreeWay() {
    CheckOneSet({"SABE", "SXYE", "SPQE"}, "prefix/suffix literal alternation, three-way");
    var r := Infer({"SABE", "SXYE", "SPQE"});
    expect Matches(r, "SABE");
    expect Matches(r, "SXYE");
    expect Matches(r, "SPQE");
    expect !Matches(r, "SAYE"), "expected no mixing of pieces across alternatives";
    expect !Matches(r, "SPYE"), "expected no mixing of pieces across alternatives";
    expect !Matches(r, "SE"), "expected the middle block to be mandatory, not skippable";
  }

  method {:test} TestPrefixSuffixSingleCharMiddles() {
    // Common prefix "SA", common suffix "E", middles "B"/"X" happen to be single
    // characters - tier 0 should still produce a clean result consistent with what
    // tier 1's own choice-slot merging would separately achieve on genuinely
    // single-character cases.
    CheckOneSet({"SABE", "SAXE"}, "prefix/suffix literal alternation, single-char middles");
    var r := Infer({"SABE", "SAXE"});
    expect Matches(r, "SABE");
    expect Matches(r, "SAXE");
    expect !Matches(r, "SAE"), "expected the middle to be mandatory, not skippable";
    expect !Matches(r, "SABXE"), "expected only one alternative, not both";
  }

  method {:test} TestPrefixSuffixOverlappingMiddlesFallsThrough() {
    // "SABE"/"SBAE": middles "AB"/"BA" share the same alphabet {A,B}, so they can't be
    // disjoint whole-block alternatives - tier 0 must reject this and fall through to
    // whatever tier 1/2/3 produces instead; confirm the result is still sound and
    // single-occurrence either way.
    CheckOneSet({"SABE", "SBAE"}, "prefix/suffix literal alternation, overlapping middles");
  }

  method {:test} TestPrefixSuffixRecursesOnMiddles() {
    // "Xreq"/"Xopt1"/"Xopt2": stripping the common prefix "X" leaves middles
    // {"req","opt1","opt2"}, which are NOT all pairwise alphabet-disjoint ("opt1" and
    // "opt2" share {o,p,t}) - so a non-recursive tier 0 would have to give up entirely and
    // fall back to a much looser construction. Tier 0 is recursive, though: it partitions
    // the middles by co-occurrence ({"req"} vs {"opt1","opt2"}), handles "req" directly,
    // and recurses on {"opt1","opt2"} - which itself has a further common prefix "opt" and
    // disjoint single-character tails "1"/"2" - giving (in effect) X(?:req|opt[12]),
    // exactly matching what grex independently produces for this input (see
    // compare_grex.py, which is what originally found this gap).
    CheckOneSet({"Xreq", "Xopt1", "Xopt2"}, "recursive prefix/suffix factoring: Xreq/Xopt1/Xopt2");
    var r := Infer({"Xreq", "Xopt1", "Xopt2"});
    expect !Matches(r, "Xo"), "expected 'opt' to be a required unit, not each of o/p/t independently optional";
    expect !Matches(r, "Xopt3"), "expected only 1/2 to be valid alternatives after 'opt'";
    expect !Matches(r, "Xreqopt1"), "expected 'req' and 'opt1'/'opt2' to be mutually exclusive alternatives";
    expect Matches(r, "Xreq"), "expected the original sample Xreq to still be accepted";
    expect Matches(r, "Xopt1"), "expected the original sample Xopt1 to still be accepted";
    expect Matches(r, "Xopt2"), "expected the original sample Xopt2 to still be accepted";
  }

  method {:test} TestGroupingScopesWildcardToConflictingSymbols() {
    // "ab"/"ba" conflict (no consistent global order for a,b), but "cd" shares no
    // alphabet with either. Before alphabet-partitioning, Infer's single global chain
    // attempt would fail on the whole batch and fall back to one wildcard over the
    // FULL alphabet {a,b,c,d} - which would then wrongly accept "ac" (mixing a symbol
    // from the unrelated {c,d} pair into the {a,b} conflict). With grouping, {a,b} and
    // {c,d} are solved independently and combined via Union, so "ac" must be rejected.
    CheckOneSet({"ab", "ba", "cd"}, "grouped: conflicting ab/ba plus unrelated cd");
    var r := Infer({"ab", "ba", "cd"});

    expect !Matches(r, "ac"), "expected the {a,b} and {c,d} groups not to mix symbols";
    expect !Matches(r, "ad"), "expected the {a,b} and {c,d} groups not to mix symbols";
    expect !Matches(r, "bc"), "expected the {a,b} and {c,d} groups not to mix symbols";
    expect !Matches(r, "bd"), "expected the {a,b} and {c,d} groups not to mix symbols";

    // The {a,b} group still needs its own local wildcard-like fallback (a,b genuinely
    // conflict) - here a degenerate periodic block with period 1, tightly bounded to
    // maxK=2 (both "ab" and "ba" are length 2) - so it accepts combinations "ab"/"ba"
    // alone could never justify, like "aa" (still within the length-2 bound), but no
    // longer "aabb" (length 4, past the tight bound).
    expect Matches(r, "aa"), "expected the {a,b} component to still over-generalize within its tight bound";
    expect !Matches(r, "aabb"), "expected the {a,b} component's tight bound to reject aabb (needs 4 reps, more than any sample's 2)";

    // The {c,d} group has only one sample and no conflict, so it takes the chain path;
    // with the Slot refinement, a single non-repeating sample now yields the exact chain
    // "cd" (no more, no less) rather than the looser c*d*.
    expect Matches(r, "cd"), "expected the {c,d} component to still accept its own sample";
    expect !Matches(r, "ccd"), "expected the {c,d} component to now be exact (no repetition observed)";
  }

  method {:test} TestThreeWayDisjointGroups() {
    // Three totally unrelated pairs, each individually chain-able. Grouping should keep
    // them fully separate: no cross-group symbol should ever appear together.
    CheckOneSet({"ab", "cd", "ef"}, "three disjoint groups ab/cd/ef");
    var r := Infer({"ab", "cd", "ef"});
    expect !Matches(r, "ac"), "expected disjoint groups to stay disjoint";
    expect !Matches(r, "ae"), "expected disjoint groups to stay disjoint";
    expect !Matches(r, "ce"), "expected disjoint groups to stay disjoint";
    expect !Matches(r, "abcdef"), "expected disjoint groups to stay disjoint, not concatenate";
  }

  method {:test} TestTwoConflictingGroupsEachGetOwnWildcard() {
    // Two SEPARATE conflicts over disjoint alphabets: {a,b} conflicts (ab/ba) and,
    // independently, {x,y} conflicts (xy/yx). Each group falls back to its own local
    // wildcard-like fallback (a period-1 periodic block, tightly bounded to maxK=2 since
    // every sample is length 2), but the two must never mix symbols with each other, and
    // neither should accept more repetitions than its own samples ever showed.
    CheckOneSet({"ab", "ba", "xy", "yx"}, "two independent conflicting groups");
    var r := Infer({"ab", "ba", "xy", "yx"});
    expect Matches(r, "aa"), "expected the {a,b} group to still over-generalize within its tight bound";
    expect Matches(r, "xx"), "expected the {x,y} group to still over-generalize within its tight bound";
    expect !Matches(r, "aabb"), "expected the {a,b} group's tight bound (maxK=2) to reject aabb";
    expect !Matches(r, "xxyy"), "expected the {x,y} group's tight bound (maxK=2) to reject xxyy";
    expect !Matches(r, "ax"), "expected the two conflicting groups to stay disjoint";
    expect !Matches(r, "ay"), "expected the two conflicting groups to stay disjoint";
  }

  method {:test} TestPositionalSplitOnIndependentAlternationAxes() {
    // "ax","bx","ay","by": two fully independent alternation axes (a/b, then x/y) at
    // fixed positions. Neither tier 0 (no common literal prefix or suffix across all
    // four - they start with 'a' OR 'b', end with 'x' OR 'y') nor tier 1 (a single linear
    // chain order can't represent two independent axes) can express this; the positional
    // split tier should split at k=1 into {"a","b"} and {"x","y"} and concatenate them,
    // giving something equivalent to [ab][xy] - deterministically, regardless of
    // whatever order the strings happen to get processed in.
    CheckOneSet({"ax", "bx", "ay", "by"}, "independent alternation axes ax/bx/ay/by");
    var r := Infer({"ax", "bx", "ay", "by"});
    expect Matches(r, "ax") && Matches(r, "bx") && Matches(r, "ay") && Matches(r, "by");
    expect !Matches(r, ""), "expected exactly two characters, not the empty string";
    expect !Matches(r, "aa"), "expected the second axis to be mandatory, not skippable";
    expect !Matches(r, "xy"), "expected the first axis to be mandatory, not skippable";
    expect !Matches(r, "aax"), "expected no repetition - each axis chosen exactly once";
    expect !Matches(r, "axy"), "expected exactly two characters, not three";
  }

  method {:test} TestPositionalSplitVariableLength() {
    // Same independent-alternation shape as above, but now the second axis's two
    // alternatives ("x" vs "yy") have DIFFERENT lengths, so the samples no longer share
    // one common total length. The positional split's fixed-PREFIX variant (length p=1)
    // still applies - it never required equal total lengths, only that every sample is
    // longer than p - splitting into {"a","b"} and {"x","yy"}. The second piece then goes
    // through the ordinary machinery on its own: "x" and "yy" don't co-occur in any
    // sample, so they land in separate co-occurrence groups and combine as x|y{1,2} (a
    // tightly bounded repeat of y, to stay single-occurrence while still not spelling out
    // the literal "yy") - not grex's own (non-single-occurrence) "x"/"yy" choice, so this
    // is checked directly against Matches rather than against compare_grex.py.
    CheckOneSet({"ax", "bx", "ayy", "byy"}, "independent axes with variable-length second axis");
    var r := Infer({"ax", "bx", "ayy", "byy"});
    expect Matches(r, "ax") && Matches(r, "bx") && Matches(r, "ayy") && Matches(r, "byy");
    expect !Matches(r, "ayyy"), "expected the tight bound (max y-run=2, from \"ayy\"/\"byy\") to reject a 3rd y";
    expect !Matches(r, "a"), "expected the second axis to be mandatory - neither x nor y";
    expect !Matches(r, "b"), "expected the second axis to be mandatory - neither x nor y";
    expect !Matches(r, "axyy"), "expected exactly one of {x, y+}, not both";
  }

  method {:test} TestPositionalSplitFixedSuffixVariant() {
    // The mirror image: fixed-length SUFFIX ("a"/"b", length 1), variable-length prefix
    // ("x" vs "yy") before it. Exercises the second (suffix-first) variant of the
    // positional split, which the previous two tests never reach (their fixed side is
    // always at the front, found by the prefix variant first).
    CheckOneSet({"xa", "xb", "yya", "yyb"}, "fixed suffix, variable-length prefix");
    var r := Infer({"xa", "xb", "yya", "yyb"});
    expect Matches(r, "xa") && Matches(r, "xb") && Matches(r, "yya") && Matches(r, "yyb");
    expect !Matches(r, "yyya"), "expected the tight bound (max y-run=2, from \"yya\"/\"yyb\") to reject a 3rd y";
    expect !Matches(r, "a"), "expected the first axis to be mandatory - neither x nor y";
    expect !Matches(r, "b"), "expected the first axis to be mandatory - neither x nor y";
    expect !Matches(r, "xyya"), "expected exactly one of {x, y+}, not both";
  }

  method {:test} TestPositionalSplitNeitherSideFixedLength() {
    // The genuinely general case an earlier, fixed-length-based version of this tier
    // could not handle at all: two independent alternation axes where NEITHER side has a
    // shared fixed length - axis 1 is "a" (length 1) vs "bb" (length 2), axis 2 is "x"
    // (length 1) vs "yyy" (length 3). The alphabet-based split still finds it: Sigma1 (the
    // "first characters seen" alphabet) is {a,b}, and every sample's maximal leading run
    // of {a,b}-characters is exactly its own axis-1 value ("a" or "bb"), disjoint from the
    // rest ("x"/"yyy"). grex's own answer for this input ("bb(?:yyy|x)|a(?:yyy|x)", roughly)
    // is itself NOT single-occurrence (b, x, y each appear more than once, spelled out
    // literally) - the true single-occurrence target is (?:a|b{1,2})(?:x|y{1,3}), each
    // repeated piece bounded by the tightest run actually observed - so this is checked
    // directly against Matches, not compare_grex.py.
    CheckOneSet({"ax", "ayyy", "bbx", "bbyyy"}, "neither axis has a fixed length");
    var r := Infer({"ax", "ayyy", "bbx", "bbyyy"});
    expect Matches(r, "ax") && Matches(r, "bbx") && Matches(r, "ayyy") && Matches(r, "bbyyy");
    expect Matches(r, "bx"), "expected b{1,2} to also accept a single b, within the tight bound (max b-run=2)";
    expect !Matches(r, "ayyyy"), "expected the tight bound (max y-run=3, from \"ayyy\"/\"bbyyy\") to reject a 4th y";
    expect !Matches(r, "a"), "expected the second axis to be mandatory - neither x nor y";
    expect !Matches(r, "x"), "expected the first axis to be mandatory - neither a nor b";
    expect !Matches(r, "axyyy"), "expected exactly one of {x, y+}, not both";
    expect !Matches(r, "abbx"), "expected exactly one of {a, b+}, not both";
  }

  method {:test} TestOrderIndependentChoiceSlotMerge() {
    // Regression test for a real bug: InferGroupFallback used to run its chain/choice-
    // slot heuristic on whatever order a recursive construction happened to hand it,
    // rather than a canonical order - and for the literal ordering ["B","C","BC"] (the
    // two single-character samples listed before the one that establishes their
    // relative order), MergeString's greedy heuristic placed C before B with no
    // justification (neither sample alone gives any relative-order evidence), which then
    // conflicted with "BC" once it arrived, made CheckOrderAll fail, and fell through to
    // an overly permissive fallback that wrongly merged B and C into a repeatable choice
    // ([CB]+ or similar) even though they demonstrably co-occur (in "BC") and should stay
    // separate, independently-optional slots in a fixed order (B?C?). The fix sorts the
    // batch of strings before running the heuristic, which this specific case needs to
    // see "BC" early enough to establish B-before-C before "C" alone could be placed
    // arbitrarily.
    CheckOneSet({"B", "C", "BC"}, "minimal order-dependent choice-slot repro");
    var r := Infer({"B", "C", "BC"});
    expect Matches(r, "B") && Matches(r, "C") && Matches(r, "BC");
    expect !Matches(r, "CB"), "B and C are not a free choice - BC establishes a fixed order";
    expect !Matches(r, "BB"), "B must not repeat";
    expect !Matches(r, "CC"), "C must not repeat";
  }

  method {:test} TestOrderIndependentChoiceSlotMergeNested() {
    // The full originally-reported case: A(mandatory) B?(optional) C?(optional)
    // D?(optional) E(mandatory), reached via tier 0 (stripping common prefix "A" and
    // suffix "E") recursing into the alphabet-based split (isolating the {B,C} axis from
    // the {D} axis), which in turn recurses into exactly the {"B","C","BC"} sub-problem
    // above - so this also exercises that the fix helps through nested recursion, not
    // just a single top-level call.
    CheckOneSet({"ABCDE", "ACDE", "ABE"}, "originally reported nested repro");
    var r := Infer({"ABCDE", "ACDE", "ABE"});
    expect Matches(r, "ABCDE") && Matches(r, "ACDE") && Matches(r, "ABE") && Matches(r, "AE");
    expect !Matches(r, "ACBDE"), "C before B is the wrong order";
    expect !Matches(r, "ABCBCDE"), "B and C must not repeat/mix";
  }

  method {:test} TestPlainRepeatedCharTightBound() {
    // "aabbc"/"abbbc": a plain (non-periodic, non-wildcard-fallback) chain - order=[a,b,c]
    // fits every sample via NoDup+CheckOrderAll, so this never reaches tier 2's periodic
    // block (no shared period across the batch) or tier 3's wildcard fallback. It
    // exercises the base chain/Slot machinery's own per-position bound instead: 'a'
    // repeats up to 2 times (from "aabbc"'s leading "aa"), 'b' repeats up to 3 times (from
    // "abbbc"'s "bbb") - two different tight bounds at two different positions in the
    // same order, each computed independently of the other and of any shared block/length.
    CheckOneSet({"aabbc", "abbbc"}, "plain repeated single chars: aabbc/abbbc");
    var r := Infer({"aabbc", "abbbc"});
    expect Matches(r, "aabbc") && Matches(r, "abbbc");
    expect Matches(r, "abc"), "expected a{1,2}b{1,3}c to still accept a single a and single b";
    expect !Matches(r, "aaabbc"), "expected the tight bound (max a-run=2) to reject a 3rd a";
    expect !Matches(r, "abbbbc"), "expected the tight bound (max b-run=3) to reject a 4th b";
  }

  // ---- Small deterministic PRNG + fuzz loop ----

  // A tiny linear congruential generator, entirely in Dafny, so the fuzz loop is
  // reproducible without any external randomness source.
  function NextSeed(seed: nat): nat {
    (seed * 1103515245 + 12345) % 2147483648
  }

  function PickChar(seed: nat): char {
    var alphabet := ['a', 'b', 'c'];
    alphabet[seed % 3]
  }

  method GenRandomString(seed: nat, maxLen: nat) returns (s: string, nextSeed: nat)
  {
    var len := seed % (maxLen + 1);
    s := "";
    var cur := seed;
    var i := 0;
    while i < len
      invariant 0 <= i <= len
    {
      cur := NextSeed(cur);
      s := s + [PickChar(cur)];
      i := i + 1;
    }
    nextSeed := NextSeed(cur + 7);
  }

  method GenRandomSet(seed: nat, maxStrings: nat, maxLen: nat) returns (S: set<string>, nextSeed: nat)
  {
    var count := seed % (maxStrings + 1);
    S := {};
    var cur := seed;
    var i := 0;
    while i < count
      invariant 0 <= i <= count
    {
      var s;
      s, cur := GenRandomString(cur, maxLen);
      S := S + {s};
      i := i + 1;
    }
    nextSeed := NextSeed(cur + 13);
  }

  method {:test} FuzzInfer() {
    var seed := 42;
    var trial := 0;
    var numTrials := 300;
    while trial < numTrials
      invariant 0 <= trial <= numTrials
    {
      var S;
      S, seed := GenRandomSet(seed, 5, 6);

      var r := Infer(S);

      var strs: seq<string> := [];
      var rem := S;
      while rem != {}
        decreases rem
      {
        var x :| x in rem;
        strs := strs + [x];
        rem := rem - {x};
      }

      var accepted := CheckAllAccepted(r, strs);
      expect accepted, "fuzz: Infer result rejected an input string at trial " + Fmt(trial);

      var alphabet: seq<char> := [];
      var j := 0;
      while j < |strs|
        invariant 0 <= j <= |strs|
      {
        alphabet := alphabet + AllCharsOf(strs[j]);
        j := j + 1;
      }
      var sore := CheckSingleOccurrence(r, alphabet);
      expect sore, "fuzz: Infer result was not single-occurrence at trial " + Fmt(trial);

      trial := trial + 1;
    }
  }

  // Fuzz loop biased toward periodic strings (block^k), to get real coverage of tier 2.
  method GenRandomPeriodicString(seed: nat, maxBlockLen: nat, maxReps: nat) returns (s: string, nextSeed: nat)
  {
    var blockLen := seed % (maxBlockLen + 1);
    if blockLen == 0 { blockLen := 1; }
    var reps := (NextSeed(seed)) % (maxReps + 1);

    var block := "";
    var cur := seed;
    var i := 0;
    while i < blockLen
      invariant 0 <= i <= blockLen
    {
      cur := NextSeed(cur);
      block := block + [PickChar(cur)];
      i := i + 1;
    }

    s := "";
    var k := 0;
    while k < reps
      invariant 0 <= k <= reps
    {
      s := s + block;
      k := k + 1;
    }
    nextSeed := NextSeed(cur + 19);
  }

  method GenRandomPeriodicSet(seed: nat, maxStrings: nat, maxBlockLen: nat, maxReps: nat)
    returns (S: set<string>, nextSeed: nat)
  {
    var count := seed % (maxStrings + 1);
    S := {};
    var cur := seed;
    var i := 0;
    while i < count
      invariant 0 <= i <= count
    {
      var s;
      s, cur := GenRandomPeriodicString(cur, maxBlockLen, maxReps);
      S := S + {s};
      i := i + 1;
    }
    nextSeed := NextSeed(cur + 23);
  }

  method {:test} FuzzInferPeriodic() {
    var seed := 1337;
    var trial := 0;
    var numTrials := 300;
    while trial < numTrials
      invariant 0 <= trial <= numTrials
    {
      var S;
      S, seed := GenRandomPeriodicSet(seed, 4, 3, 4);

      var r := Infer(S);

      var strs: seq<string> := [];
      var rem := S;
      while rem != {}
        decreases rem
      {
        var x :| x in rem;
        strs := strs + [x];
        rem := rem - {x};
      }

      var accepted := CheckAllAccepted(r, strs);
      expect accepted, "periodic fuzz: Infer result rejected an input string at trial " + Fmt(trial);

      var alphabet: seq<char> := [];
      var j := 0;
      while j < |strs|
        invariant 0 <= j <= |strs|
      {
        alphabet := alphabet + AllCharsOf(strs[j]);
        j := j + 1;
      }
      var sore := CheckSingleOccurrence(r, alphabet);
      expect sore, "periodic fuzz: Infer result was not single-occurrence at trial " + Fmt(trial);

      trial := trial + 1;
    }
  }

  // ---- Fuzz coverage for the tight RepRange bound itself (tier 2's maxK, tier 3's
  // maxLen), added alongside the switch from unbounded Plus/Star to bounded RepRange.
  // These fuzz the CONSTRUCTIONS directly (BlockPieces/UnionAll + MaxKForPeriod/MaxLen +
  // RepRange), rather than routing through the full multi-tier Infer() pipeline: which
  // tier the full pipeline picks for a given random sample set also depends on tier 0
  // (prefix/suffix) and the positional split, which would make it hard to predict, from
  // the outside, which bound a given trial is even supposed to be exercising. Testing
  // the tier-2/tier-3 constructions directly still gives real coverage of exactly what
  // changed, and for each trial checks both halves the task calls for: (1) soundness -
  // every generated sample is still accepted, and (2) tightness - one MORE repetition
  // than the computed bound allows is genuinely rejected, not just "some bound that
  // happens to work". The tightness probe is airtight by construction, not by luck:
  // BlockPieces(Sigmas) (tier 2) and UnionAll(cs) (tier 3) both consume a fixed, nonzero
  // number of characters per repetition (p and 1 respectively), so MatchesKCopies's own
  // definition forces the repetition count for a string of a given length to be
  // determined by that length alone - meaning a probe one length-unit past the computed
  // bound cannot possibly be reached by any *other*, smaller, in-bounds count either. ----

  // Builds Sigmas of length p, position j drawn from two disjoint characters starting at
  // pool index 2*j (so distinct positions never accidentally share a character), each
  // position getting either just the first of its two characters or both - a coin flip
  // per position - so some trials exercise tier 2's per-position "choice" (like
  // abab/acac) and some exercise the plain single-literal-block case (like plain abab).
  function CharPool(idx: nat): char {
    var alphabet := "abcdefghijklmnopqrstuvwxyz";
    alphabet[idx % 26]
  }

  method BuildRandomSigmas(seed: nat, p: nat) returns (Sigmas: seq<seq<char>>, nextSeed: nat)
    requires p >= 1
    ensures |Sigmas| == p
    ensures forall j :: 0 <= j < |Sigmas| ==> Sigmas[j] != []
  {
    Sigmas := [];
    var cur := seed;
    var j := 0;
    while j < p
      invariant 0 <= j <= p
      invariant |Sigmas| == j
      invariant forall k :: 0 <= k < |Sigmas| ==> Sigmas[k] != []
    {
      cur := NextSeed(cur);
      var c1 := CharPool(2 * j);
      var sigma := if cur % 2 == 0 then [c1, CharPool(2 * j + 1)] else [c1];
      Sigmas := Sigmas + [sigma];
      j := j + 1;
    }
    nextSeed := NextSeed(cur + 41);
  }

  // Builds 1..maxSamples samples, each a concatenation of 1..maxReps repetitions of the
  // p-position block, independently re-choosing (per repetition, per position) which of
  // that position's alternatives to use - exactly the shape FitsPeriodChoice accepts.
  method BuildRandomPeriodicSamples(seed: nat, p: nat, Sigmas: seq<seq<char>>, maxSamples: nat, maxReps: nat)
    returns (strs: seq<string>, nextSeed: nat)
    requires p >= 1
    requires |Sigmas| == p
    requires forall j :: 0 <= j < p ==> Sigmas[j] != []
    requires maxReps >= 1
    requires maxSamples >= 1
  {
    var numSamples := seed % maxSamples + 1;
    strs := [];
    var cur := seed;
    var i := 0;
    while i < numSamples
      invariant 0 <= i <= numSamples
      invariant cur >= 0
    {
      cur := NextSeed(cur);
      var reps := cur % maxReps + 1;
      var s := "";
      var k := 0;
      while k < reps
        invariant 0 <= k <= reps
        invariant cur >= 0
      {
        var j := 0;
        while j < p
          invariant 0 <= j <= p
          invariant cur >= 0
        {
          cur := NextSeed(cur);
          s := s + [Sigmas[j][cur % |Sigmas[j]|]];
          j := j + 1;
        }
        k := k + 1;
      }
      strs := strs + [s];
      i := i + 1;
    }
    nextSeed := NextSeed(cur + 43);
  }

  // `reps` copies of the block, always picking each position's first alternative -
  // always constructible (every Sigmas[j] is nonempty) regardless of which alternatives
  // any particular fuzz trial's samples happened to use.
  method BuildBlockRepeat(Sigmas: seq<seq<char>>, reps: nat) returns (s: string)
    requires forall j :: 0 <= j < |Sigmas| ==> Sigmas[j] != []
  {
    s := "";
    var k := 0;
    while k < reps
      invariant 0 <= k <= reps
    {
      var j := 0;
      while j < |Sigmas|
        invariant 0 <= j <= |Sigmas|
      {
        s := s + [Sigmas[j][0]];
        j := j + 1;
      }
      k := k + 1;
    }
  }

  method {:test} FuzzPeriodicTightBound() {
    var seed := 4242;
    var trial := 0;
    var numTrials := 200;
    while trial < numTrials
      invariant 0 <= trial <= numTrials
    {
      var p := seed % 3 + 1;
      var Sigmas;
      Sigmas, seed := BuildRandomSigmas(seed, p);
      var strs;
      strs, seed := BuildRandomPeriodicSamples(seed, p, Sigmas, 4, 4);

      var maxK := MaxKForPeriod(strs, p);
      var r := RepRange(BlockPieces(Sigmas), 1, maxK);

      var i := 0;
      while i < |strs|
        invariant 0 <= i <= |strs|
      {
        expect Matches(r, strs[i]),
          "periodic tight-bound fuzz: rejected an original sample at trial " + Fmt(trial);
        i := i + 1;
      }

      var probe := BuildBlockRepeat(Sigmas, maxK + 1);
      expect !Matches(r, probe),
        "periodic tight-bound fuzz: bound was looser than necessary (accepted maxK+1 repetitions) at trial " + Fmt(trial);

      trial := trial + 1;
    }
  }

  // Same shape of check for tier 3's wildcard fallback: random strings over a small
  // fixed alphabet, checked against RepRange(UnionAll(cs), 0, MaxLen(strs)) directly.
  method BuildRandomWildcardSamples(seed: nat, alpha: seq<char>, maxSamples: nat, maxLen: nat)
    returns (strs: seq<string>, nextSeed: nat)
    requires alpha != []
  {
    var numSamples := seed % (maxSamples + 1);
    strs := [];
    var cur := seed;
    var i := 0;
    while i < numSamples
      invariant 0 <= i <= numSamples
      invariant cur >= 0
    {
      cur := NextSeed(cur);
      var len := cur % (maxLen + 1);
      var s := "";
      var k := 0;
      while k < len
        invariant 0 <= k <= len
        invariant cur >= 0
      {
        cur := NextSeed(cur);
        s := s + [alpha[cur % |alpha|]];
        k := k + 1;
      }
      strs := strs + [s];
      i := i + 1;
    }
    nextSeed := NextSeed(cur + 47);
  }

  method {:test} FuzzWildcardTightBound() {
    var seed := 9001;
    var trial := 0;
    var numTrials := 200;
    var alpha := ['a', 'b', 'c'];
    while trial < numTrials
      invariant 0 <= trial <= numTrials
    {
      var strs;
      strs, seed := BuildRandomWildcardSamples(seed, alpha, 5, 6);

      var maxLen := MaxLen(strs);
      var r := RepRange(UnionAll(alpha), 0, maxLen);

      var i := 0;
      while i < |strs|
        invariant 0 <= i <= |strs|
      {
        expect Matches(r, strs[i]),
          "wildcard tight-bound fuzz: rejected an original sample at trial " + Fmt(trial);
        i := i + 1;
      }

      // maxLen+1 copies of a single alphabet character: same length argument as
      // BuildBlockRepeat above, specialized to UnionAll's one-character-per-repetition
      // shape - guaranteed past the bound and so guaranteed rejected.
      var probe := Repeat(alpha[0], maxLen + 1);
      expect !Matches(r, probe),
        "wildcard tight-bound fuzz: bound was looser than necessary (accepted maxLen+1 length) at trial " + Fmt(trial);

      trial := trial + 1;
    }
  }

  function Fmt(n: nat): string {
    if n < 10 then [('0' as int + n) as char]
    else Fmt(n / 10) + [('0' as int + n % 10) as char]
  }
}
