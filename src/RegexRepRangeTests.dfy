// Standalone executable tests for the new RepRange constructor added to Regex.dfy this
// round. Nothing in Chain.dfy/Infer.dfy/Graph.dfy constructs a RepRange yet (it's pure
// groundwork for a later effort - see Regex.dfy's own header comment on RepRange), so it
// can't be exercised through either existing inference pipeline; this file constructs
// RepRange values directly and checks Matches/PrettyPrint against them at runtime via
// `expect` (mirroring the style of Tests.dfy/GraphTests.dfy's own {:test} methods).
include "Regex.dfy"
include "Print.dfy"

module RegexRepRangeTests {
  import opened RegexCore
  import opened Print

  // ---- Matches: RepRange(Sym('a'), 2, 4) accepts exactly 2, 3, or 4 a's ----

  method {:test} TestRepRangeBasicCounts() {
    var r := RepRange(Sym('a'), 2, 4);
    expect !Matches(r, ""), "0 a's is below lo=2";
    expect !Matches(r, "a"), "1 a is below lo=2";
    expect Matches(r, "aa"), "2 a's is within [2,4]";
    expect Matches(r, "aaa"), "3 a's is within [2,4]";
    expect Matches(r, "aaaa"), "4 a's is within [2,4]";
    expect !Matches(r, "aaaaa"), "5 a's is above hi=4";
    expect !Matches(r, "b"), "wrong symbol entirely";
    expect !Matches(r, "aab"), "extra trailing junk after enough a's";
  }

  // ---- Matches: the lo > hi empty-range case matches nothing at all ----

  method {:test} TestRepRangeEmptyRangeMatchesNothing() {
    var r := RepRange(Sym('a'), 3, 1);
    expect !Matches(r, "");
    expect !Matches(r, "a");
    expect !Matches(r, "aa");
    expect !Matches(r, "aaa");
    expect !Matches(r, "aaaa");
  }

  // ---- Matches: RepRange(_, 0, 0) matches only the empty string, for any r ----

  method {:test} TestRepRangeZeroZero() {
    var r := RepRange(Sym('a'), 0, 0);
    expect Matches(r, "");
    expect !Matches(r, "a");
    expect !Matches(r, "aa");

    // Also true when the operand itself can't match "" on its own - the count of
    // zero repetitions doesn't depend on what r is.
    var r2 := RepRange(Concat(Sym('x'), Sym('y')), 0, 0);
    expect Matches(r2, "");
    expect !Matches(r2, "xy");
  }

  // ---- Matches: RepRange(r, 1, 1) matches exactly what r matches ----

  method {:test} TestRepRangeOneOne() {
    var r := RepRange(Union(Sym('a'), Sym('b')), 1, 1);
    expect Matches(r, "a");
    expect Matches(r, "b");
    expect !Matches(r, "");
    expect !Matches(r, "ab");
    expect !Matches(r, "aa");
  }

  // ---- Matches: RepRange(r, 0, 1) matches exactly what Opt(r) does ----

  method {:test} TestRepRangeZeroOneMatchesLikeOpt() {
    var r := RepRange(Sym('a'), 0, 1);
    expect Matches(r, "");
    expect Matches(r, "a");
    expect !Matches(r, "aa");
  }

  // ---- Matches: RepRange composed inside a larger regex via Concat ----

  method {:test} TestRepRangeInsideConcat() {
    // x, then between 1 and 2 y's, then z.
    var r := Concat(Sym('x'), Concat(RepRange(Sym('y'), 1, 2), Sym('z')));
    expect Matches(r, "xyz");
    expect Matches(r, "xyyz");
    expect !Matches(r, "xz");
    expect !Matches(r, "xyyyz");
  }

  // ---- Matches: a RepRange whose operand can itself match multiple lengths ----

  method {:test} TestRepRangeOverMultiCharBlock() {
    // Between 2 and 3 repetitions of the 2-character block "ab".
    var r := RepRange(Concat(Sym('a'), Sym('b')), 2, 3);
    expect Matches(r, "abab");
    expect Matches(r, "ababab");
    expect !Matches(r, "ab");
    expect !Matches(r, "abababab");
    expect !Matches(r, "aba");
  }

  // ---- IsSore: RepRange still counts its operand's symbols exactly once ----

  method {:test} TestRepRangeIsSore() {
    var r := RepRange(Concat(Sym('a'), Sym('b')), 2, 4);
    RepRangeIsSore(Concat(Sym('a'), Sym('b')), 2, 4);
    expect IsSore(r);
    expect Symbols(r) == multiset{'a', 'b'};
  }

  // ---- MatchesKCopies / MatchesKCopiesImpliesRepRange: the bridge later rounds use ----

  method {:test} TestMatchesKCopiesBridge() {
    var r := Sym('a');
    // 3 copies of "a" is "aaa".
    expect MatchesKCopies(r, "aaa", 3);
    MatchesKCopiesImpliesRepRange(r, 1, 5, 3, "aaa");
    expect Matches(RepRange(r, 1, 5), "aaa");
  }

  // ---- PrettyPrint: general {lo,hi} form ----

  method {:test} TestPrettyPrintGeneralForm() {
    var r := RepRange(Sym('a'), 2, 4);
    expect PrettyPrint(r) == "a{2,4}";
  }

  // ---- PrettyPrint: {n} shorthand when lo == hi (n > 1) ----

  method {:test} TestPrettyPrintExactCount() {
    var r := RepRange(Sym('a'), 3, 3);
    expect PrettyPrint(r) == "a{3}";
  }

  // ---- PrettyPrint: {0,1} prints as the shorter "?", matching Opt ----

  method {:test} TestPrettyPrintZeroOneAsQuestionMark() {
    var r := RepRange(Sym('a'), 0, 1);
    expect PrettyPrint(r) == "a?";
    expect PrettyPrint(r) == PrettyPrint(Opt(Sym('a')));
  }

  // ---- PrettyPrint: {1,1} prints as just the operand, no suffix at all ----

  method {:test} TestPrettyPrintOneOneIsBare() {
    var r := RepRange(Sym('a'), 1, 1);
    expect PrettyPrint(r) == "a";
  }

  // ---- PrettyPrint: {0,0} prints as the empty string (matches only "") ----

  method {:test} TestPrettyPrintZeroZeroIsEmpty() {
    var r := RepRange(Sym('a'), 0, 0);
    expect PrettyPrint(r) == "";
  }

  // ---- PrettyPrint: an empty [lo,hi] range prints as the same "never matches"
  // marker Empty itself uses ----

  method {:test} TestPrettyPrintEmptyRange() {
    var r := RepRange(Sym('a'), 3, 1);
    expect PrettyPrint(r) == "(?!)";
    expect PrettyPrint(r) == PrettyPrint(Empty);
  }

  // ---- PrettyPrint: a non-atomic operand gets (?:...) wrapped before the {lo,hi} ----

  method {:test} TestPrettyPrintWrapsNonAtomicOperand() {
    var r := RepRange(Concat(Sym('a'), Sym('b')), 2, 4);
    expect PrettyPrint(r) == "(?:ab){2,4}";
  }

  // ---- Simplify: RepRange's degenerate forms collapse the same way Matches treats
  // them (Empty/Eps/bare operand), so a Simplify+PrettyPrint pipeline (as Main.dfy
  // actually runs) prints the same idiomatic forms tested above ----

  method {:test} TestSimplifyCollapsesDegenerateForms() {
    expect Simplify(RepRange(Sym('a'), 3, 1)) == Empty;
    expect Simplify(RepRange(Sym('a'), 0, 0)) == Eps;
    expect Simplify(RepRange(Sym('a'), 1, 1)) == Sym('a');
    expect Simplify(RepRange(Sym('a'), 2, 4)) == RepRange(Sym('a'), 2, 4);
  }
}
