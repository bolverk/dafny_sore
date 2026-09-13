// "Chain" machinery: given a candidate order of distinct symbols, decide whether a
// string "fits" that order (i.e. is a concatenation of maximal runs of each symbol,
// in that order, some runs possibly empty via the surrounding Opt), and build the
// corresponding single-occurrence regex.
include "Regex.dfy"

module Chain {
  import opened RegexCore

  // Length of the maximal run of c at the front of t.
  function RunLength(t: string, c: char): nat
    decreases |t|
  {
    if t == "" || t[0] != c then 0
    else 1 + RunLength(t[1..], c)
  }

  lemma RunLengthBound(t: string, c: char)
    ensures RunLength(t, c) <= |t|
  {
  }

  // The string consisting of c repeated k times.
  function Repeat(c: char, k: nat): string
    decreases k
  {
    if k == 0 then "" else [c] + Repeat(c, k - 1)
  }

  lemma RepeatLength(c: char, k: nat)
    ensures |Repeat(c, k)| == k
  {
  }

  // The leading run of t on symbol c is exactly Repeat(c, RunLength(t,c)), and the
  // remainder is what's left after stripping it.
  lemma RunLengthSplit(t: string, c: char)
    ensures var m := RunLength(t, c);
            m <= |t| && t[..m] == Repeat(c, m)
    decreases |t|
  {
    var m := RunLength(t, c);
    if t == "" || t[0] != c {
      assert m == 0;
      assert t[..0] == "" == Repeat(c, 0);
    } else {
      RunLengthSplit(t[1..], c);
      var m' := RunLength(t[1..], c);
      assert m == 1 + m';
      assert t[..m] == [t[0]] + t[1..][..m'];
      assert t[1..][..m'] == Repeat(c, m');
      assert Repeat(c, m) == [c] + Repeat(c, m');
    }
  }

  // Star(Sym(c)) matches any repeat-string of c.
  lemma StarSymMatchesRepeat(c: char, k: nat)
    ensures Matches(Star(Sym(c)), Repeat(c, k))
    decreases k
  {
    if k == 0 {
      assert Repeat(c, 0) == "";
    } else {
      StarSymMatchesRepeat(c, k - 1);
      var s := Repeat(c, k);
      assert s == [c] + Repeat(c, k - 1);
      assert s[..1] == [c];
      assert s[1..] == Repeat(c, k - 1);
      assert Matches(Sym(c), s[..1]);
      assert Matches(Star(Sym(c)), s[1..]);
      assert 0 < 1 <= |s|;
    }
  }

  // A single repeated-k-times (k >= 1) string is matched by Plus(Sym(c)). Extracted out
  // of OptPlusSymMatchesRepeat's k > 0 case so the "mandatory + repeats" Slot case (see
  // FitsSlotsSound below) can reuse it directly without going through Opt.
  lemma PlusSymMatchesRepeat(c: char, k: nat)
    requires k >= 1
    ensures Matches(Plus(Sym(c)), Repeat(c, k))
  {
    StarSymMatchesRepeat(c, k - 1);
    var s := Repeat(c, k);
    assert s == [c] + Repeat(c, k - 1);
    assert s[..1] == [c];
    assert s[1..] == Repeat(c, k - 1);
    assert Matches(Sym(c), s[..1]);
    assert Matches(Star(Sym(c)), s[1..]);
    assert Matches(Plus(Sym(c)), s) by {
      assert 0 < 1 <= |s| && Matches(Sym(c), s[..1]) && Matches(Star(Sym(c)), s[1..]);
    }
  }

  // Opt(Plus(Sym(c))) matches any repeat-string of c, including the empty one.
  lemma OptPlusSymMatchesRepeat(c: char, k: nat)
    ensures Matches(Opt(Plus(Sym(c))), Repeat(c, k))
  {
    if k == 0 {
      OptSoundEps(Plus(Sym(c)));
    } else {
      PlusSymMatchesRepeat(c, k);
      OptSound(Plus(Sym(c)), Repeat(c, k));
    }
  }

  // A string t "fits" an order of (distinct) symbols if it is exactly the
  // concatenation, in that order, of a (possibly empty) run of each symbol.
  function Fits(t: string, order: seq<char>): bool
    decreases order
  {
    if order == [] then t == ""
    else
      var c := order[0];
      var m := RunLength(t, c);
      assert m <= |t| by { RunLengthBound(t, c); }
      Fits(t[m..], order[1..])
  }

  lemma FitsEmpty(order: seq<char>)
    ensures Fits("", order)
    decreases order
  {
    if order == [] {
    } else {
      assert RunLength("", order[0]) == 0;
      FitsEmpty(order[1..]);
    }
  }

  // The single-occurrence regex Opt(c1+) Opt(c2+) ... Opt(cn+) for order = [c1,...,cn].
  function ConcatAll(order: seq<char>): Regex
    decreases order
  {
    if order == [] then Eps
    else Concat(Opt(Plus(Sym(order[0]))), ConcatAll(order[1..]))
  }

  // Soundness of the chain construction: fitting an order is enough to be matched by
  // the regex built from that order. This lemma is entirely self-contained - it makes
  // no assumption about how `order` was produced.
  lemma FitsSound(t: string, order: seq<char>)
    requires Fits(t, order)
    ensures Matches(ConcatAll(order), t)
    decreases order
  {
    if order == [] {
      assert t == "";
    } else {
      var c := order[0];
      var m := RunLength(t, c);
      RunLengthSplit(t, c);
      assert m <= |t| && t[..m] == Repeat(c, m);
      OptPlusSymMatchesRepeat(c, m);
      assert Matches(Opt(Plus(Sym(c))), t[..m]);
      FitsSound(t[m..], order[1..]);
      assert Matches(ConcatAll(order[1..]), t[m..]);
      assert Matches(ConcatAll(order), t) by {
        assert 0 <= m <= |t| && Matches(Opt(Plus(Sym(c))), t[..m]) && Matches(ConcatAll(order[1..]), t[m..]);
      }
    }
  }

  // ---- No-duplicate order builds a single-occurrence regex ----

  function NoDup(order: seq<char>): bool {
    forall i, j :: 0 <= i < |order| && 0 <= j < |order| && i != j ==> order[i] != order[j]
  }

  lemma ConcatAllSymbols(order: seq<char>)
    ensures Symbols(ConcatAll(order)) == multiset(order)
    decreases order
  {
    if order == [] {
      assert order == [];
      assert multiset(order) == multiset{};
    } else {
      ConcatAllSymbols(order[1..]);
      assert order == [order[0]] + order[1..];
      assert multiset(order) == multiset{order[0]} + multiset(order[1..]);
      assert ConcatAll(order) == Concat(Opt(Plus(Sym(order[0]))), ConcatAll(order[1..]));
      assert Symbols(ConcatAll(order)) ==
        Symbols(Opt(Plus(Sym(order[0])))) + Symbols(ConcatAll(order[1..]));
      assert Symbols(Opt(Plus(Sym(order[0])))) == Symbols(Plus(Sym(order[0])));
      assert Symbols(Plus(Sym(order[0]))) == Symbols(Sym(order[0]));
      assert Symbols(Sym(order[0])) == multiset{order[0]};
    }
  }

  lemma NoDupMultisetBound(order: seq<char>)
    requires NoDup(order)
    ensures forall c :: multiset(order)[c] <= 1
    decreases order
  {
    if order == [] {
    } else {
      var c0 := order[0];
      var rest := order[1..];
      forall i, j | 0 <= i < |rest| && 0 <= j < |rest| && i != j ensures rest[i] != rest[j] {
        assert order[i + 1] == rest[i] && order[j + 1] == rest[j];
      }
      NoDupMultisetBound(rest);
      assert order == [c0] + rest;
      assert multiset(order) == multiset{c0} + multiset(rest);
      if c0 in multiset(rest) {
        var j :| 0 <= j < |rest| && rest[j] == c0;
        assert order[j + 1] == c0 && order[0] == c0;
        assert false;
      }
      assert c0 !in multiset(rest);
      forall c ensures multiset(order)[c] <= 1 {
        assert multiset(order)[c] == multiset{c0}[c] + multiset(rest)[c];
      }
    }
  }

  lemma NoDupImpliesSore(order: seq<char>)
    requires NoDup(order)
    ensures IsSore(ConcatAll(order))
  {
    ConcatAllSymbols(order);
    NoDupMultisetBound(order);
  }

  // ---- Periodic-block machinery (tier 2: "abab" -> (ab)+) ----

  // Literal, non-optional concatenation of exactly these characters in order. Unlike
  // ConcatAll's per-symbol Opt(Plus(Sym(c))), each symbol here appears exactly once with
  // no repetition/optionality wrapper, since within one repetition of a block each
  // symbol occurs exactly once.
  function ConcatLiteral(block: string): Regex
    decreases |block|
  {
    if block == "" then Eps
    else Concat(Sym(block[0]), ConcatLiteral(block[1..]))
  }

  lemma ConcatLiteralMatchesBlock(block: string)
    requires block != ""
    ensures Matches(ConcatLiteral(block), block)
    decreases |block|
  {
    var c := block[0];
    var rest := block[1..];
    assert block == [c] + rest;
    assert block[..1] == [c];
    assert block[1..] == rest;
    if rest == "" {
      assert ConcatLiteral(block) == Concat(Sym(c), ConcatLiteral(rest));
      assert Matches(Sym(c), block[..1]);
      assert Matches(ConcatLiteral(rest), block[1..]);
    } else {
      ConcatLiteralMatchesBlock(rest);
      assert Matches(ConcatLiteral(rest), rest);
      assert Matches(Sym(c), block[..1]);
      assert Matches(ConcatLiteral(rest), block[1..]);
    }
    assert Matches(ConcatLiteral(block), block) by {
      assert 0 <= 1 <= |block| && Matches(Sym(c), block[..1]) && Matches(ConcatLiteral(rest), block[1..]);
    }
  }

  // Plus(r)'s existential witness for s is directly also a witness for Star(r)'s second
  // disjunct: both bodies are syntactically the same existential. (No longer used by
  // the periodic-block tier below, now that it targets a tight RepRange instead of an
  // unbounded Plus/Star - kept as a small general-purpose fact about the two
  // constructors' semantics.)
  lemma PlusImpliesStar(r: Regex, s: string)
    requires Matches(Plus(r), s)
    ensures Matches(Star(r), s)
  {
  }

  lemma ConcatLiteralSymbols(block: string)
    ensures Symbols(ConcatLiteral(block)) == multiset(block)
    decreases |block|
  {
    if block == "" {
      assert multiset(block) == multiset{};
    } else {
      var rest := block[1..];
      ConcatLiteralSymbols(rest);
      assert block == [block[0]] + rest;
      assert multiset(block) == multiset{block[0]} + multiset(rest);
      assert ConcatLiteral(block) == Concat(Sym(block[0]), ConcatLiteral(rest));
      assert Symbols(ConcatLiteral(block)) == Symbols(Sym(block[0])) + Symbols(ConcatLiteral(rest));
      assert Symbols(Sym(block[0])) == multiset{block[0]};
    }
  }

  // ---- Tier 2: periodic block *with a per-position choice*. Generalizes "t is exactly
  // one literal block repeated" (which only ever let every repetition look identical) to
  // "t is exactly p characters repeated, where position i within each repetition is drawn
  // from its own alphabet Sigmas[i]" - e.g. "abab"/"acac" share period 2 with position 0
  // always 'a' and position 1 either 'b' or 'c', giving (?:a(?:b|c)){1,2} instead of a
  // full wildcard. Reduces to the old literal-only behavior exactly when every Sigmas[i]
  // is a singleton. Like everywhere else in this project, the *only* correctness-critical
  // condition is checked explicitly (pairwise disjointness across positions, so each
  // position's choice can be its own Union without breaking single-occurrence) - which
  // period `p` and which alphabets to propose is a pure heuristic with no burden beyond
  // producing *some* candidate.
  //
  // The repeat count is tightly bounded, not unbounded: FitsPeriodChoiceKCopies below
  // establishes that a fitting t decomposes into exactly PeriodRepCount(t, p) copies of
  // the block (MatchesKCopies), which Infer.dfy uses - via MaxKForPeriod's fold over the
  // whole sample batch, and Regex.dfy's MatchesKCopiesImpliesRepRange - to build
  // RepRange(BlockPieces(Sigmas), 1, maxK) instead of the old unbounded
  // Plus(BlockPieces(Sigmas)). ----

  // Build the block-with-choice regex: position i of the (single) repeated unit matches
  // whichever character was proposed for it, drawn from Sigmas[i].
  function BlockPieces(Sigmas: seq<seq<char>>): Regex
    decreases Sigmas
  {
    if Sigmas == [] then Eps else Concat(UnionAll(Sigmas[0]), BlockPieces(Sigmas[1..]))
  }

  // If every one of t's first |Sigmas| characters lies in its respective Sigmas[i],
  // BlockPieces(Sigmas) matches that whole prefix.
  lemma HeadFitsBlockPieces(t: string, Sigmas: seq<seq<char>>)
    requires |t| >= |Sigmas|
    requires forall i :: 0 <= i < |Sigmas| ==> t[i] in Sigmas[i]
    ensures Matches(BlockPieces(Sigmas), t[..|Sigmas|])
    decreases Sigmas
  {
    if Sigmas == [] {
      assert t[..0] == "";
    } else {
      UnionAllSound(Sigmas[0], t[0]);
      assert t[..1] == [t[0]];
      assert Matches(UnionAll(Sigmas[0]), t[..1]);
      forall i | 0 <= i < |Sigmas[1..]| ensures t[1..][i] in Sigmas[1..][i] {
        assert t[1..][i] == t[i + 1];
        assert Sigmas[1..][i] == Sigmas[i + 1];
      }
      HeadFitsBlockPieces(t[1..], Sigmas[1..]);
      assert Matches(BlockPieces(Sigmas[1..]), t[1..][..|Sigmas[1..]|]);
      assert t[1..][..|Sigmas[1..]|] == t[1..|Sigmas|];
      assert t[..|Sigmas|][1..] == t[1..|Sigmas|];
      assert t[..|Sigmas|][..1] == t[..1];
      assert Matches(BlockPieces(Sigmas), t[..|Sigmas|]) by {
        assert 0 <= 1 <= |t[..|Sigmas|]| &&
          Matches(UnionAll(Sigmas[0]), t[..|Sigmas|][..1]) &&
          Matches(BlockPieces(Sigmas[1..]), t[..|Sigmas|][1..]);
      }
    }
  }

  // t is exactly p characters repeated some positive number of times, where the i-th
  // character of EVERY repetition (independently re-checked chunk by chunk, not assumed
  // identical across chunks) is drawn from Sigmas[i]. Note this already forces |t| to be
  // an exact multiple of p - the recursion only ever bottoms out (true) at |t| == p
  // exactly, never at some in-between length - so no separate "|t| % p == 0" or
  // adjacency-equality check is needed alongside it.
  function FitsPeriodChoice(t: string, p: nat, Sigmas: seq<seq<char>>): bool
    decreases |t|
  {
    if p == 0 || |Sigmas| != p || |t| < p then false
    else
      var headOk := forall i :: 0 <= i < p ==> t[i] in Sigmas[i];
      if |t| == p then headOk
      else headOk && FitsPeriodChoice(t[p..], p, Sigmas)
  }

  // Number of period-p repetitions needed to exactly cover t, computed by simple
  // recursive countdown (peel off one block of length p at a time, stop once at most
  // one block's worth remains). Total for any p >= 1 and any t, but only meaningful as
  // "the" repetition count for t's that actually satisfy FitsPeriodChoice(t, p, _): for
  // those, FitsPeriodChoice's own recursion bottoms out at exactly |t| == p (never at
  // some in-between remainder - see the comment on FitsPeriodChoice itself), so this
  // recursion's remaining length is always exactly p at the base case too, and the
  // result is exactly |t| / p (with zero remainder) - though that division fact is never
  // needed as a lemma, since this recursive definition already computes the same count
  // FitsPeriodChoiceKCopies below builds its MatchesKCopies witness around, with no `/`
  // or `%` reasoning anywhere. Used both to state that witness's exact copy-count and,
  // in Infer.dfy, to fold over every sample's own count to find the tightest overall
  // upper bound for RepRange.
  function PeriodRepCount(t: string, p: nat): nat
    requires p >= 1
    decreases |t|
  {
    if |t| <= p then 1 else 1 + PeriodRepCount(t[p..], p)
  }

  // t decomposes into exactly PeriodRepCount(t, p) concatenated copies of
  // BlockPieces(Sigmas)'s language - the bridge to RepRange via
  // MatchesKCopiesImpliesRepRange (Regex.dfy), replacing the old unbounded
  // Matches(Plus(BlockPieces(Sigmas)), t) conclusion this lemma used to prove: the two
  // are equally easy to establish (same induction on |t|, peeling one block off the
  // front each step), but MatchesKCopies additionally exposes the *exact* count, which
  // Plus's own semantics threw away.
  lemma FitsPeriodChoiceKCopies(t: string, p: nat, Sigmas: seq<seq<char>>)
    requires p >= 1 && |Sigmas| == p
    requires FitsPeriodChoice(t, p, Sigmas)
    ensures MatchesKCopies(BlockPieces(Sigmas), t, PeriodRepCount(t, p))
    decreases |t|
  {
    assert |t| >= p;
    assert forall i :: 0 <= i < p ==> t[i] in Sigmas[i];
    HeadFitsBlockPieces(t, Sigmas);
    assert Matches(BlockPieces(Sigmas), t[..p]);
    if |t| == p {
      assert PeriodRepCount(t, p) == 1;
      assert t[..p] == t;
      assert MatchesKCopies(BlockPieces(Sigmas), t, 1) by {
        assert t[p..] == "";
        assert 0 <= p <= |t| && Matches(BlockPieces(Sigmas), t[..p]) && MatchesKCopies(BlockPieces(Sigmas), t[p..], 0);
      }
    } else {
      assert |t| > p;
      var rest := t[p..];
      assert FitsPeriodChoice(rest, p, Sigmas);
      FitsPeriodChoiceKCopies(rest, p, Sigmas);
      assert MatchesKCopies(BlockPieces(Sigmas), rest, PeriodRepCount(rest, p));
      assert PeriodRepCount(t, p) == 1 + PeriodRepCount(rest, p);
      assert MatchesKCopies(BlockPieces(Sigmas), t, PeriodRepCount(t, p)) by {
        assert 0 <= p <= |t| &&
          Matches(BlockPieces(Sigmas), t[..p]) &&
          MatchesKCopies(BlockPieces(Sigmas), t[p..], PeriodRepCount(t, p) - 1);
      }
    }
  }

  function SeqDisjoint(a: seq<char>, b: seq<char>): bool
    decreases a
  {
    a == [] || (a[0] !in b && SeqDisjoint(a[1..], b))
  }

  lemma SeqDisjointMem(a: seq<char>, b: seq<char>, c: char)
    requires SeqDisjoint(a, b)
    requires c in a
    ensures c !in b
    decreases a
  {
    if a[0] == c {
    } else {
      SeqDisjointMem(a[1..], b, c);
    }
  }

  function AllDisjointFromSeq(cs: seq<char>, Sigmas: seq<seq<char>>): bool
    decreases Sigmas
  {
    Sigmas == [] || (SeqDisjoint(cs, Sigmas[0]) && AllDisjointFromSeq(cs, Sigmas[1..]))
  }

  lemma AllDisjointFromSeqMem(cs: seq<char>, Sigmas: seq<seq<char>>, c: char, j: nat)
    requires AllDisjointFromSeq(cs, Sigmas)
    requires c in cs
    requires 0 <= j < |Sigmas|
    ensures c !in Sigmas[j]
    decreases Sigmas
  {
    if j == 0 {
      SeqDisjointMem(cs, Sigmas[0], c);
    } else {
      AllDisjointFromSeqMem(cs, Sigmas[1..], c, j - 1);
    }
  }

  function SigmasPairwiseDisjoint(Sigmas: seq<seq<char>>): bool
    decreases Sigmas
  {
    Sigmas == [] || (AllDisjointFromSeq(Sigmas[0], Sigmas[1..]) && SigmasPairwiseDisjoint(Sigmas[1..]))
  }

  function SigmasSymbols(Sigmas: seq<seq<char>>): multiset<char>
    decreases Sigmas
  {
    if Sigmas == [] then multiset{} else multiset(Sigmas[0]) + SigmasSymbols(Sigmas[1..])
  }

  lemma BlockPiecesSymbols(Sigmas: seq<seq<char>>)
    ensures Symbols(BlockPieces(Sigmas)) == SigmasSymbols(Sigmas)
    decreases Sigmas
  {
    if Sigmas == [] {
    } else {
      UnionAllSymbolsMultiset(Sigmas[0]);
      BlockPiecesSymbols(Sigmas[1..]);
    }
  }

  // Every position individually duplicate-free, and no character shared across two
  // different positions, is exactly what's needed for the combined per-position choices
  // to use every character once overall.
  lemma SigmasNoDupBound(Sigmas: seq<seq<char>>)
    requires forall j :: 0 <= j < |Sigmas| ==> NoDup(Sigmas[j])
    requires SigmasPairwiseDisjoint(Sigmas)
    ensures forall c :: SigmasSymbols(Sigmas)[c] <= 1
    decreases Sigmas
  {
    if Sigmas == [] {
    } else {
      forall j | 0 <= j < |Sigmas[1..]| ensures NoDup(Sigmas[1..][j]) {
        assert Sigmas[1..][j] == Sigmas[j + 1];
      }
      SigmasNoDupBound(Sigmas[1..]);
      NoDupMultisetBound(Sigmas[0]);
      forall c ensures SigmasSymbols(Sigmas)[c] <= 1 {
        assert SigmasSymbols(Sigmas) == multiset(Sigmas[0]) + SigmasSymbols(Sigmas[1..]);
        if c in Sigmas[0] {
          if SigmasSymbols(Sigmas[1..])[c] > 0 {
            SigmasSymbolsMem(Sigmas[1..], c);
            var j :| 0 <= j < |Sigmas[1..]| && c in Sigmas[1..][j];
            AllDisjointFromSeqMem(Sigmas[0], Sigmas[1..], c, j);
            assert false;
          }
        }
      }
    }
  }

  lemma SigmasSymbolsMem(Sigmas: seq<seq<char>>, c: char)
    requires SigmasSymbols(Sigmas)[c] > 0
    ensures exists j :: 0 <= j < |Sigmas| && c in Sigmas[j]
    decreases Sigmas
  {
    if Sigmas == [] {
    } else if c in Sigmas[0] {
      assert c in Sigmas[0];
    } else {
      SigmasSymbolsMem(Sigmas[1..], c);
      var j :| 0 <= j < |Sigmas[1..]| && c in Sigmas[1..][j];
      assert c in Sigmas[j + 1];
    }
  }

  // Note: this establishes IsSore of the *bare* block, not of any repetition wrapper
  // around it - callers now wrap it in RepRange (via Regex.dfy's RepRangeIsSore) rather
  // than the old unbounded Plus, since RepRangeIsSore/PlusIsSore both reduce to exactly
  // this same fact about BlockPieces(Sigmas) itself (repetition wrappers never add or
  // remove symbols - see Symbols's RepRange/Plus cases in Regex.dfy).
  lemma PeriodicChoiceIsSore(Sigmas: seq<seq<char>>)
    requires forall j :: 0 <= j < |Sigmas| ==> NoDup(Sigmas[j])
    requires SigmasPairwiseDisjoint(Sigmas)
    ensures IsSore(BlockPieces(Sigmas))
  {
    BlockPiecesSymbols(Sigmas);
    SigmasNoDupBound(Sigmas);
    assert forall c :: Symbols(BlockPieces(Sigmas))[c] <= 1;
  }

  // ---- Wildcard building block: the union of Sym(c) for c in cs, repeated a tightly
  // bounded number of times (RepRange(UnionAll(cs), 0, maxLen), built in Infer.dfy - see
  // UnionKCopies/MaxLen below) rather than unboundedly (the old Star(UnionAll(cs))): every
  // sample t reaching this tier 3 fallback has some known length |t|, and UnionKCopies
  // shows t decomposes into exactly |t| one-character copies of UnionAll(cs) (via
  // MatchesKCopies), so the longest sample's length - maxLen, folded over the whole batch
  // by MaxLen - is the most repetitions RepRange ever needs to allow. (Moved here from
  // Infer.dfy so the new Slot machinery below - which also needs UnionAll, for choice
  // slots - can use it without a circular include.) ----

  function UnionAll(cs: seq<char>): Regex
    decreases cs
  {
    if cs == [] then Empty
    else if |cs| == 1 then Sym(cs[0])
    else Union(Sym(cs[0]), UnionAll(cs[1..]))
  }

  lemma UnionAllSound(cs: seq<char>, c: char)
    requires c in cs
    ensures Matches(UnionAll(cs), [c])
    decreases cs
  {
    if cs[0] == c {
    } else {
      UnionAllSound(cs[1..], c);
    }
  }

  // Symbols(UnionAll(cs)) is exactly multiset(cs) - mirrors ConcatAllSymbols/
  // ConcatLiteralSymbols's proof shape.
  lemma UnionAllSymbolsMultiset(cs: seq<char>)
    ensures Symbols(UnionAll(cs)) == multiset(cs)
    decreases cs
  {
    if cs == [] {
      assert multiset(cs) == multiset{};
    } else if |cs| == 1 {
      assert multiset(cs) == multiset{cs[0]};
    } else {
      UnionAllSymbolsMultiset(cs[1..]);
      assert cs == [cs[0]] + cs[1..];
      assert multiset(cs) == multiset{cs[0]} + multiset(cs[1..]);
      assert UnionAll(cs) == Union(Sym(cs[0]), UnionAll(cs[1..]));
      assert Symbols(UnionAll(cs)) == Symbols(Sym(cs[0])) + Symbols(UnionAll(cs[1..]));
      assert Symbols(Sym(cs[0])) == multiset{cs[0]};
    }
  }

  lemma UnionAllIsSore(cs: seq<char>)
    requires NoDup(cs)
    ensures IsSore(UnionAll(cs))
  {
    UnionAllSymbolsMultiset(cs);
    NoDupMultisetBound(cs);
  }

  // t decomposes into exactly |t| concatenated one-character copies of UnionAll(cs)'s
  // language - the bridge to RepRange via MatchesKCopiesImpliesRepRange (Regex.dfy),
  // replacing the old unbounded Matches(Star(UnionAll(cs)), t) conclusion this lemma
  // used to prove: the induction is the same character-by-character walk down t (so it
  // was already, in effect, counting |t| repetitions), just restated to expose that
  // exact count instead of discarding it into Star's unbounded semantics.
  lemma UnionKCopies(cs: seq<char>, alpha: set<char>, t: string)
    requires multiset(cs) == multiset(alpha)
    requires forall i :: 0 <= i < |t| ==> t[i] in alpha
    ensures MatchesKCopies(UnionAll(cs), t, |t|)
    decreases |t|
  {
    if t == "" {
    } else {
      assert t[0] in alpha;
      assert t[0] in multiset(alpha) by { assert t[0] in alpha; }
      assert t[0] in multiset(cs);
      assert t[0] in cs;
      UnionAllSound(cs, t[0]);
      assert t[..1] == [t[0]];
      assert Matches(UnionAll(cs), t[..1]);
      forall i | 0 <= i < |t[1..]| ensures t[1..][i] in alpha {
        assert t[1..][i] == t[i + 1];
      }
      UnionKCopies(cs, alpha, t[1..]);
      assert MatchesKCopies(UnionAll(cs), t[1..], |t[1..]|);
      assert MatchesKCopies(UnionAll(cs), t, |t|) by {
        assert 0 <= 1 <= |t| && Matches(UnionAll(cs), t[..1]) && MatchesKCopies(UnionAll(cs), t[1..], |t| - 1);
      }
    }
  }

  // ---- Tight-bound folds: the smallest RepRange upper bound that still covers every
  // sample in a batch, computed directly from that batch (never a universal constant).
  // Used by both tiers above: tier 2's period-block count (PeriodRepCount, per sample)
  // folds to maxK below; tier 3's per-sample length folds to maxLen further below. ----

  function MaxKForPeriod(strs: seq<string>, p: nat): nat
    requires p >= 1
    decreases strs
  {
    if strs == [] then 1
    else
      var restMax := MaxKForPeriod(strs[1..], p);
      var k0 := PeriodRepCount(strs[0], p);
      if k0 > restMax then k0 else restMax
  }

  lemma MaxKForPeriodBound(strs: seq<string>, p: nat, t: string)
    requires p >= 1
    requires t in strs
    ensures PeriodRepCount(t, p) <= MaxKForPeriod(strs, p)
    decreases strs
  {
    if strs[0] == t {
    } else {
      MaxKForPeriodBound(strs[1..], p, t);
    }
  }

  function MaxLen(strs: seq<string>): nat
    decreases strs
  {
    if strs == [] then 0
    else
      var restMax := MaxLen(strs[1..]);
      var m0 := |strs[0]|;
      if m0 > restMax then m0 else restMax
  }

  lemma MaxLenBound(strs: seq<string>, t: string)
    requires t in strs
    ensures |t| <= MaxLen(strs)
    decreases strs
  {
    if strs[0] == t {
    } else {
      MaxLenBound(strs[1..], t);
    }
  }

  // ---- Choice/mandatory-refined chain (Slot machinery): a tighter alternative to
  // ConcatAll, applied per-position along an already-validated `order`. Where ConcatAll
  // treats every position as an independently optional/repeatable symbol, Slots capture
  // two additional, common patterns: a position that's actually mandatory and/or never
  // repeats needs no Opt/Plus wrapper at all, and a run of adjacent positions that are
  // mutually exclusive across every sample (never repeat, never co-occur) collapses into
  // one choice (e.g. "abc"/"adc" -> a(b|d)c instead of a?b?d?c?). Like MergeString/
  // CandidatePeriod, BuildSlots is a pure heuristic: it carries no correctness burden of
  // its own beyond producing *some* slots partitioning `order`'s symbols exactly once
  // each (proved below); actual soundness rests entirely on re-checking FitsSlots against
  // every sample (see CheckSlotsAll in Infer.dfy), exactly the certifying-algorithm
  // pattern used everywhere else in this project. ----

  datatype Slot =
    | SSingle(c: char, mandatory: bool, rep: bool)
    | SChoice(cs: seq<char>, mandatory: bool)

  function SlotRegex(slot: Slot): Regex {
    match slot
    case SSingle(c, mandatory, rep) =>
      var base := if rep then Plus(Sym(c)) else Sym(c);
      if mandatory then base else Opt(base)
    case SChoice(cs, mandatory) =>
      var base := UnionAll(cs);
      if mandatory then base else Opt(base)
  }

  function SlotsRegex(slots: seq<Slot>): Regex
    decreases slots
  {
    if slots == [] then Eps else Concat(SlotRegex(slots[0]), SlotsRegex(slots[1..]))
  }

  // A string t "fits" a slot sequence if, walking the slots left to right, each one
  // consumes a (possibly empty, for non-mandatory slots) prefix run matching its shape:
  // a plain run of one symbol (SSingle) or a run of at most 1 of a set of mutually
  // exclusive symbols (SChoice) - mutual exclusivity between a choice's alternatives is
  // automatic here, since RunLength(t, c) > 0 forces t[0] == c, and t[0] is one specific
  // character, so at most one alternative can ever have a positive run at the same
  // position.
  function FitsSlots(t: string, slots: seq<Slot>): bool
    decreases slots
  {
    if slots == [] then t == ""
    else
      match slots[0]
      case SSingle(c, mandatory, rep) =>
        var m := RunLength(t, c);
        assert m <= |t| by { RunLengthBound(t, c); }
        (!mandatory || m > 0) && (rep || m <= 1) && FitsSlots(t[m..], slots[1..])
      case SChoice(cs, mandatory) =>
        if t != "" && t[0] in cs then
          RunLength(t, t[0]) <= 1 && FitsSlots(t[1..], slots[1..])
        else
          !mandatory && FitsSlots(t, slots[1..])
  }

  lemma FitsSlotsSound(t: string, slots: seq<Slot>)
    requires FitsSlots(t, slots)
    ensures Matches(SlotsRegex(slots), t)
    decreases slots
  {
    if slots == [] {
      assert t == "";
    } else {
      match slots[0]
      case SSingle(c, mandatory, rep) => {
        var m := RunLength(t, c);
        RunLengthSplit(t, c);
        assert m <= |t| && t[..m] == Repeat(c, m);
        FitsSlotsSound(t[m..], slots[1..]);
        assert Matches(SlotsRegex(slots[1..]), t[m..]);
        if rep {
          if mandatory {
            assert m > 0;
            PlusSymMatchesRepeat(c, m);
            assert Matches(Plus(Sym(c)), t[..m]);
          } else {
            OptPlusSymMatchesRepeat(c, m);
            assert Matches(Opt(Plus(Sym(c))), t[..m]);
          }
        } else {
          assert m <= 1;
          if mandatory {
            assert m == 1;
            assert t[..1] == [c];
            assert Matches(Sym(c), t[..m]);
          } else if m == 0 {
            OptSoundEps(Sym(c));
            assert Matches(Opt(Sym(c)), t[..m]);
          } else {
            assert m == 1;
            assert t[..1] == [c];
            OptSound(Sym(c), t[..m]);
          }
        }
        assert Matches(SlotsRegex(slots), t) by {
          assert 0 <= m <= |t| &&
            Matches(SlotRegex(slots[0]), t[..m]) &&
            Matches(SlotsRegex(slots[1..]), t[m..]);
        }
      }
      case SChoice(cs, mandatory) => {
        if t != "" && t[0] in cs {
          FitsSlotsSound(t[1..], slots[1..]);
          assert Matches(SlotsRegex(slots[1..]), t[1..]);
          UnionAllSound(cs, t[0]);
          assert t[..1] == [t[0]];
          assert Matches(UnionAll(cs), t[..1]);
          if !mandatory {
            OptSound(UnionAll(cs), t[..1]);
          }
          assert Matches(SlotsRegex(slots), t) by {
            assert 0 <= 1 <= |t| &&
              Matches(SlotRegex(slots[0]), t[..1]) &&
              Matches(SlotsRegex(slots[1..]), t[1..]);
          }
        } else {
          FitsSlotsSound(t, slots[1..]);
          assert Matches(SlotsRegex(slots[1..]), t[0..]);
          OptSoundEps(UnionAll(cs));
          assert Matches(SlotRegex(slots[0]), "");
          assert Matches(SlotsRegex(slots), t) by {
            assert 0 <= 0 <= |t| &&
              Matches(SlotRegex(slots[0]), t[..0]) &&
              Matches(SlotsRegex(slots[1..]), t[0..]);
          }
        }
      }
    }
  }

  function SlotSymbols(slot: Slot): multiset<char> {
    match slot
    case SSingle(c, _, _) => multiset{c}
    case SChoice(cs, _) => multiset(cs)
  }

  function SlotsSymbols(slots: seq<Slot>): multiset<char>
    decreases slots
  {
    if slots == [] then multiset{} else SlotSymbols(slots[0]) + SlotsSymbols(slots[1..])
  }

  lemma SlotRegexSymbols(slot: Slot)
    ensures Symbols(SlotRegex(slot)) == SlotSymbols(slot)
  {
    match slot
    case SSingle(c, mandatory, rep) => {
      var base := if rep then Plus(Sym(c)) else Sym(c);
      assert SlotRegex(slot) == (if mandatory then base else Opt(base));
      assert Symbols(base) == multiset{c};
      assert Symbols(Opt(base)) == Symbols(base);
    }
    case SChoice(cs, mandatory) => {
      UnionAllSymbolsMultiset(cs);
      var base := UnionAll(cs);
      assert SlotRegex(slot) == (if mandatory then base else Opt(base));
      assert Symbols(Opt(base)) == Symbols(base);
    }
  }

  lemma SlotsRegexSymbols(slots: seq<Slot>)
    ensures Symbols(SlotsRegex(slots)) == SlotsSymbols(slots)
    decreases slots
  {
    if slots == [] {
    } else {
      SlotRegexSymbols(slots[0]);
      SlotsRegexSymbols(slots[1..]);
    }
  }

  // ---- Heuristic slot-builder: partitions an already-validated `order` into
  // contiguous runs, each becoming one Slot. No correctness burden beyond the
  // symbol-preservation fact proved below (BuildSlotsSymbols) - the mandatory/rep/
  // choice-merge decisions themselves are re-checked wholesale by CheckSlotsAll. ----

  // Total count of c anywhere in t (not just its leading run) - unlike RunLength, this
  // needs no stripping/position context, so it's safe to use directly against any
  // sample regardless of how much of it has (or hasn't yet) been stripped by earlier
  // slots. Given NoDup(order) and Fits(t,order), all of c's occurrences in t (if any)
  // form exactly one contiguous run somewhere in t, so "count >= 2 anywhere" is exactly
  // "that run has length >= 2" - the two checks agree, but this one doesn't require c to
  // already be at the front.
  function CountChar(t: string, c: char): nat
    decreases |t|
  {
    if t == "" then 0
    else (if t[0] == c then 1 else 0) + CountChar(t[1..], c)
  }

  function CharRepeatsAnywhere(strs: seq<string>, c: char): bool
    decreases strs
  {
    strs != [] && (CountChar(strs[0], c) >= 2 || CharRepeatsAnywhere(strs[1..], c))
  }

  // Does any character of `run` appear anywhere in t?
  function AnyCharIn(run: seq<char>, t: string): bool
    decreases run
  {
    run != [] && (run[0] in t || AnyCharIn(run[1..], t))
  }

  // Does candidate character c ever appear in the same sample as some character already
  // in `run`? If so, c and run are NOT mutually exclusive and must not be merged into
  // the same choice slot - e.g. for "abc"/"adc", c co-occurs with both b and d in every
  // sample it appears in, so it must stay its own slot rather than join {b,d}'s choice.
  function CoOccursWithAny(strs: seq<string>, c: char, run: seq<char>): bool
    decreases strs
  {
    strs != [] && ((c in strs[0] && AnyCharIn(run, strs[0])) || CoOccursWithAny(strs[1..], c, run))
  }

  function AllMandatorySingle(strs: seq<string>, c: char): bool
    decreases strs
  {
    strs == [] || (RunLength(strs[0], c) > 0 && AllMandatorySingle(strs[1..], c))
  }

  function AllMandatoryChoice(strs: seq<string>, cs: seq<char>): bool
    decreases strs
  {
    strs == [] || ((strs[0] != "" && strs[0][0] in cs) && AllMandatoryChoice(strs[1..], cs))
  }

  // Strip the leading run of whichever of `cs` (if any) is t's own next character - the
  // portion of t this slot consumes, or "" (no-op) if t skips this slot entirely.
  function StripOneSlot(t: string, cs: seq<char>): string {
    if t != "" && t[0] in cs then
      assert RunLength(t, t[0]) <= |t| by { RunLengthBound(t, t[0]); }
      t[RunLength(t, t[0])..]
    else t
  }

  function StripRunChars(strs: seq<string>, cs: seq<char>): seq<string>
    decreases strs
  {
    if strs == [] then [] else [StripOneSlot(strs[0], cs)] + StripRunChars(strs[1..], cs)
  }

  // How many leading elements of `order` form a maximal run of characters that never
  // repeat and are pairwise mutually exclusive across every sample (never co-occur) - a
  // candidate for merging into one SChoice. `runSoFar` accumulates the characters
  // already tentatively accepted into this run, purely to check new candidates against
  // them; `strs` stays fixed throughout (stripped of everything before this run started,
  // but NOT of the run itself, since it isn't finalized yet).
  function ExtendNonRepeatingRun(order: seq<char>, strs: seq<string>, runSoFar: seq<char>): nat
    decreases order
  {
    if order == [] then 0
    else if CharRepeatsAnywhere(strs, order[0]) then 0
    else if CoOccursWithAny(strs, order[0], runSoFar) then 0
    else 1 + ExtendNonRepeatingRun(order[1..], strs, runSoFar + [order[0]])
  }

  lemma ExtendNonRepeatingRunBounds(order: seq<char>, strs: seq<string>, runSoFar: seq<char>)
    ensures 0 <= ExtendNonRepeatingRun(order, strs, runSoFar) <= |order|
    decreases order
  {
    if order == [] {
    } else if CharRepeatsAnywhere(strs, order[0]) {
    } else if CoOccursWithAny(strs, order[0], runSoFar) {
    } else {
      ExtendNonRepeatingRunBounds(order[1..], strs, runSoFar + [order[0]]);
    }
  }

  lemma CoOccursWithAnyEmpty(strs: seq<string>, c: char)
    ensures !CoOccursWithAny(strs, c, [])
    decreases strs
  {
    if strs == [] {
    } else {
      CoOccursWithAnyEmpty(strs[1..], c);
    }
  }

  lemma ExtendNonRepeatingRunPositive(order: seq<char>, strs: seq<string>, runSoFar: seq<char>)
    requires order != []
    requires !CharRepeatsAnywhere(strs, order[0])
    requires !CoOccursWithAny(strs, order[0], runSoFar)
    ensures ExtendNonRepeatingRun(order, strs, runSoFar) >= 1
  {
  }

  function BuildSlotsAt(order: seq<char>, strs: seq<string>): seq<Slot>
    decreases order
  {
    if order == [] then []
    else if CharRepeatsAnywhere(strs, order[0]) then
      var slot := SSingle(order[0], AllMandatorySingle(strs, order[0]), true);
      var strs' := StripRunChars(strs, [order[0]]);
      [slot] + BuildSlotsAt(order[1..], strs')
    else
      var runLen := ExtendNonRepeatingRun(order, strs, []);
      assert 1 <= runLen <= |order| by {
        ExtendNonRepeatingRunBounds(order, strs, []);
        CoOccursWithAnyEmpty(strs, order[0]);
        ExtendNonRepeatingRunPositive(order, strs, []);
      }
      var runChars := order[..runLen];
      var slot :=
        if runLen == 1 then SSingle(order[0], AllMandatorySingle(strs, order[0]), false)
        else SChoice(runChars, AllMandatoryChoice(strs, runChars));
      var strs' := StripRunChars(strs, runChars);
      [slot] + BuildSlotsAt(order[runLen..], strs')
  }

  function BuildSlots(order: seq<char>, strs: seq<string>): seq<Slot> {
    BuildSlotsAt(order, strs)
  }

  lemma BuildSlotsAtSymbols(order: seq<char>, strs: seq<string>)
    ensures SlotsSymbols(BuildSlotsAt(order, strs)) == multiset(order)
    decreases order
  {
    if order == [] {
    } else if CharRepeatsAnywhere(strs, order[0]) {
      var strs' := StripRunChars(strs, [order[0]]);
      BuildSlotsAtSymbols(order[1..], strs');
      assert order == [order[0]] + order[1..];
      assert multiset(order) == multiset{order[0]} + multiset(order[1..]);
    } else {
      ExtendNonRepeatingRunBounds(order, strs, []);
      CoOccursWithAnyEmpty(strs, order[0]);
      ExtendNonRepeatingRunPositive(order, strs, []);
      var runLen := ExtendNonRepeatingRun(order, strs, []);
      var runChars := order[..runLen];
      var strs' := StripRunChars(strs, runChars);
      BuildSlotsAtSymbols(order[runLen..], strs');
      assert order == runChars + order[runLen..];
      assert multiset(order) == multiset(runChars) + multiset(order[runLen..]);
      if runLen == 1 {
        assert runChars == [order[0]];
      }
    }
  }

  // ---- Literal alternation support (tier 0 in Infer.dfy: common-prefix/common-suffix
  // decomposition, e.g. "SABE"/"SXYE" -> S(?:AB|XY)E). Tier 0 is itself recursive (the
  // "middle" regex between the stripped prefix/suffix is built by recursing into
  // InferGroups over there, not by a flat union-of-literals here), so only the two small,
  // still-needed pieces remain in this file: turning a literal block into a
  // single-occurrence regex, and expressing "two strings share no character" via NoDup of
  // their concatenation (so this file never needs Infer.dfy's StringAlphabet). ----

  // Two strings sharing no character, expressed via NoDup of their concatenation: if a
  // character appeared in both, it would occupy two distinct positions in a+b, violating
  // NoDup(a+b).
  lemma NoDupConcatDisjoint(a: string, b: string)
    requires NoDup(a + b)
    ensures forall c :: c in a ==> c !in b
  {
    forall c | c in a && c in b ensures false {
      var i :| 0 <= i < |a| && a[i] == c;
      var k :| 0 <= k < |b| && b[k] == c;
      assert (a + b)[i] == a[i];
      assert (a + b)[|a| + k] == b[k];
      assert i < |a| + k;
      assert 0 <= i < |a + b| && 0 <= |a| + k < |a + b| && i != |a| + k;
    }
  }

  lemma NoDupImpliesConcatLiteralSore(block: string)
    requires NoDup(block)
    ensures IsSore(ConcatLiteral(block))
  {
    ConcatLiteralSymbols(block);
    NoDupMultisetBound(block);
  }
}
