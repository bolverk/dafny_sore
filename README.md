# sore

A Dafny-verified inference of **single-occurrence regular expressions** (SOREs) from
a finite set of sample strings. A SORE is a regular expression in which every alphabet
symbol appears at most once (the notion used in schema inference literature, e.g.
Bex, Neven, Schwentick & Vansummeren). Given `S: set<string>`, `Infer(S)` returns a
`Regex` that is:

- **sound** — it accepts every string in `S`, and
- **single-occurrence** — every character appears at most once in the regex tree,

both proved as Dafny `ensures` clauses, checked by the verifier, not just tested.

`Infer` first **partitions the alphabet into connected components by co-occurrence**
(two characters are related if some sample string contains both), then solves each
component's samples completely independently, then combines the per-component regexes
with `Union` (safe because components have pairwise-disjoint alphabets). This means the
`Star(a1|...|an)` wildcard — used only when a component genuinely can't be expressed any
tighter — is never global: it only ever spans the minimal set of symbols that actually
conflict, never symbols from an unrelated part of the input. For example,
`{"ab", "ba", "cd"}` needs a wildcard for the *conflicting* `{a,b}` pair, but `{c,d}`
(which never co-occurs with `a`/`b` in any sample) is solved separately and combined via
`Union` — so the result correctly rejects `"ac"`, even though a single global wildcard
over `{a,b,c,d}` would have wrongly accepted it. See "Design: alphabet partitioning"
below.

Within each component, `Infer` tries four tiers in order, falling through to the next
only when the previous one's independent checker rejects its candidate (see "Design: a
certifying algorithm" below for what that means):

0. **Prefix/suffix literal alternation, recursively** — when every sample in the
   component shares one common prefix and one common suffix, and neither shares a
   character with what's left over ("the middles"), e.g. `{"SABE","SXYE"}` →
   `S(?:AB|XY)E` rather than decomposing per-character (which would wrongly accept
   `"SAYE"` or `"SXBE"`, mixing pieces of the two alternatives). The middles themselves
   don't need to be immediately mutually exclusive — they're partitioned by
   co-occurrence and each part is solved recursively (which may strip a further shared
   prefix/suffix, or fall through to tiers 1-3), so e.g. `{"Xreq","Xopt1","Xopt2"}` →
   `X(?:req|opt[12])` (`"req"` peels off directly; `{"opt1","opt2"}` recurses once more
   to find the further shared prefix `"opt"` and disjoint tails `"1"`/`"2"`). See
   "Design: tier 0" below.
1. **Chain** — a single order of the component's alphabet, tightened by a second,
   independently-checked refinement: positions that are mandatory and/or never repeat
   drop their `Opt`/`Plus` wrapper, and a run of adjacent positions that never co-occur
   and never repeat collapses into one mandatory choice. E.g. `{"cat","car","cab"}` →
   `ca[trb]` (`c` then `a`, both mandatory-exact, then exactly one of `t`/`r`/`b`) rather
   than the looser `c?a?t?r?b?`-shaped result a plain per-symbol chain would give. See
   "Design: the choice-slot refinement" below. (In practice tiers 0 and 1 often agree on
   simple cases — `{"cat","car","cab"}` and `{"abc","adc"}` both already have a
   common-prefix/common-suffix decomposition, so tier 0 actually handles them; tier 1's
   choice-slot refinement remains the one that fires for chains with mandatory/optional
   structure that isn't just "one shared prefix + one shared suffix", e.g.
   `{"aabbcc","abc","aabc","abbcc"}`.)
2. **Periodic block, with an optional per-position choice** — when the whole component
   is (or reduces to) repetitions of some period `p`, where each of the `p` positions
   *within one repetition* may itself be a choice among several characters, not just a
   fixed literal — e.g. `{"abab"}` → `(ab)+`, `{"ab","abab","ababab"}` → the same `(ab)+`
   (every position's alphabet happens to be a singleton, reducing to the literal case),
   and `{"abab","acac"}` (period 2, position 0 always `a`, position 1 either `b` or `c`)
   → `(?:a(?:b|c))+` rather than a full wildcard over `{a,b,c}`.
3. **Wildcard** — `Star(a1|a2|...|an)` over *that component's* alphabet only, always
   sound and always single-occurrence, used whenever none of the above applies.

## Files

- `src/Regex.dfy` — the `Regex` datatype (`Empty | Eps | Sym | Concat | Union | Star |
  Opt | Plus`), its language semantics `Matches`, and `IsSore`, the single-occurrence
  predicate.
- `src/Chain.dfy` — the "chain" building block (tier 1): given an ordered list of
  distinct symbols, decide whether a string is a concatenation of runs of those symbols
  in that order (`Fits`), build the corresponding regex (`ConcatAll`), and prove both
  that fitting implies acceptance (`FitsSound`) and that a duplicate-free order yields a
  single-occurrence regex (`NoDupImpliesSore`). Also holds:
  - the periodic-block-with-choice building block (tier 2): `BlockPieces(Sigmas)` builds
    a regex for one repetition of the block from a list of per-position character sets
    (`UnionAll(Sigmas[i])` at each position `i`, reducing to a plain literal when
    `Sigmas[i]` is a singleton); `FitsPeriodChoice`/`FitsPeriodChoiceSound` decide whether
    a string is exactly `p` characters repeated some positive number of times with each
    repetition's `i`-th character drawn from `Sigmas[i]` (re-checked independently at
    every repetition, not assumed identical across them) and prove that
    `Plus(BlockPieces(Sigmas))` is sound for such strings; `PeriodicChoiceIsSore` proves
    single-occurrence given every `Sigmas[i]` is itself duplicate-free
    (`SigmasNoDupBound`) and no character is shared *across* two different positions
    (`SigmasPairwiseDisjoint`/`SeqDisjoint`) — this cross-position disjointness is the one
    condition that's actually correctness-critical, exactly like every other disjointness
    check in this project;
  - the choice-slot refinement (a tighter alternative *within* tier 1): the `Slot`
    datatype (`SSingle`/`SChoice`), `SlotsRegex`/`FitsSlots`/`FitsSlotsSound` (a
    self-contained soundness proof mirroring `Fits`/`FitsSound`, independent of how the
    slots were built), `SlotsRegexSymbols` (symbol-preservation, used for the
    single-occurrence proof), and the heuristic slot-builder `BuildSlots` (with its own
    symbol-preservation proof `BuildSlotsAtSymbols`, but no other correctness burden —
    see "Design: a certifying algorithm");
  - `UnionAll`/`UnionAllSound`/`UnionAllIsSore`/`UnionStarSound` — the wildcard (tier 3)
    building block, also reused by `SChoice` slots for a mandatory/optional choice among
    several mutually-exclusive symbols;
  - two small pieces still needed for tier 0's literal prefix/suffix (`ConcatLiteral(P)`/
    `ConcatLiteral(Q)`) even though tier 0 itself is defined in `Infer.dfy` and recurses
    rather than building a flat literal alternation here: `NoDupConcatDisjoint` ("no
    shared character" between two strings, expressed as `NoDup` of their concatenation,
    so neither this file nor `Infer.dfy`'s tier-0 code needs a separate "disjoint
    alphabets" predicate just for strings) and `NoDupImpliesConcatLiteralSore` (a
    duplicate-free literal block is single-occurrence).
- `src/Infer.dfy` — alphabet partitioning, the per-component tiers (0 through 3), and the
  top-level algorithm:
  - grouping: `BuildGroups`/`MergeOneString` compute connected components of the
    co-occurrence relation over the (non-empty) sample strings, threaded through three
    invariants proved directly (not via the certifying-algorithm pattern, since
    connected components are canonical rather than heuristic) — `PairwiseDisjoint`
    (components never share a character), `Contained` (every sample assigned to a
    component only uses that component's characters), and `NoEmptyMembers` (`""` is
    never assigned anywhere, since it belongs to no component); `BuildGroupsCoversAll`
    proves every non-empty sample ends up in some component. The same machinery is
    reused *inside* tier 0 (see below) to partition a component's leftover middles;
  - `InferGroup`: tries tier 0 (prefix/suffix literal alternation, now recursive) first,
    falling through to `InferGroupPositionalSplit` (the positional-split tier — split
    every same-length sample at one fixed index into two independently-solved halves)
    when tier 0's checker rejects its candidate, which itself falls through to
    `InferGroupFallback` — the original three-tier construction (chain / periodic block
    / wildcard), completely unchanged — when the positional split doesn't apply either.
    All three share the symbol-containment postcondition (`Symbols(r) <=
    AlphabetAll(strs)`) needed to justify combining components via `Union` without
    symbol reuse. `InferGroupPositionalSplit`, `InferGroup`, and `InferGroups` are
    mutually recursive (see "Design: tier 0" and "Design: positional split" for the
    termination argument — a lexicographic `TotalLength`-plus-tag `decreases` clause on
    each, tags `0 < 1 < 2` respectively);
    - tier 0: `LCP`/`LCS` propose the longest common prefix/suffix of the component's
      samples (`LCPIsPrefix`/`LCSIsSuffix` prove they really are a prefix/suffix of
      every sample that contains them, nothing about the heuristic's *choice* of
      candidate); `Middle` slices out what's left of each sample after stripping both
      ends; `CheckPrefixSuffixAll` independently verifies the proposed prefix/suffix
      actually fits every sample; `Dedup` removes duplicate middles; the check that
      licenses recursing is `strs != [] && (P != "" || Q != "") &&
      CheckPrefixSuffixAll(strs, P, Q) && NoDup(P) && NoDup(Q) && NoDup(P + Q) &&
      StringAlphabet(P) * AlphabetAll(distinctMiddles) == {} &&
      StringAlphabet(Q) * AlphabetAll(distinctMiddles) == {}`; if it passes,
      `BuildGroups(distinctMiddles, [])` partitions the middles and `InferGroups` solves
      that partition, recursing back into `InferGroup` for each piece — see "Design:
      tier 0";
    - tier 1: a heuristic that proposes a candidate symbol order (`MergeString`/
      `MergeAll`), and a checker that verifies whether that candidate actually fits
      every sample (`CheckOrderAll` + `NoDup`);
    - tier 2: a heuristic that proposes a candidate period `p` by directly re-checking
      each candidate length (1, 2, ... up to the first non-empty sample's own length)
      against every sample rather than using some cheap necessary-but-insufficient
      pre-filter (`|t| % p == 0` alone is satisfied by `p = 1` for literally any string,
      which would short-circuit before ever trying a real period) — `CandidatePeriod`/
      `FindPeriodChoice` — together with, for each of the `p` positions, the set of
      characters actually observed there across every sample (`PositionAlphabetSeq`/
      `BuildSigmas`); a checker that verifies the period and per-position alphabets
      together cover every sample (`CheckPeriodChoiceAll`) *and* that the alphabets are
      pairwise disjoint across positions (`SigmasPairwiseDisjoint`);
    - tier 3: the always-sound `Star(a1|a2|...|an)` wildcard fallback (`UnionAll` +
      `UnionStarSound`) over that component's own alphabet (`AlphabetAll`);
  - `InferGroupPositionalSplit` (tried between tier 0 and tier 1): tries a front-alphabet
    split first — `Sigma1 := FrontAlphabet(strs)` (every character ever seen as some
    sample's first character), `MaximalPrefixInSet`/`TakeFrontRun`/`DropFrontRun` split
    each sample at its own maximal leading run of `Sigma1`-characters (a run length that
    can differ from sample to sample — nothing here requires a shared fixed length or
    even a shared total length any more), gated on a non-degeneracy witness
    (`FindNonDegenerateWitness`) plus the disjointness check
    `AlphabetAll(Dedup(DropFrontRuns(strs,Sigma1))) * Sigma1 == {}` — falling back to the
    mirror-image back-alphabet split (`BackAlphabet`/`MaximalSuffixInSet`/`TakeBackRun`/
    `DropBackRun`/`FindNonDegenerateWitnessBack`) if that finds nothing; either way it
    then recurses via `BuildGroups`/`InferGroups` on each side independently and
    `Concat`s the two results — see "Design: positional split";
  - `InferGroups`: folds `InferGroup` over every component and combines the results with
    `Union`, using `SymbolsDisjointIsSore` (licensed by `PairwiseDisjoint` +
    `InferGroup`'s containment postcondition) to prove the combined regex is still
    single-occurrence;
  - the `Infer` method itself, which builds the groups, calls `InferGroups`, handles
    `""` (via `Opt`, exactly as before — `""` belongs to no component, so it's handled
    once at the very top rather than inside any component), and carries the two
    top-level theorems as `ensures` clauses.
- `src/Tests.dfy` — executable `{:test}` methods: a handful of hardcoded cases
  (including ones that specifically distinguish each tier from the next by checking a
  string only the *looser* tier would accept, ones that specifically distinguish
  grouped behavior from one-big-wildcard behavior by checking that cross-component
  strings are rejected, ones that specifically check tier 0 rejects cross-alternative
  mixing like `"SAYE"`/`"SXBE"` for `{"SABE","SXYE"}`, one — for
  `{"Xreq","Xopt1","Xopt2"}` — that specifically checks tier 0's *recursive* step
  actually engages, rejecting `"Xo"`/`"Xopt3"`/`"Xreqopt1"`, and four for the positional
  split — `{"ax","bx","ay","by"}` (front-alphabet variant, same-length samples),
  `{"ax","bx","ayy","byy"}` (front-alphabet variant, mixed-length samples),
  `{"xa","xb","yya","yyb"}` (back-alphabet variant), and
  `{"ax","ayyy","bbx","bbyyy"}` (front-alphabet variant, *neither* axis has a length
  shared across all samples) — that check the tier gives the tight, deterministic result
  (e.g. `[ab][xy]`- or `(?:a|b+)(?:x|y+)`-equivalent) rather than the flaky wildcard/
  tight-chain split tier 1 alone used to produce), plus two ~300-trial fuzz loops — one with a
  general in-Dafny linear congruential generator, one biased toward periodic strings to
  exercise tier 2 — all checked at runtime with `expect`.

## Design: alphabet partitioning

Unlike the tier-1/tier-2 heuristics below, grouping is **not** a certifying-algorithm
heuristic — connected components of the co-occurrence relation are a canonical,
well-defined notion, so the construction is proved correct directly rather than
proposed-then-checked:

1. `BuildGroups` folds over the sample strings (via `MergeOneString`), maintaining each
   sample's character set as either joining an existing component it shares a character
   with (merging that component and every other component it also touches into one), or
   starting a fresh singleton component.
2. Three invariants are carried through that fold and proved preserved by every single
   merge step: `PairwiseDisjoint` (no two components share a character — the property
   that licenses combining them with `Union` later), `Contained` (every sample assigned
   to a component only ever uses that component's own characters), and `NoEmptyMembers`
   (`""` never becomes a member of any component, since `MergeOneString` leaves the
   groups untouched whenever the incoming string's character set is empty — which is
   exactly when the string is `""`).
3. `BuildGroupsCoversAll` proves every non-empty-alphabet sample ends up a member of
   some component in the final result (via `ConcatMembers`, the flattened list of every
   component's members) — established by relating `BuildGroups` over an arbitrary split
   of the sample list (`BuildGroupsAppend`) to the point where that specific sample was
   processed.
4. `InferGroups` folds `InferGroup` over the components and combines them with `Union`.
   The one substantive proof obligation at each fold step is that the two sides'
   symbol sets are disjoint (required by `SymbolsDisjointIsSore` to conclude the `Union`
   is still single-occurrence) — which follows from `PairwiseDisjoint` together with
   `InferGroup`'s own symbol-containment postcondition (`Symbols(r) <= AlphabetAll(strs)`,
   proved for each of its three tiers) and an analogous containment postcondition on
   `InferGroups` itself, carried inductively through the fold.

## Design: tier 0

Plain per-character decomposition (tiers 1-3) can get the *shape* of a decision wrong,
not just its tightness. For `{"SABE","SXYE"}`, the per-character chain heuristic happens
to place `B` and `X` adjacently and merges them into a choice slot, but leaves `A` and
`Y` as independent optional singles — giving `SA?[BX]Y?E`, which still wrongly accepts
`"SAXE"` or `"SBYE"` (mixing a piece of one alternative with a piece of the other). The
real structure is that `"AB"` and `"XY"` are mutually exclusive *whole blocks*, not
independently-varying single characters. Tier 0 looks for exactly this shape, one level
up from individual characters:

1. Propose `P := LCP(strs)` (longest common prefix) and `Q := LCS(strs)` (longest common
   suffix) of the component's samples — a heuristic, same as everywhere else in this
   project: nothing is proved about *how good* a candidate this is, only that `LCP`/`LCS`
   terminate and that `LCPIsPrefix`/`LCSIsSuffix` correctly describe whatever they
   produce (that it really is a prefix/suffix of every sample containing it). Tier 0 only
   applies at all when there's something nonempty to strip (`P != "" || Q != ""`) —
   stripping nothing would make the recursive step below a no-op, see "recursive"
   paragraph.
2. Strip `P` and `Q` off every sample to get its `Middle` — what's left in between — and
   check, independently, that this was actually valid for *every* sample
   (`CheckPrefixSuffixAll`: no overlap between `P` and `Q`, and both genuinely are that
   sample's prefix/suffix).
3. Deduplicate the middles (`Dedup`) and check that neither `P` nor `Q` shares a character
   with any of them (`StringAlphabet(P) * AlphabetAll(distinctMiddles) == {}`, similarly
   for `Q`) — needed so the outer `Concat(P, Concat(_, Q))` stays single-occurrence
   regardless of what the middles turn out to need internally.
4. **Recurse on the middles**: partition `distinctMiddles` by character co-occurrence with
   the very same `BuildGroups` used to split the top-level input into components, then
   solve that partition with `InferGroups` — literally the same function this whole
   process started from, just handed a smaller batch of strings. Each resulting
   sub-component goes back through `InferGroup`, which means it can hit tier 0 again (a
   further prefix/suffix strip), tier 1 (chain/choice-slot), tier 2 (periodic block), or
   tier 3 (wildcard), all scoped to just that sub-component. Wrap the result in `Opt` if
   `"" in distinctMiddles` (some sample was exactly `P + Q` with nothing in between,
   mirroring how `Infer` handles `"" in S` at the very top).
5. Build
   `Concat(ConcatLiteral(P), Concat(rMid, ConcatLiteral(Q)))` where `rMid` is whatever
   step 4 produced. If any earlier check fails, fall through to `InferGroupFallback`
   (tiers 1-3) unchanged.

**Why this recurses instead of requiring the middles to already be pairwise disjoint:**
an earlier, non-recursive version of tier 0 required `distinctMiddles` to be pairwise
alphabet-disjoint *up front*, which meant `{"Xreq","Xopt1","Xopt2"}` (middles
`{"req","opt1","opt2"}`, where `"opt1"`/`"opt2"` share `{o,p,t}`) rejected the whole
decomposition outright, even though `"req"` genuinely is disjoint from the other two and
`{"opt1","opt2"}` themselves have further common-prefix structure (`"opt"` + disjoint
`"1"`/`"2"`) one recursive step down. This gap was found empirically by
`compare_grex.py`'s fuzz mode (see below), comparing against the independent `grex` tool
— see `TestPrefixSuffixRecursesOnMiddles` in `Tests.dfy`.

**Termination.** `InferGroup` and `InferGroups` are now mutually recursive (tier 0's step
4 calls `InferGroups`, which calls back into `InferGroup` for each of its own partition's
members), and the two edges behave differently:
- `InferGroup(strs) -> InferGroups(midGroups)` always strictly shrinks the *total length*
  of all strings involved (`TotalLength`, summed over the batch): tier 0 only takes this
  path when something nonempty was actually stripped from *every* sample (step 1's
  guard), so `TotalLength(distinctMiddles) < TotalLength(strs)` always, and `BuildGroups`
  only ever regroups strings, never changes their total length.
- `InferGroups(groups) -> InferGroup(groups[0].1)` can be a **no-op** in terms of total
  length: `BuildGroups` might partition a batch into a single group covering everything
  (exactly what happens for `{"opt1","opt2"}` — they can't be split further by
  co-occurrence alone), so `groups[0].1` can have the same total length as the batch
  `InferGroups` started with.

A single `decreases TotalLength(...)` clause on both methods would reject the second edge
outright (Dafny can't tell it always shrinks, because it doesn't). The fix is a
lexicographic pair with a constant tie-breaking second component. Three methods now
share this scheme (the positional split tier, below, adds a third): `InferGroupPositionalSplit`
uses `decreases TotalLength(strs), 0`, `InferGroup` uses `decreases TotalLength(strs), 1`,
and `InferGroups` uses `decreases TotalLength(ConcatMembers(groups)), 2, |groups|`. At any
no-shrink edge, the first (`TotalLength`) components tie, so Dafny compares the second —
the tags are ordered so that's always a strict `<` exactly where it's needed (`InferGroup`
calling `InferGroupPositionalSplit` with the very same `strs`: `0 < 1`; `InferGroups`
calling `InferGroup` when `BuildGroups` doesn't split a batch at all: `1 < 2`) regardless
of whether anything actually shrank. Every always-safe edge (any call whose `TotalLength`
strictly decreases) never even needs the tie-breaker. (`InferGroups`' own self-recursion
on `groups[1..]` also needs a tie-breaker of its own for the case where `groups[0].1`
contributes nothing to the total length; the third component, `|groups|`, covers that.)

Because tier 0 is tried *first*, it actually ends up handling several cases that used to
demonstrate the tier-1 choice-slot refinement (`{"cat","car","cab"}`, `{"abc","adc"}`) —
both happen to have a clean common-prefix/common-suffix decomposition too, and tier 0
gets there before tier 1 is even attempted. This is harmless (both tiers are
independently sound, and the tests for each check *behavioral* properties of the result,
not which tier produced it) and expected, not a regression.

## Design: positional split

Tier 0 and tier 1 both failed on `{"ax","bx","ay","by"}`: tier 0 needs a *literal* common
prefix or suffix shared by every sample, but here the samples start with `a` **or** `b`
(never the same character) and end with `x` **or** `y` — there's nothing to strip. Tier
1's chain heuristic tries to lay every character out on a single line and has no way to
represent two genuinely independent alternation axes; building that single order hits a
spurious conflict the moment it meets the second axis (`b` is a fresh symbol encountered
right where `x` — already placed, but not at the front — blocks it, even though `a`/`b`
never actually co-occur, so there's no real conflict). Depending on the arbitrary order
the (since-replaced, see "Determinism and reproducibility" below) `SetToSeq` happened to
hand the samples in — itself dependent on Python's per-process string hash randomization
when going through the compiled CLI, before that helper was replaced with a canonical
sorted extraction — tier 1 would sometimes stumble into a valid order anyway and
sometimes not — a genuinely flaky gap, found and pinned down with `compare_grex.py` (see
below): `grex` reliably answers `^[ab][xy]$`; this project's
output varied run to run between that shape and a full wildcard.

Tried after tier 0 and before tier 1 (`InferGroupPositionalSplit`, in `Infer.dfy`), this
tier looks for a much simpler shape: **some split point, not necessarily the same numeric
index for every sample**, that separates each sample into two pieces drawn from disjoint
alphabets. An earlier version of this tier required a shared *fixed length* on (at least)
one side, which worked for `{"ax","bx","ay","by"}` (split every sample at index 1) and
even `{"ax","bx","ayy","byy"}` (fixed-length prefix `p=1`, variable-length suffix), but
could not touch `{"ax","ayyy","bbx","bbyyy"}` — axis 1 is `"a"` (length 1) vs `"bb"`
(length 2), axis 2 is `"x"` (length 1) vs `"yyy"` (length 3): *neither* axis has a length
that's the same across every sample, so no fixed split index exists at all. The current
version generalizes the split criterion from "a shared index" to "a shared *alphabet*":
each sample's own split point is wherever its maximal leading (or trailing) run of
characters drawn from a candidate alphabet ends — a run can be any length, so samples no
longer need to agree on where the run stops, only on *which characters* it's made of. It
comes in two variants, tried in order:

1. **Front-alphabet split.** The candidate alphabet is `Sigma1 := FrontAlphabet(strs)` —
   every character ever seen as *some* sample's first character (so trivially `t[0] in
   Sigma1` for every `t`). For each sample, `MaximalPrefixInSet(t, Sigma1)` is the length of
   its maximal leading run of `Sigma1`-characters; `TakeFrontRun`/`DropFrontRun` split it
   there. `Prefixes := Dedup(TakeFrontRuns(strs, Sigma1))`, `Suffixes :=
   Dedup(DropFrontRuns(strs, Sigma1))` (the leftover "rest" of each sample — possibly
   different lengths from each other, and possibly `""` for a sample entirely made of
   `Sigma1`-characters). Two conditions gate this variant: a **non-degeneracy witness**
   (some sample whose run doesn't consume it entirely — `FindNonDegenerateWitness` looks
   for one; without it, every sample would be entirely `Sigma1`-characters and the
   "prefix" side would make zero progress, breaking termination) and the usual
   **disjointness check**, `AlphabetAll(Suffixes) * Sigma1 == {}` (no `Sigma1`-character
   ever reappears after the run — `Prefixes`' own alphabet is automatically `⊆ Sigma1` by
   construction, so nothing more needs checking on that side). Both are exactly the
   "propose a candidate cheaply, verify it, otherwise fall back" pattern used everywhere
   else in this project — the alphabet itself (`Sigma1`) carries no correctness burden;
   only the disjointness check does.
2. **Back-alphabet split** — the mirror image (`Sigma2 := BackAlphabet(strs)`, the
   trailing-run analogue of the above), tried only if the front-alphabet variant finds no
   usable split at all. This is what's still needed for e.g. `{"xa","xb","yya","yyb"}`
   (fixed-length suffix `"a"`/`"b"`, variable-length prefix `"x"`/`"yy"` before it): the
   front-alphabet candidate here would be `{x,y}` (first characters), but `y` also
   reappears in `"yya"`/`"yyb"`'s *own* leading run in a way that doesn't cleanly separate
   from the rest — the back-alphabet candidate `{a,b}` (last characters) finds the right
   split directly.
3. **Recurse on each side independently** (whichever variant matched): `BuildGroups` +
   `InferGroups` on `Prefixes`, and again on `Suffixes` — literally the same recursive
   step tier 0 already uses for its middles, just applied twice (once per side) and
   combined with `Concat` instead of `Union` (a sample here is the concatenation of *both*
   halves, not a choice between pieces). Unlike the old fixed-length version, one side
   *can* now contain `""` (a sample entirely made of the candidate alphabet's characters)
   — handled exactly like tier 0 handles an empty middle, wrapping that side's recursive
   result in `Opt`.
4. If neither variant finds a usable split, fall through to `InferGroupFallback` (tiers
   1-3) unchanged.

**Termination**: the key fact is that a sample's own run is nonempty as soon as it starts
(resp. ends) with a candidate-alphabet character — which is *guaranteed* by how the
candidate alphabet is built (`Sigma1`/`Sigma2` are defined as exactly the characters
observed at that position) — so the "rest" side (`DropFrontRuns`/`DropBackRuns`) always
strictly shrinks, unconditionally, for *any* candidate alphabet built this way. The "run"
side (`TakeFrontRuns`/`TakeBackRuns`) only strictly shrinks once *something* is left over
*somewhere* in the batch — exactly the non-degeneracy witness from step 1. Rather than
prove this per-element (which hit a genuine SMT solver blowup for the back-alphabet
variant — see below), both directions use one exact identity,
`TotalLength(TakeFrontRuns(strs,chars)) + TotalLength(DropFrontRuns(strs,chars)) ==
TotalLength(strs)` (`FrontRunsTotalLengthSum`/`BackRunsTotalLengthSum`, a one-line
induction over `TakeFrontRunSplitReconstructs`/`TakeBackRunSplitReconstructs`), plus a
generic "a list containing some nonempty element has positive total length"
(`SomeNonEmptyTotalLengthPos`) — giving both the unconditional and the witness-gated
bound as easy corollaries of the same sum fact, with no case-by-case per-element
recursion needed for either. `InferGroupPositionalSplit`'s own calls into `InferGroups`
are then licensed by `TotalLength` alone, exactly like tier 0's — reusing tier 0's
existing lexicographic tag scheme (`InferGroupPositionalSplit=0 < InferGroup=1 <
InferGroups=2`) without any change.

*(A genuine SMT hiccup, not just slowness: the first cut of the back-alphabet
"unconditional" bound mirrored the front-alphabet proof's own per-element induction
almost verbatim, and Z3 choked on it outright — "Overflow encountered when expanding
vector," reproducible even after raising the time limit far past what a merely-slow proof
would need. Rewriting that one lemma to go through the sum identity instead (matching how
the *other*, witness-gated bound was already proved) sidestepped whatever the back-slicing
recursion was triggering, rather than chasing the underlying solver behavior further.)*

`{"ax","bx","ay","by"}` and `{"ax","bx","ayy","byy"}` both find a front-alphabet split
(`Sigma1={a,b}`) into `{"a","b"}` and `{"x","y"}` / `{"x","yy"}` respectively;
`{"xa","xb","yya","yyb"}` needs the back-alphabet variant (`Sigma2={a,b}`), splitting into
`{"x","yy"}` and `{"a","b"}`; `{"ax","ayyy","bbx","bbyyy"}` — the case with *no* fixed
length on either side — finds a front-alphabet split too (`Sigma1={a,b}`, giving runs `"a"`
or `"bb"` per sample). Each side is solved independently and concatenated — giving
something equivalent to `[ab][xy]`, `[ab](?:x|y+)`, `(?:x|y+)[ab]`, and
`(?:a|b+)(?:x|y+)` respectively, deterministically, regardless of processing order.
`grex`'s own answer for the variable-length cases (e.g. `^[ab](?:yy|x)$`) is itself *not*
single-occurrence (`y` appears twice, spelled `"yy"`), so those are checked directly with
`Matches` in `Tests.dfy` rather than via `compare_grex.py`, which correctly reports
"nothing to compare" for them. See `TestPositionalSplitOnIndependentAlternationAxes`,
`TestPositionalSplitVariableLength`, `TestPositionalSplitFixedSuffixVariant`, and
`TestPositionalSplitNeitherSideFixedLength` in `Tests.dfy`.

This heuristic still only tries **one** candidate alphabet per direction — the observed
first (resp. last) characters — not an exhaustive search over all possible alphabet
bipartitions, so some exotic cases might still slip through and fall all the way to
`InferGroupFallback`'s wildcard. In all the cases explored while building this (including
the full test suite and hundreds of `compare_grex.py --fuzz` trials), the back-alphabet
variant was needed for exactly one case (`{"xa","xb","yya","yyb"}`-shaped inputs); every
other case tried was already caught by the front-alphabet variant alone.

## Design: a certifying algorithm

Proving a real SORE-inference algorithm correct by reasoning about the algorithm's
*construction process* tends to be painful in Dafny (you'd need an invariant that
holds across every step of a heuristic merge). Instead this project uses the
*certifying algorithm* pattern:

1. `MergeAll` is a cheap heuristic that proposes a candidate symbol order by walking
   each sample string and greedily building an order in which same symbol runs stay
   grouped together (e.g. from `"cat"`, `"car"`, `"cab"` it proposes something like
   `[c, a, t, r, b]`-ish, encoding "each string is a `c`-run then an `a`-run then a
   run of one of `t`/`r`/`b`"). **It carries no correctness burden beyond
   termination** — nothing is proved about it, and nothing needs to be.
2. `CheckOrderAll(strs, order) && NoDup(order)` is a completely independent,
   easy-to-verify *checker*: does every sample actually decompose into runs in that
   exact order, and is the order itself duplicate-free? This is what `FitsSound` and
   `NoDupImpliesSore` are proved about, with no reference to how `order` was produced.
3. `Infer` builds the chain regex only if the checker passes; otherwise it falls back
   to `Star(a1|...|an)` over the sample alphabet, which is unconditionally sound (it
   accepts every string over that alphabet) and unconditionally single-occurrence.

Because the checker's soundness proof (step 2) doesn't depend on the heuristic at all,
`MergeAll` could be replaced by a smarter heuristic (or a dumb one, or a random one)
without touching a single proof — only the *test* results (how often the chain path
is actually taken vs. the fallback) would change.

## Design: the choice-slot refinement

Plain `ConcatAll(order)` treats every position in the chain identically: each symbol
gets `Opt(Plus(Sym(c)))`, independently optional and independently repeatable,
regardless of what the samples actually show. That's sound but can be much looser than
necessary — e.g. for `{"abc","adc"}`, `order = [a,d,b,c]` (or similar) gives
`a?b?d?c?`-shaped output, which also wrongly accepts `"abdc"` (mixing both `b` and `d`,
which no sample does) and skips-everything strings like `""`, neither of which is
remotely close to the real structure. The choice-slot refinement, applied once a
candidate `order` has already passed `CheckOrderAll`, tries a tighter alternative before
falling back to `ConcatAll`:

1. `BuildSlots(order, strs)` partitions `order` into contiguous **slots**: a lone
   position becomes `SSingle(c, mandatory, rep)` (dropping `Opt`/`Plus` when the samples
   show `c` is always present, and/or never repeats), while a maximal run of adjacent
   positions that (a) never repeat and (b) are pairwise mutually exclusive — no sample
   ever shows two of them at once — collapses into one `SChoice(cs, mandatory)`. For
   `{"abc","adc"}` this gives `[SSingle('a',...), SChoice(['d','b'],...), SSingle('c',...)]`
   → printed as `a[bd]c`.
2. Mutual exclusivity is checked explicitly (`CoOccursWithAny`), *not* assumed for free
   — it would be tempting to think "at most one alternative can match at a given
   position" is automatic, since `RunLength(t,c)>0` forces `t[0]==c` and `t[0]` is one
   specific character, but that reasoning only holds for the *end result* (`FitsSlots`'s
   own check). It says nothing about whether merging a batch of positions into one slot
   is *appropriate* in the first place — two positions that are both mandatory and
   always co-occur (like `a` and `c` in `{"abc","adc"}`) would merge into a nonsensical,
   uncheckable single choice slot without this check (an earlier draft of this feature
   had exactly this bug, caught by the tests below).
3. Like every other heuristic in this project, `BuildSlots` carries no correctness
   burden beyond terminating and preserving the symbol multiset (`BuildSlotsAtSymbols`,
   needed for the single-occurrence proof) — actual soundness rests entirely on
   `CheckSlotsAll` (mirroring `CheckOrderAll`/`CheckPeriodChoiceAll`) independently re-checking
   the proposed slots against every sample via the self-contained `FitsSlotsSound`. If
   `CheckSlotsAll` fails for any reason, `InferGroup` falls back to the already-proven
   plain `ConcatAll(order)` — never to a wrong result.

`TestChoiceSlotMergesMutuallyExclusiveAlternatives` and `TestThreeWayChoiceSlot` in
`Tests.dfy` assert the tightened behavior directly (e.g. that `{"abc","adc"}`'s result
rejects `"abdc"`, `"ac"`, and `"abbc"`, not just that it accepts the original samples).

## Why `Opt`/`Plus` are primitive constructors, not macros

An earlier draft defined `Plus(r) = Concat(r, Star(r))` and `Opt(r) = Union(r, Eps)`
as plain functions. That's wrong for this purpose: `Symbols(Concat(r, Star(r)))`
counts every symbol of `r` *twice* (once directly, once inside the `Star`), so `c+`
would look like two occurrences of `c` under a leaf-counting single-occurrence
predicate — defeating the entire point. `Opt` and `Plus` are therefore their own
datatype constructors with their own `Matches` and `Symbols` cases, matching how the
SORE literature actually treats `?`, `*`, `+` as unary postfix operators on an
already-single-occurrence sub-expression, not desugared syntax.

## Why `Infer` is a `method`, not a `function`

Converting the input `set<string>` into a concrete processing order requires an
assign-such-that pick (`var x :| x in rem`) somewhere — Dafny only allows *compiling*
such a pick inside a `method`, since a compiled `function` would need the witness to be
*uniquely determined*, which an arbitrary element of a set obviously isn't. That pick
now lives only inside `FindMinChar`/`FindMinString`'s own recursive scan (see
"Determinism and reproducibility" below) — their *results* are provably unique (the
true minimum of the set, by a fixed total order), so the pick doesn't leak
nondeterminism into anything that calls them, but Dafny still requires the enclosing
declarations to be `method`s rather than `function`s. So `Infer`, `SortedCharSeq`,
`SortedStringSeq`, and `FindMinChar`/`FindMinString` are methods; everything else in the
algorithm (`MergeString`, `CheckOrderAll`, `ConcatAll`, etc.) is a plain deterministic
`function` over `seq`, and `Infer`'s `ensures` clauses carry the two theorems:

```dafny
method Infer(S: set<string>) returns (r: Regex)
  ensures forall t :: t in S ==> Matches(r, t)   // soundness
  ensures IsSore(r)                              // single-occurrence
```

**Tier 0 (prefix/suffix literal alternation):** only ever tries the single candidate
pair `(LCP(strs), LCS(strs))` — the *longest* common prefix and suffix — and gives up
entirely (falling through to tiers 1-3) if that specific pair doesn't yield disjoint
middles, even if some *shorter* prefix/suffix choice might have worked. E.g. if the
longest common prefix accidentally eats into what should have been part of a
mutually-exclusive middle, tier 0 won't back off and try a shorter prefix instead — it
just fails over to the per-character tiers. Same "propose one candidate, verify,
otherwise fall back" spirit as every other heuristic here; soundness is unaffected,
only how often the tightest available shape is actually found.

## Determinism and reproducibility

For a long stretch of this project's history, `Infer`'s output was *sound and
reasonably tight on every run*, but not necessarily the *same text* run to run for the
same input. Root cause: the original `SetToSeq<T(==)>` helper converted a `set<string>`
(or a `set<char>` alphabet) into a `seq` using a bare `var x :| x in rem` — Dafny's
"pick some element satisfying this" operator, which deliberately does not specify
*which* element gets picked. Compiled to Python, that pick bottoms out in Python's own
`set`/`frozenset` iteration order, which is hash-randomized per process by default
(`PYTHONHASHSEED` is randomized unless pinned) — so the exact same logical set of input
strings could enumerate in a different order on every fresh `python3` invocation. That
order fed into every tier's heuristics (which candidate chain order, split point, or
period got tried first) and into how alphabets got laid out into character classes, so
e.g. `python3 ./sore.py SABE SXYE SMNOE` could print `S(?:AB|MNO|XY)E` on one run and
`S(?:XY|MNO|AB)E` on the next — both sound, both equally tight, but not the same text.

The fix: `SetToSeq` is gone, replaced by `SortedCharSeq`/`SortedStringSeq`, which
repeatedly extract the *minimum* remaining element (`FindMinChar`/`FindMinString`, using
`char`'s native `<` — already a total order, backed by Unicode code points — and a new
`StringLess` lexicographic order over `string`, with its own `StringLessTrichotomy`/
`StringLessTransitive`/`StringLessIrreflexive` lemmas) instead of *any* element. The
result is now a canonical function of the set's content: two equal sets always sort to
the same sequence, regardless of what the underlying runtime representation's iteration
order happens to be. `FindMinChar`/`FindMinString` still use `:|` internally to grab a
starting candidate for their scan, but that doesn't reintroduce nondeterminism — their
`ensures` clauses pin the returned value down as *the* minimum, a quantity that's
independent of scan order by definition, so the value they return is the same
regardless of which arbitrary element the runtime handed back first.

`Infer`'s output is now a genuinely deterministic function of the input set: the same
input always produces byte-identical regex text, verified by running every interesting
example from this project's history (`ax bx ay by`, `ax bx ayy byy`, `ax ayyy bbx
bbyyy`, `abc adc`, `cat car cab`, `Xreq Xopt1 Xopt2`, `abab acac`, `abab`, `ab ba cd`,
and the `SABE SXYE SMNOE` case above) across 10+ repeated runs and across
`PYTHONHASHSEED=0` through `9` — all byte-identical, not just "equivalent." This is a
meaningfully stronger guarantee than what every `PYTHONHASHSEED`-varying check in this
README's differential-testing history was actually confirming before this fix (those
checks verified "reliably sound and tight," which remains true, but did not — and could
not have — verified "the exact same text," since it wasn't true yet).

## Bug fix: order-dependent choice-slot merging

This one is a genuine bug fix, not a new capability or a documented scope cut — worth
calling out separately from "known limitations" below because, unlike those, it wasn't
an accepted tradeoff.

`Infer({"ABCDE", "ACDE", "ABE"})` used to print `A[CB]+D?E` — sound (it does accept all
three samples), but wrong-shaped: it treats `B` and `C` as an interchangeable, repeatable
choice, so it also (wrongly) accepts `"ACBDE"` (`C` before `B` — backwards; never
observed) and `"ABCBCDE"` (repeated/mixed `B`/`C`). The correct answer is `AB?C?D?E` — `B`,
`C`, and `D` each independently optional, in the one fixed relative order they actually
appear in across the three samples.

**Root cause.** `Infer` first strips the common prefix `"A"`/suffix `"E"` (tier 0),
recurses into solving `{"BCD", "CD", "B"}`, which recurses again (via the alphabet-based
split) into solving `{"B", "C", "BC"}` — and *that* innermost call is where the bug
lived. `InferGroupFallback` ran its chain/choice-slot heuristic (`MergeString`/
`MergeAll`) on whatever literal order its caller happened to hand it, rather than a
canonical one. Fed the literal ordering `["B", "C", "BC"]`, `MergeString`'s greedy,
single-pass heuristic merges `"B"` then `"C"` with no established relationship between
them yet (neither sample alone gives any evidence about their relative order), and
arbitrarily places `C` before `B`. By the time `"BC"` arrives — establishing B-before-C —
the candidate order is already committed and conflicts with it. `CheckOrderAll` correctly
rejects the resulting order (this part worked exactly as designed), but that means the
chain tier never got a valid order to hand to the choice-slot merger at all, so the
construction fell through to a much looser fallback that ends up merging `B` and `C` into
one repeatable class — even though the choice-slot merger's own `CoOccursWithAny` check
(added specifically to prevent exactly this kind of merge, for cases like `{"abc","adc"}`
→ `a[bd]c`) would have correctly kept them as two separate slots, *had the chain tier
succeeded and given it the chance to run*. "Do `B` and `C` co-occur" is a fact about the
sample *set* (yes, via `"BC"`), not about processing order — so this was a real bug, not
acceptable heuristic looseness.

**The fix.** `InferGroupFallback` now sorts its input into canonical order
(`SortedStringSeq`, the same proven sort from the determinism fix above) before running
the chain/choice-slot heuristic, via a thin wrapper (`InferGroupFallback`) around the
unchanged original logic (renamed `InferGroupFallbackCore`). Sorted, `{"B","C","BC"}`
becomes `["B","BC","C"]`, and merging `"BC"` right after `"B"` establishes B-before-C
before `"C"` alone ever gets a chance to be placed arbitrarily — confirmed empirically:
`InferGroupFallbackCore` given `["B","BC","C"]`, `["BC","B","C"]`, or `["C","B","BC"]` (any
ordering other than the one pathological case) already gave the correct `B?C?`. This is
purely a heuristic-quality improvement, not a new correctness mechanism: `MergeString`
carries no correctness burden of its own — `CheckOrderAll`/`CheckSlotsAll` are checked
independently regardless of input order — so sorting here cannot introduce unsoundness,
only change which (always-safe) construction gets picked. It does not make the chain
heuristic *complete* (order-sensitivity is an accepted, documented limitation of
`MergeString` elsewhere in this file — see "Known limitations" below), but it removes one
concrete, previously-undetected way for a *correct* choice-slot-merge safeguard to be
bypassed by feeding it an avoidably bad order.

**Why extensive prior fuzzing missed this.** Triggering it needs a fairly specific,
*deep* scenario: tier 0's recursion into disjoint middles, further recursing through the
alphabet-based split, landing on a 3-element sub-problem in the one specific relative
order (`["B","C","BC"]`) that MergeString mishandles. The project's fuzz generators
(small alphabets, short strings, shallow structure) evidently don't reliably reach that
combination — a reminder that differential testing against `grex` and random fuzzing
are complements to, not substitutes for, actually reading and reasoning about the code
when a user reports a concrete bad output.

## Known limitations (intentional scope cuts)

**Grouping:** components are connected via direct character co-occurrence only — two
characters are related iff *some single sample string* contains both, and components are
merged transitively from there. This is the coarsest split that's still always safe (any
finer split could put two co-occurring characters in different components, which would
then be unable to honestly describe the sample that contains both). Tier 0 (above) does
now recurse *within* a component — after a prefix/suffix strip, the leftover middles get
re-partitioned and solved independently — so a single component isn't strictly
all-or-nothing the way it used to be. But that recursion only ever triggers off a shared
literal prefix/suffix: if a component's samples conflict in a way tier 0 can't strip
anything from (e.g. `{"ab","ba"}` — no common prefix or suffix at all), it's still tier
1/2/3's flat, whole-component treatment that decides the outcome, with no per-position
sub-grouping or interleaving/choice combinators (as in the published SORE-inference
literature) beyond what tier 0's prefix/suffix recursion happens to expose.

**Tier 1 (chain):** within one component, the checker validates the *entire* candidate
order against the *entire* component's samples: if even one sample string conflicts with
the chain, `Infer` falls through to tier 2 (and from there, possibly tier 3) for that
**whole component**, not just the conflicting part of it. (Before grouping existed, this
meant the whole *input*; now it's scoped down to just the connected component that
conflicts — a real improvement, but the same all-or-nothing behavior still applies
within a component.)

**Tier 0 now recurses on its middles** (see "Design: tier 0" above) — after stripping a
common prefix/suffix, the leftover middles are partitioned by co-occurrence and each
sub-partition is solved by recursing all the way back into `InferGroup`/`InferGroups`,
so a *further* shared prefix/suffix or choice structure among the middles gets found too
(this is what makes `{"Xreq","Xopt1","Xopt2"}` work — see above). **Tier 1's own
per-character choice-slot merging, by contrast, is still not recursive** — `BuildSlots`
never re-partitions and re-solves a run of adjacent positions the way tier 0 now does for
whole middles; it only ever merges flat, adjacent single characters into one choice slot
(see the "Choice-slot refinement" limitation below). Generalizing tier 1 the same way
tier 0 was generalized here is a plausible future direction, not attempted in this round.

**Positional split only tries ONE candidate alphabet per direction, and only ever tries a
single split per level** (see "Design: positional split" above). Two earlier, more
restrictive versions of this tier required first a shared fixed *length* on one side
(replaced), then — even in that fixed-length form — could not touch a case where neither
axis had a constant length at all (`{"ax","ayyy","bbx","bbyyy"}`); the alphabet-based split
now in place handles all of these, since it splits on a shared *alphabet* rather than a
shared *length* or *index*. What's still not attempted: an exhaustive search over all
possible alphabet bipartitions (only "characters observed at the very front" and
"characters observed at the very back" are ever tried as candidates — a bipartition that
isn't characterizable as a maximal leading/trailing run of *some* naturally-occurring
candidate alphabet won't be found), and trying more than one split point in sequence
within a single level (finding one split, then further splitting *that* split's own
prefix or suffix independently, as opposed to recursing into the ordinary tiers for each
side, which can of course still find further prefix/suffix or positional structure inside
a side on its own). These remain documented gaps, not attempted here.

Two side effects worth noting: this tier's applicability depends only on the *set* of
samples, not on any processing order, so it also fixed the specific tier-1 flakiness
described in the next paragraph for every case it now reaches, and it fully supersedes
what used to be the standing example of tier 1's `MergeAll`-can't-find-an-existing-order
gap (`{"ax","bx","by"}` — so it now goes through the positional split instead and comes
back as `[ab][xy]`, deterministically). That underlying tier-1 gap is still real in
principle for inputs this tier's two variants don't reach; it just no longer has a short,
previously-documented example, since the known concrete instances of it all turned out to
be fixable by the positional split.

Separately, tier 1's heuristic (`MergeAll`) is a single non-backtracking pass, so it can
still fail to find a working order even when one exists, for cases the positional split
tier doesn't reach. Soundness is unaffected either way (the checker always catches it),
but precision is left on the table in such cases.

**Choice-slot refinement:** `BuildSlots` only ever considers merging *adjacent*
positions in the already-built `order` into one choice — it does not search for
mutually-exclusive alternatives that ended up non-adjacent because `MergeAll` happened
to interleave something else between them. A component whose alternatives really are
mutually exclusive can still miss the tighter choice-slot form (falling back to plain
`ConcatAll`, still sound, just less tight) if the order-building heuristic didn't happen
to place them next to each other. This is the same category of heuristic-incompleteness
as tier 1's order-building itself (see above) — no proof is affected, only how often the
tightest available result is actually found.

**Tier 2 (periodic block, with per-position choice):** within one component, the period
`p` is chosen by directly re-checking each candidate length against every sample in the
component (not a cheap pre-filter), but it only ever considers periods derived from *one*
representative sample — the lexicographically-first non-empty one, per `SortedStringSeq`'s
now-deterministic ordering of that component's samples (see "Determinism and
reproducibility") — so a component whose common period only becomes apparent from a
*different* sample's length (e.g. the first enumerated sample is `"aa"`,
whose own candidate periods are just `1` and `2`, but the component's real shared period
is `3`, only evident from another, longer sample) will still fall through to the tier-3
wildcard. Separately, each position's per-repetition alphabet (`Sigmas[i]`) is built from
every *sample's* character at that position, but only the first repetition within each
sample (`PositionAlphabetSeq` never looks past index `i` itself) — so a single sample
that genuinely varies *within its own* later repetitions at some position (e.g. one
sample alone containing both an `"ab"`-repetition and an `"ac"`-repetition of the same
period, rather than the variation only ever showing up as a difference *between*
samples) can cause the certifying check to reject that period even though a per-position
choice covering it does exist — again, safe (falls through to the wildcard), just not as
tight as possible. Finally, `Plus` only ever produces "one or more" repetitions
(`(ab)+`), never an exact bounded count like `(ab){2}` — that would need a new primitive
`Rep(r, n)` constructor with its own `Matches`/`IsSore` cases, deliberately out of scope
here (`(ab)+` is strictly sound, just not as tight as an exact count).

Module names (`RegexCore`, `SoreInfer`) are distinct from their main datatype/method
names (`Regex`, `Infer`) because Dafny's JavaScript backend silently misbehaves at
runtime (not at verification time) when a module and a value inside it share a name —
worth knowing if you extend this code.

## Running it

Verification (no code execution, just the proofs):

```sh
dafny verify src/Regex.dfy src/Chain.dfy src/Infer.dfy src/Tests.dfy
```

Tests (compiles to JavaScript and runs with Node; requires `bignumber.js`, installed
via `npm install` in this directory — Dafny's numeric types need it at runtime):

```sh
dafny test --target:js src/Tests.dfy
```

(`--target:cs` would be the normal default, but this environment has no `dotnet`/
`javac` installed, only Node — hence targeting JavaScript.)

## Command-line usage

`sore.py` at the project root gives you `Infer` as a regular command-line tool:

```sh
python3 ./sore.py abab abc xab
# [cbax]*
python3 ./sore.py abc adc
# a[bd]c
python3 ./sore.py cat car cab
# ca[trb]
python3 ./sore.py SABE SXYE
# S(?:AB|XY)E
python3 ./sore.py Xreq Xopt1 Xopt2
# X(?:req|opt[12])
```

It prints one line: a Python `re`-compatible regex that is sound for the given
space-separated arguments and single-occurrence, per `Infer`'s proved theorems. A
`Union` of nothing but `Sym` leaves (any nesting) prints as a bracket character class
(`[bd]`) rather than a `(?:b|d)` alternation, since that's what such a union actually
is — including the tier-3 wildcard itself (`(a|b|c)*` prints as `[abc]*`). Anything
else that needs grouping (a `Union` containing a `Concat`/`Star`/etc., or as the operand
of `Concat`/`Star`/`Plus`/`Opt`) still gets `(?:...)`.

**Prerequisite — build the Python target once** (regenerate this after any change to
`src/*.dfy`):

```sh
dafny build --target:py src/Regex.dfy src/Chain.dfy src/Infer.dfy src/Print.dfy src/Main.dfy --output build/sore
```

This writes `build/sore-py/`, including Dafny's own small Python runtime support
(`_dafny/`, `System_/`) — nothing needs to be `pip install`ed separately.

`sore.py` does not shell out to Dafny's own generated `__main__.py` entry point: as
compiled by this Dafny version, that entry point passes `sys.argv` to `Main` as a plain
Python `list` rather than a proper `_dafny.Seq`, which the generated code's
`for x in (strs).Elements` then rejects (`AttributeError: 'list' object has no
attribute 'Elements'`) — worth knowing if you invoke `build/sore-py/__main__.py`
directly instead of going through `sore.py`. Calling `Main.default__.Run(...)` straight
from Python, with the input strings wrapped as a proper `_dafny.Seq` of
`_dafny.Seq`-of-`_dafny.CodePoint` (see `sore.py`'s `_dafny_str`/`infer_regex`
helpers), sidesteps this entirely.

`src/Print.dfy` (`PrettyPrint`, plus a `Simplify` pass that drops the redundant
`Empty`/`Eps` identity elements `InferGroups`' fold and `ConcatAll`'s base case leave
behind, e.g. printing `Union(r, Empty)` as just `r`) is a plain display utility with no
Dafny-level correctness proof of its own — unlike `Infer`, it is not part of the
verified core. As defense in depth, `sore.py` re-parses its own printed text with
Python's `re` module and checks `fullmatch` against every input string before printing
anything; if that check ever fails it means `PrettyPrint`/`Simplify` disagrees with the
proved `Matches` semantics, and `sore.py` reports it as an internal error rather than
silently emitting a wrong regex.

## The bigram-graph alternative implementation

`src/Graph.dfy` (module `BigramGraph`) is a second, completely standalone SORE-inference
implementation, based on contracting a graph built from the input strings' bigrams
(adjacent-character pairs) down to a single node — see the module's own header comment
for the full algorithm (bigram-graph construction, simple-path/self-loop/exact-overlap/
optional/SCC contractions, a topological chain-wrap, and a wildcard fallback of last
resort) and `InferViaBigramGraph`'s `ensures` clauses for its own soundness/soreness
theorems, proved completely independently of `Infer`/`Chain.dfy`. It shares only the
`Regex`/`Matches`/`IsSore` core in `Regex.dfy` with the tiered implementation above —
no other code or proof is reused between the two.

`sore_bigram.py` gives you this second implementation as the same kind of command-line
tool as `sore.py`, for comparing the two side by side:

```sh
dafny build --target:py src/Regex.dfy src/Graph.dfy src/Print.dfy src/MainBigram.dfy --output build/sore_bigram
python3 ./sore_bigram.py B C BC
# B?C?
python3 ./sore_bigram.py abc adc
# a[bd]c
python3 ./sore_bigram.py abab
# [ab]*    (sound, but looser than sore.py's (?:ab)+ — see "Known limitations" in
#           Graph.dfy's header: the bigram-graph algorithm's only repetition
#           mechanism, SCC contraction, is inherently order-blind for genuine cycles)
```

Same CLI conventions and the same `re.fullmatch` self-check defense-in-depth as
`sore.py` (see above) — `sore_bigram.py` is a near-identical wrapper, just pointing at
`MainBigram`/`build/sore_bigram-py/` instead of `Main`/`build/sore-py/`.

`GraphTests.dfy` holds this implementation's own `{:test}` suite (run with
`dafny test --target:js src/Regex.dfy src/Graph.dfy src/GraphTests.dfy`), separate from
`Tests.dfy`'s.

## Differential testing against `grex`

[`grex`](https://github.com/pemistahl/grex) is a mature, independent regex-inference
CLI, unrestricted to single-occurrence output. `compare_grex.py` (project root) checks
that whenever `grex`'s output for a given input set *happens* to already be
single-occurrence, it defines the same language as our own `Infer`'s output for that
same input — good outside evidence that a SORE really does exist for that input, and
that our tool finds an equally good one.

```sh
python3 compare_grex.py STRING [STRING ...]   # compare one input set
python3 compare_grex.py --fuzz [N]            # batch-compare N random sets plus a
                                               # curated list of interesting examples
                                               # from this project's own history
                                               # (default N = 300)
```

For each input set it runs both `grex` and `sore.py`, parses `grex`'s output with a
small hand-written regex parser (literals, `\`-escapes, `[...]`/ranges, `(?:...)`
groups, `|`, and `*`/`+`/`?`/`{m,n}` quantifiers — enough for grex's un-flagged output
vocabulary) to count each alphabet symbol's occurrences as tree *leaves* (a quantifier
wrapping a subtree doesn't multiply its count, same reasoning as `Opt`/`Plus` being
primitive constructors in `Regex.dfy` — see above), and — only when that comes out
single-occurrence — brute-force-enumerates every string up to a length bound over the
combined alphabet (scaled down as the alphabet grows, to keep it fast) checking
`fullmatch` agreement between the two compiled patterns. **This is a strong empirical
check up to that length bound, not a formal proof of language equivalence** — unlike
`Infer`'s own soundness, nothing here is machine-checked for all strings of all lengths.
A construct outside the parser's vocabulary (`.`, `\d`/`\w`/`\s`, negated classes, etc. —
none of which `grex` emits without extra flags we don't pass) is reported as
"unsupported" rather than silently mis-handled.

Prerequisite: `grex` on `PATH`. On this machine, the global `~/.cargo/config.toml`
points cargo's linker at a nonexistent `zigcc`, so install with:

```sh
CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER=cc cargo install grex
```

Running `python3 compare_grex.py --fuzz 300` (or `--fuzz 600`) currently finds **no
mismatches** out of the ~50-70 cases where `grex`'s output happens to be
single-occurrence. This wasn't always true: an earlier version of tier 0 found exactly
one mismatch here — `{"Xreq","Xopt1","Xopt2"}`, where `grex` recursively factors
`X(?:opt[12]|req)$` but the non-recursive tier 0 of the time could only manage the much
looser `Xr?e?[qo]p?t?[12]?` — which is exactly what motivated making tier 0 recursive
(see "Design: tier 0"); `TestPrefixSuffixRecursesOnMiddles` in `Tests.dfy` now covers this
case directly. A second mismatch turned up after that fix — `{"ax","bx","ay","by"}`,
where `grex` reliably answers `^[ab][xy]$` but this project's output varied run to run
(sometimes matching, sometimes a full wildcard) depending on Python's per-process string
hash randomization, since that affected the arbitrary order the (since-replaced —
see "Determinism and reproducibility") `SetToSeq` handed samples to tier 1's
order-building heuristic — which motivated the positional-split tier (see
"Design: positional split"); `TestPositionalSplitOnIndependentAlternationAxes` in
`Tests.dfy` covers this one. A variable-length version of the same shape
(`{"ax","bx","ayy","byy"}`) was a further, related gap fixed by generalizing the
positional split beyond its original same-total-length restriction (see "Design:
positional split") — but note `grex`'s own answer for that one (`^[ab](?:yy|x)$`) is
*not* single-occurrence itself (`y` appears twice, spelled `"yy"`), so `compare_grex.py`
correctly reports nothing to compare there; it's checked directly with `Matches` in
`TestPositionalSplitVariableLength` instead. (Also worth knowing: `grex` silently drops the empty string
`""` when it
appears alongside other, non-empty inputs, e.g. `grex -- "" "a"` prints `^a$`, which does
not actually accept `""` — so this script excludes `""` from its generated fuzz cases and
doesn't compare sets mixing `""` with other strings.)

Beyond `compare_grex.py`'s reach entirely: after thousands of trials across both plain
random fuzzing and a template-based generator biased toward nested prefix/choice/repeat
structures found zero further mismatches in the "`grex` output happens to be
single-occurrence" comparable space, a hand-crafted case outside that space —
`{"abab","acac"}` — turned up a real gap: both periodic with period 2, sharing `a` at
even positions but differing (`b` vs `c`) at odd positions, this collapsed to a full
wildcard `[abc]*` rather than the tight `(?:a(?:b|c))+`, because tier 2 could previously
only ever propose one fixed *literal* block, never a block with its own internal choice.
`grex`'s own answer here (`^a(?:bab|cac)$`) is not single-occurrence either (`a` appears
twice), so this was checked directly with `Matches`, not `compare_grex.py` — see
`TestPeriodicBlockWithChoice`/`TestPeriodicBlockWithThreeWayChoice` in `Tests.dfy`. Fixed
by generalizing tier 2 to allow a per-position choice within the repeated block (see
"Tier 2 (periodic block, with per-position choice)" above).
