// A bigram-graph based alternative algorithm for inferring a single-occurrence regular
// expression (SORE) from a finite set of sample strings. This is a SEPARATE, standalone
// implementation from the tiered heuristic in Chain.dfy/Infer.dfy - it must not be
// confused with, or share machinery with, that pipeline (only the shared Regex core in
// Regex.dfy is reused).
//
// The planned algorithm, in full (only step 1 is implemented in this file so far):
//
//   1. Build a bigram graph: nodes are the symbols occurring in the input strings, plus
//      sentinel start/end nodes attached to the start/end of every string; draw an edge
//      a -> b if some input string contains the substring "ab" (and edges connecting the
//      sentinels to the first/last symbol of every string, or directly to each other for
//      the empty string).
//   2. Repeatedly apply "lossless" contractions until none apply:
//        2.1 simple-path contraction: a linear a -> b (b's only parent, a's only child)
//            becomes one node labeled "ab" (their labels concatenated);
//        2.2 same-parents/same-children merge: nodes with identical predecessor and
//            successor sets become one OR node (a|b);
//        2.3 optional contraction: if every parent of a node connects directly to every
//            one of its children (a bypass edge), the node becomes optional and those
//            bypass edges are removed.
//   3. Contract every strongly connected component (SCC) into a single node whose label
//      accepts any combination of the SCC's symbols (an over-approximating "loop" regex).
//   4. Re-exhaust the lossless contractions from step 2 on the resulting DAG.
//   5. If not fully contracted, do a "lossy" OR-merge: pick two nodes in the same
//      topological layer with the largest parent/child overlap, merge them into an OR
//      node (like 2.2, but without requiring exact overlap), then re-exhaust step 2.
//   6. Once no more contractions apply, the graph should be a single chain; wrap every
//      remaining node's label in Opt and concatenate them in chain order.
//   7. The single remaining node's label is the final regex.
//
// The eventual goal is a Dafny implementation of this whole pipeline, proved to (a)
// accept every input string (soundness) and (b) produce a single-occurrence regex
// (soreness, i.e. IsSore), passing the same behavioral tests the existing Infer passes.
//
// ROUND 1 implemented step 1 - the graph representation, the language a graph defines
// (walks from start to end, matched piecewise by each visited node's Regex label), the
// two invariants (AllLabelsSore, PairwiseDisjointLabels) that will make the final
// single-node result's IsSore provable "for free" once later rounds build the rest of
// the pipeline (any Concat/Union composition of labels drawn from a graph satisfying
// both invariants stays IsSore, by repeated application of the already-proven
// SymbolsDisjointIsSore in Regex.dfy) - and the bigram-graph construction itself, proved
// to satisfy all of the above and to accept every input string.
//
// ROUND 2 implements step 2.1, simple-path contraction: if x has exactly one outgoing
// edge (to y) and y has exactly one incoming edge (from x), and neither is a sentinel
// and they don't form a 2-cycle (that case belongs to the later SCC-contraction round,
// not this one), merge them into one node labeled Concat(labels[x], labels[y]).
// ContractSimplePathGraph builds the contracted graph; ContractSimplePathWF/
// ContractSimplePathAllLabelsSore/ContractSimplePathPairwiseDisjoint prove it preserves
// well-formedness and both invariants; ContractSimplePathSound proves it preserves
// GraphAccepts for every string (the direction that matters: anything the old graph
// accepted, the new graph still accepts - it may accept more, which is fine, same
// "sound but possibly over-approximating" spirit as the existing tiered Infer
// implementation in Chain.dfy/Infer.dfy, which this file is otherwise unrelated to).
//
// ROUND 3 implements step 2.2 in a GENERALIZED form: an OR-merge of any two distinct,
// non-sentinel, non-adjacent nodes a, b (no edge directly between them in either
// direction, and neither has a self-loop), merging them into one node labeled
// Union(labels[a], labels[b]) and redirecting every edge that touched a or b (from
// EITHER side - the edge sets of a and b are unioned, not assumed equal) to/from the
// merged node instead. This does not require Preds(g,a) == Preds(g,b) or
// Succs(g,a) == Succs(g,b) at all: the textbook "same parents/same children" OR-merge
// (algorithm step 2.2 as originally stated) is simply the special case where a and b
// happen to share all their parents and children - CanMergeAny/MergeAnyGraph subsume it
// directly, with no separate predicate or construction needed for that case. The
// generality matters for a later "lossy" merge step (step 5), which needs to merge
// nodes that only PARTIALLY overlap in parents/children. Like the original relabeling
// technique this round started from, this does not shrink the walk - it relabels every
// occurrence of a or b (at the same position) to the merged node id; the union (rather
// than reuse of just one side's edges) in MergeAnyGraph's into_m/outof_m construction is
// exactly what makes this valid even when a and b's neighborhoods differ. One genuine
// new proof obligation versus the exact-overlap case: without Preds/Succs equality, a
// self-loop on a or b can no longer be ruled out as a CONSEQUENCE of the other
// conditions (the original NoSelfLoopOnMergeCandidates lemma derived it from the
// equality), so CanMergeAny instead states it directly as a precondition ((a,a) and
// (b,b) both not in g.edges) - without it, into_m/outof_m could produce an edge whose
// endpoint is the just-removed node a or b instead of the merged node m. MergeAnySound
// proves the whole construction preserves GraphAccepts for every string.
//
// ROUND 4 implements step 2.3, optional contraction: if a non-sentinel node v has at
// least one parent, at least one child, and EVERY parent has a direct "bypass" edge to
// EVERY child, wrap v's label in Opt and remove those bypass edges. This is the
// opposite shape from the other contractions - it removes edges, so old walks that used
// a bypass edge directly (skipping v) are no longer walks in the new graph, and instead
// a NEW walk that INSERTS v at that point (using Opt's own ability to match "") is
// needed - so this round's walk-transform (InsertOptional/InsertOptionalSplits) GROWS
// the walk by one step at every bypass point, rather than shrinking or relabeling it.
// MakeOptionalSound proves this preserves GraphAccepts for every string.
//
// ROUND 5 implements step 3, SCC contraction - with a scope simplification: proving
// this sound does NOT require proving the contracted node-subset C is a genuine,
// maximal strongly-connected-component of the graph (that's a separate, purely
// heuristic/precision concern about WHICH C a real pipeline should choose to contract,
// e.g. via Tarjan's algorithm - not attempted here, same "propose a candidate
// heuristically, prove whatever was proposed is sound" separation of concerns this
// whole project uses throughout). Soundness holds for contracting ANY nonempty subset
// C of non-sentinel nodes into one node labeled Star(UnionAllLabels(g,C)) - an
// over-approximating "any combination of C's labels" regex - regardless of whether C
// is strongly connected. Edges entirely within C are removed (absorbed into the new
// node); edges crossing into/out of C are redirected to/from it; edges entirely
// outside C are untouched. The walk-transform (CollapseRuns/SkipCRun) collapses every
// MAXIMAL contiguous run of C-membership in a walk into a single visit to the new
// node - a genuinely new shape compared to Rounds 2-4 (which each handled a FIXED
// number of steps: 2 shrinking to 1, 1-for-1 relabeling, or 1 growing to 2); here the
// run length is unbounded, so StarOfUnionAccepts builds up Star's acceptance of the
// whole run one step at a time via induction. ContractSCCSound proves the contraction
// preserves GraphAccepts for every string.
//
// ROUND 6 adds an always-available fallback, not one of the original seven numbered
// steps: the described algorithm expects steps 2-5 to always bottom out in a single
// interior node (a clean chain), but proving that classification claim about this
// specific rule set in general is a hard combinatorial fact, not attempted here. Instead,
// CollapseAllGraph collapses EVERY remaining interior node into one node in a single
// step, regardless of the graph's structure (connected, disconnected, cyclic, acyclic,
// whatever), guaranteeing the pipeline can always reach a single interior node in one
// more step whenever it gets stuck - the same role Chain.dfy/Infer.dfy's final
// Star(a1|...|an) wildcard tier plays in that OTHER, unrelated pipeline, though this
// implementation stays standalone and shares no machinery with it. This turns out to be
// almost free: CanContractSCC(g, C) (Round 5) never actually required C to be a genuine
// strongly-connected-component - its precondition is just "C is a nonempty subset of
// g's non-sentinel nodes" - so C := InteriorNodes(g) satisfies it trivially, and
// CollapseAllGraph/CollapseAllWF/CollapseAllAllLabelsSore/CollapseAllPairwiseDisjoint/
// CollapseAllSound are all thin wrappers around the already-proven ContractSCCGraph/WF/
// AllLabelsSore/PairwiseDisjoint/Sound, with no new walk-transform reasoning needed at
// all. This round also proves the "last mile" fact SingleInteriorNodeAccepts: once a
// graph has been reduced to one interior node m (with g.start/g.end still carrying their
// original Eps labels and no leftover start->end bypass edge - true throughout this
// whole pipeline, since no round ever touches a sentinel's label or set), GraphAccepts
// collapses directly to Matches(g.labels[m], w), no more walk/graph reasoning needed -
// proved via SingleInteriorWalkShape, which shows the start-to-end walk is forced to be
// exactly [g.start, m, g.end] once g.edges contains only the two edges connecting them
// through m.
//
// Steps 4-7 (re-exhausting lossless contractions, lossy OR-merge, and the final chain
// wrap) are future work, not attempted here - EXCEPT that Round 3's OR-merge
// (CanMergeAny/MergeAnyGraph) was generalized, in this same round's slot, to already
// cover the "merge without requiring exact overlap" construction step 5 needs, and Round
// 6 (above) added the always-sound fallback that makes reaching a single interior node
// unconditional; what is still missing for step 5 is the heuristic candidate-selection
// logic (same topological layer, largest parent/child overlap) and re-exhausting step 2
// afterwards, not the merge-and-prove-sound machinery itself.
//
// A proof-tractability gotcha worth knowing for future rounds, hit while generalizing
// Round 3: a StepsOk-shaped ensures clause written as
// `ensures var lo := splits[i]; var hi := splits[i+1]; lo <= hi <= |w| && Matches(...)`
// is NOT reliably closed just by asserting its unpacked pieces separately (e.g.
// `assert splits[i] <= splits[i+1] <= |w|;` then `assert Matches(g.labels[walk[i]], ...)`
// with the label/index equalities asserted alongside) - the solver can fail to re-fold
// those separate facts back through the `var lo := ...; var hi := ...;` bindings into
// the exact shape the ensures clause names. The fix is to rebind the SAME `lo`/`hi`
// (`var lo := splits[i]; var hi := splits[i + 1];`) inside the proof body and finish with
// one final `assert Matches(g'.labels[walk'[i]], w[lo..hi]);` stated against those exact
// bound names - see MergeAnyStepsPreserves's last forall block.
//
// A reusable technique worth knowing about for those future rounds: the soundness
// induction (ContractStepsPreserves) bundles the "walk validity + per-index splits
// match" facts into one named predicate (StepsOk) with a single "drop the first step"
// lemma (StepsOkDropFirst) proved once, rather than re-deriving shifted-index
// (splits[i+1], splits[i+2], ...) reasoning separately at every call site with ad hoc
// {:trigger} annotations - the latter was tried first and repeatedly hit brittle
// quantifier-instantiation failures (a fact proved as three separate per-index
// universally-quantified requires/ensures clauses turned out to be far harder for the
// solver to chain across shifted indices than the same three facts bundled into one
// predicate's conjunction, matched by ensuring any two facts that need to be used
// together - like a bound check and the Matches call it justifies - live in the SAME
// forall's body via a `var lo := ...; var hi := ...;` binding, exactly like WalkMatches
// itself already does, rather than as separate top-level quantifiers).
//
// ROUND 7 wires Rounds 1-6's ghost-only machinery into an actual, executable, tested
// top-level method: InferViaBigramGraph(S: set<string>) returns (r: Regex), with
// `ensures forall w :: w in S ==> Matches(r, w)` (soundness) and `ensures IsSore(r)`
// (soreness) as its only postconditions - both already proved, just finally attached to
// something that runs. Precision/tightness is deliberately NOT this round's goal: the
// strategy is the simplest one that terminates and is provably sound - repeatedly apply
// whichever of the three easy, decidable contractions (simple-path, general OR-merge,
// optional - via the executable search methods FindSimplePathPair/FindMergePair/
// FindOptionalNode, in that priority order) is currently findable, and fall back to
// CollapseAllGraph (Round 6) whenever none of the three applies and interior nodes
// remain, which can make the result looser than a real SCC-detection pass would produce
// on genuinely cyclic input. Real SCC-detection (e.g. Tarjan's algorithm) to tighten
// results on cyclic inputs remains deferred future work, exactly as Round 5/6 already
// said - CollapseAllGraph's soundness proof never needed genuine strong connectivity,
// so nothing here does either.
//
// Two new mechanical difficulties came with actually executing this, neither present in
// Rounds 1-6's pure-ghost setting:
//
// (a) ContractSimplePathGraph/MergeAnyGraph/MakeOptionalGraph/ContractSCCGraph/
//     CollapseAllGraph are all `ghost function`s (their fresh-node allocation goes
//     through FreshNode/SetMax, which pick a set element via `:|` inside a *function*
//     body - Dafny only compiles that inside *methods*, where the picked witness need
//     not be uniquely determined). Rather than touch any of that already-proven ghost
//     code, this round adds a parallel EXECUTABLE construction for each transform
//     (ExecContractSimplePath/ExecMergeAny/ExecMakeOptional/ExecCollapseAll) that
//     computes the identical graph value at runtime, bridged to its ghost counterpart
//     via plain equality (ExecFreshNode + ExecFreshNodeIsFreshNode establish the
//     executable fresh-node search returns the exact same value as the ghost FreshNode,
//     via SetMax's uniqueness) - once that equality holds, every already-proven Round
//     1-6 lemma applies directly to the executable result by substitution. The one
//     exception is ExecCollapseAll: its merged node's label is a Union over SOME
//     enumeration of InteriorNodes(g), and the executable enumeration (SetToSeqExec)
//     can legitimately differ in ORDER from the ghost SetToSeq's (also `:|`-based, and
//     just as unpredictable) - so exact equality to CollapseAllGraph(g) isn't provable.
//     Instead, WF/AllLabelsSore/PairwiseDisjointLabels/NoBackEdges/single-occurrence are
//     all reproved directly (each already had a fully order-generic proof available -
//     UnionAllLabelsIsSore/UnionAllLabelsSymbolsMem take an arbitrary enumeration as a
//     parameter already, no ghost-function detour needed), and GraphAccepts
//     preservation is transported from the ghost CollapseAllGraph via a new, reusable
//     fact (GraphAcceptsRelabelEquiv): two graphs that agree on everything except one
//     node's label, and even there only up to Matches-equivalence, accept exactly the
//     same strings - proved once, generically, rather than re-deriving the whole SCC
//     walk-collapsing induction a second time for an arbitrary enumeration.
//
// (b) SingleInteriorNodeAccepts (Round 6) needs the final single-interior-node graph's
//     edges to be EXACTLY {(start,m),(m,end)} - not automatically true of whichever node
//     ends up last, for two independent reasons: a self-loop can survive untouched if it
//     was already there in the very first bigram graph (e.g. S = {"aa"}) and the loop
//     never happens to run a set-contraction over that node; and a direct start->end
//     "bypass" edge can coexist with m whenever "" is a sample alongside non-empty ones.
//     Both are resolved by a small canonicalization step once the main loop reaches one
//     interior node (FinishSingleInteriorNode): a self-loop is cleared by one more
//     CollapseAllGraph application (contracting the singleton {m}, which - as a
//     consequence of the SAME freshness argument from (a) - always produces a
//     self-loop-free node); a bypass is cleared by one more MakeOptionalGraph
//     application, licensed by a new structural invariant, NoBackEdges(g) (no edge
//     targets g.start, no edge sources g.end - true of the base bigram graph and
//     preserved by every contraction "for free" from fresh-node-ness alone, so it costs
//     almost nothing to carry as a loop invariant) - combined with the fact that some
//     sample string is non-empty, whose accepted walk is then forced to pass through the
//     sole interior node, pinning down both edges unconditionally (FinalNodeHasNeighbors/
//     FinalGraphEdgesEnumerated/FinalNodeCanMakeOptional).
//
// The termination measure is lexicographic (|InteriorNodes(g)|, |g.edges|): simple-path,
// merge and CollapseAll all strictly shrink the interior-node count (by exactly one for
// the first two, straight down to exactly one for the third - InteriorNodesContractSimplePath/
// InteriorNodesMergeAny/InteriorNodesCollapseAll), while optional-contraction leaves the
// node count unchanged but strictly shrinks the edge count instead (EdgeCountMakeOptional)
// - a decreases clause of |InteriorNodes(g)| alone would not have proved termination for
// that one branch, since MakeOptionalGraph only ever removes bypass edges, never a node.
//
// GraphTests.dfy (a separate, standalone file, not included here) exercises
// InferViaBigramGraph end to end via `{:test}` methods and `dafny test --target:js`,
// the same mechanics this project's OTHER, unrelated implementation already uses in
// Tests.dfy - confirming it actually runs, terminates, and matches its own postconditions
// on concrete inputs (including ones chosen specifically to exercise the two
// canonicalization steps from (b): a repeated character forcing a self-loop, and a mix
// of "" with non-empty samples forcing a bypass edge).
//
// A verification-robustness note for future rounds, worth knowing given how much of this
// round's debugging time went here: several proof obligations elsewhere in this file
// (pre-dating this round, never touched by it - e.g. inside ContractStepsPreserves,
// MergeAnyStepsPreserves, CollapseStepsPreservesRun) turned out to verify fine under
// `dafny verify` but intermittently fail under `dafny build`/`dafny test` on the exact
// same source, REGARDLESS of `--verification-time-limit` or `--cores` (ruling out a
// simple time/resource-contention explanation) - a form of solver instability apparently
// sensitive to the overall proof/lemma population of the file, not specific to anything
// this round added. The fix that actually worked, in every case, was making the
// suspect step's quantifier instantiation fully explicit rather than relying on Z3 to
// auto-instantiate an ambient `requires StepsOk(...)`-shaped hypothesis from inside a
// nested `forall`: a small dedicated lemma, StepsOkAt(g, walk, splits, w, i), restates
// StepsOk's per-index fact at one fixed, concrete index (trivial to prove on its own),
// and calling it explicitly at each use site removed the instability entirely. If a
// `dafny verify`-clean proof involving StepsOk/ValidSteps-shaped foralls ever starts
// failing only under `dafny build`/`dafny test`, reach for this pattern first.
//
// ROUND 8 closes the gap Round 7's own header explicitly left open: the driver never
// looked for a genuine cycle before giving up and collapsing the ENTIRE remaining
// interior via CollapseAllGraph, which over-approximates whenever a cycle is only a
// PROPER SUBSET of what's left (the rest being an already-acyclic DAG that the ordinary
// simple-path/merge/optional rules could otherwise keep whittling down on their own).
// This round adds a real, executable, reachability-based cycle finder -
// Reachable/ReachableBackward (plain forward/backward reachability fixpoints, growing a
// `visited` set until no new nodes are added, terminating because `g.nodes - visited`
// strictly shrinks each step) and SCCCandidate(g, x) := the intersection of everything x
// can reach and everything that can reach x, restricted to interior nodes (excluding the
// sentinels, which - as the task that spawned this round warned - are typically
// reachable/co-reachable from every node, so must be filtered out before ever being
// handed to CanContractSCC, whose precondition forbids them). Proving SCCCandidate is a
// genuine, maximal, closed-under-mutual-reachability strongly-connected component is NOT
// attempted (and not needed): exactly as Round 5/6 already established, CanContractSCC's
// precondition is just "nonempty subset of interior nodes" - nothing about actual strong
// connectivity - so SCCCandidateProps only proves the (much easier) membership/subset
// facts that precondition actually requires, matching this file's established
// "propose a candidate heuristically, prove whatever was proposed sound" approach.
// FindNontrivialSCC searches interior nodes for the first one whose SCCCandidate has
// size >= 2 (a genuine multi-node cycle); single-node self-loops are deliberately NOT
// treated as "nontrivial" here, since contracting a singleton leaves the interior-node
// count unchanged and would need a whole new edge-count-based termination argument for no
// behavioral benefit - every self-loop case this project exercises (S = {"aa"}) already
// reduces to a single interior node before the main loop even runs, and is already
// handled unconditionally by FinishSingleInteriorNode's own self-loop canonicalization
// step (Round 7). The driver tries FindNontrivialSCC right before the CollapseAllGraph
// fallback (after FindSimplePathPair/FindMergePair/FindOptionalNode, unchanged in
// priority): those three are cheap, purely local, reachability-search-free checks, so
// they stay tried first exactly as before; only once none of them applies does it make
// sense to pay for a whole-graph reachability search, and doing so before reaching for
// the wildcard CollapseAllGraph is strictly better whenever a genuine proper-subset
// cycle remains, while costing nothing when no such cycle exists (CollapseAllGraph still
// fires exactly as before in that case). ExecContractSCC generalizes Round 7's
// ExecCollapseAll from C := InteriorNodes(g) to an arbitrary C satisfying
// CanContractSCC(g, C) - every one of ExecCollapseAll's supporting lemmas
// (…SoreDisjoint/…NoBackEdges/…Sentinels/…SoundOne) turned out to already be fully
// generic in C, with only one new lemma needed (ExecContractSCCInterior, replacing
// ExecCollapseAllInterior's C-specific "InteriorNodes(g2) == {m}" with the general
// "InteriorNodes(g2) == InteriorNodes(g) - C + {m}", proved directly off the executable
// construction's own node-set formula via a new CardRemoveSubset lemma generalizing
// CardRemoveTwo to an arbitrary-size subset). Termination for the new branch reuses the
// SAME first-component argument as simple-path/merge/CollapseAll (contracting |C| >= 2
// nodes strictly shrinks |InteriorNodes(g)|, by exactly |C| - 1), so the loop's existing
// lexicographic (|InteriorNodes(g)|, |g.edges|) measure needs no change at all.
//
// A worked example confirming the gap was real (empirically checked, not just assumed,
// before writing any of the above): S = {"abab"} produced Star(Union(Sym('a'),Sym('b')))
// - i.e. (a|b)* - both before AND after this round, since that particular input's bigram
// graph has ONLY the two cycle nodes as its entire interior (no other structure), so
// contracting "just the cycle" there happens to equal contracting everything; the
// genuine, empirically-verified tightening this round buys shows up instead on an input
// where the cycle is a PROPER subset of the remaining interior - see
// GraphTests.dfy's TestNontrivialSCCTightening.
//
// ROUND 9 fixes a genuine precision bug found by direct testing (not a hypothesis):
// InferViaBigramGraph({"ax", "ayyy", "bbx", "bbyyy"}) produced
// Star(Union(Union(Union(Sym('a'),Sym('x')),Sym('y')),Sym('b'))) - i.e. [axyb]*, a full
// wildcard - wrongly accepting "a" alone, "x" alone, "abbx" (mixing a and bb), etc. Root
// cause: this input's bigram graph gives node 'b' a self-loop (b,b) (from the consecutive
// "bb" in "bbx"/"bbyyy"). Every contraction rule up through Round 8 explicitly EXCLUDES
// self-looped nodes from its precondition (CanContractSimplePath, CanMergeAny,
// CanMakeOptional all require (v,v) !in g.edges for the node(s) involved), and
// FindNontrivialSCC deliberately does not treat a lone self-loop as a "nontrivial SCC"
// worth contracting (only genuine multi-node cycles, |C| >= 2 - see Round 8's comment).
// So whenever a self-loop shows up on a node that ISN'T the last one standing, the driver
// has no small rule that applies to it, falls through to CollapseAllGraph, and the
// self-loop poisons the ENTIRE remaining graph into one big wildcard - destroying
// recoverable structure on totally unrelated nodes ('a', 'x', 'y' above) that had nothing
// to do with the self-loop.
//
// The fix: a new small contraction, CanLoopToPlus/LoopToPlusGraph - if a node v has a
// self-loop (v,v), replace its label with Plus(labels[v]) and remove just that one edge.
// This captures "one or more repetitions of v's own current label" without merging v with
// anything else, and - crucially for termination - shrinks |g.edges| by exactly 1 while
// leaving |g.nodes|/|InteriorNodes(g)| completely unchanged, exactly like the existing
// MakeOptionalGraph (which also only ever shrinks edges, not nodes): the driver's existing
// lexicographic (|InteriorNodes(g)|, |g.edges|) termination measure needs no change,
// EdgeCountLoopToPlus is simply another |edges|-reducing case alongside
// EdgeCountMakeOptional.
//
// One genuine wrinkle CanLoopToPlus's precondition must rule out, beyond what the task
// description originally sketched: LoopToPlusSound needs every individual repetition
// piece in a collapsed run to be NON-EMPTY, because Plus's own definition
// (Regex.dfy) can never match "" even when its argument is nullable (its existential
// requires a strictly positive split index) - so if v's label matched "" and an entire
// maximal run of v happened to contribute nothing to the string, collapsing that run to
// one Plus(labels[v]) step would be unsound (nothing could witness matching ""). This is
// ruled out by requiring !Matches(g.labels[v], "") in CanLoopToPlus, which costs nothing
// in practice: a self-loop can only ever survive on a node whose label is still its
// original bigram-graph Sym(c) (every one of Rounds 2-4's relabeling rules already
// excludes self-looped candidates from its own precondition, and Round 5/6's set
// contraction absorbs a self-looped node's self-loop, if included, entirely into the
// merged Star node rather than leaving it on a surviving node) - and Sym(c) never matches
// "". PlusOfRunAccepts (peeling one repetition off as Plus's own existential witness, then
// reusing the already-proven StarOfUnionAccepts verbatim - instantiated at the singleton
// C := {v}, cs := [v], since UnionAllLabels(g, [v]) reduces to exactly g.labels[v] - for
// the rest) proves this formally; LoopStepsPreserves/…Untouched/…Run are the walk-transform trio, mirroring
// CollapseStepsPreserves/…Untouched/…Run's shape but simpler (v keeps its own identity, no
// fresh node, no into_m/outof_m redirection - only the removed self-loop edge itself needs
// distinguishing), reusing the SCC section's already-fully-generic SkipCRun/CollapseRuns/
// CollapseSplits/SkipCSplits/RunIsAllC/SkipCSplitsIsSuffix/CollapseRunsFirstUnchanged/
// CollapseRunsLastUnchanged/SkipCRunHeadNotInC verbatim with C := {v}, m := v.
//
// Driver placement: FindSelfLoopNode is tried right after FindSimplePathPair, before
// FindMergePair/FindOptionalNode/FindNontrivialSCC/CollapseAllGraph. Rationale: resolving
// a self-loop eagerly is exactly what lets MergeAny/FindOptionalNode/FindNontrivialSCC do
// useful work on a formerly-self-looped node afterwards (in the motivating example above,
// turning 'b' into Plus(Sym('b')) immediately lets the driver's other rules go on to
// isolate 'x'/'y' cleanly instead of everything getting swallowed by CollapseAllGraph) -
// and it is just as cheap as the other purely-local, reachability-search-free checks
// (FindSimplePathPair/FindMergePair/FindOptionalNode), so there is no cost to trying it
// early; placing it any later would let a merge/optional/SCC step fire on some other part
// of the graph first while the self-loop keeps poisoning whatever eventually reaches
// CollapseAllGraph.
//
// After this fix, InferViaBigramGraph({"ax", "ayyy", "bbx", "bbyyy"}) produces
// Concat(Union(Sym('a'),Plus(Sym('b'))),Union(Sym('x'),Plus(Sym('y')))) - i.e.
// (a|b+)(x|y+) - which still accepts "ax"/"bbx"/"ayyy"/"bbyyy" but correctly rejects "a",
// "x" and "abbx" (confirmed empirically; see GraphTests.dfy's TestSelfLoopToPlusTightening).
//
// ROUND 10 fixes another genuine precision bug found by direct testing (empirically
// confirmed via a scratch comparison probe, not a hypothesis):
// InferViaBigramGraph({"abc", "adc"}) produced a full wildcard over {a,b,c,d} - wrongly
// accepting "ac", "abdc", and "abbc", none of which are inputs. Root cause: in this
// input's bigram graph, nodes 'b' and 'd' happen to have IDENTICAL predecessor sets
// ({a}) and IDENTICAL successor sets ({c}) - the textbook "same parents/same children"
// OR-merge (algorithm step 2.2 as originally stated) applies to them directly, and
// merging them via CanMergeAny(g,b,d) (safe: Union(Sym(b),Sym(d)), matching either b's
// or d's role at that exact spot) would give a properly structured a(b|d)c. But
// FindMergePair (Round 7) just searches for ANY pair satisfying the bare CanMergeAny
// precondition - any two non-adjacent, non-self-looped, non-sentinel nodes - with no
// preference at all for a "safe/meaningful" pair like b/d over an "arbitrary,
// structurally-unrelated" pair like a and c (which ALSO happens to satisfy CanMergeAny's
// bare precondition, since there is no direct edge a-c either): depending on search
// order, FindMergePair could just as easily return (a,c) first, destroying the
// a-then-c ordering and cascading into a much worse overall result once the rest of the
// pipeline is forced to paper over the damage via CollapseAllGraph. This is exactly the
// distinction the algorithm this project is based on draws between step 2.2
// ("same parents/children merge" - a safe, lossless contraction, tried early/eagerly)
// and step 5 ("lossy merge" - explicitly a LAST RESORT, tried only once literally
// everything else, including step 3's SCC-contraction, has been exhausted); Round 7's
// driver conflated both into one generic, unprioritized FindMergePair search.
//
// The fix: a new predicate, CanMergeExact(g,a,b) := CanMergeAny(g,a,b) &&
// Preds(g,a) == Preds(g,b) && Succs(g,a) == Succs(g,b) (Preds/Succs already existed from
// Round 3), and a new executable search, FindExactMergePair, built in the exact same
// iteration-based style as FindSimplePathPair/FindMergePair/FindOptionalNode - no new
// contraction machinery, WF/AllLabelsSore/PairwiseDisjointLabels/soundness proof, or
// termination argument was needed at all: CanMergeExact implies CanMergeAny directly
// from its own definition, so the already-proven MergeAnyGraph/MergeAnyWF/
// MergeAnyAllLabelsSore/MergeAnyPairwiseDisjoint/MergeAnySound/InteriorNodesMergeAny/
// LoopStepMergeAny all apply completely unchanged to a CanMergeExact pair - this round
// is purely about search PRIORITY, not a new kind of graph transformation, exactly as
// the task that motivated it anticipated.
//
// Driver placement (the loop in InferViaBigramGraph now tries, in this order,
// restarting from the top after any successful contraction): (1) FindSimplePathPair,
// (2) FindSelfLoopNode, (3) FindExactMergePair (NEW), (4) FindOptionalNode,
// (5) FindNontrivialSCC, (6) FindMergePair (the old bare/arbitrary CanMergeAny search,
// now DEMOTED to here), (7) CollapseAllGraph (final fallback, unchanged). Rationale:
// FindExactMergePair is exactly as cheap and purely local as
// FindSimplePathPair/FindSelfLoopNode/FindOptionalNode (a double loop over nodes
// checking a decidable predicate, no reachability search), so it costs nothing to try
// eagerly alongside them, and doing so before FindOptionalNode/FindNontrivialSCC matters
// empirically: resolving an exact-overlap pair first can expose new simple-path/optional
// opportunities on the merged node exactly the way Round 9's self-loop-to-Plus ordering
// argument already established for that rule. FindNontrivialSCC stays right before the
// demoted FindMergePair (rather than after it): a genuine cycle is real, load-bearing
// structure discoverable independently of node overlap, so it is strictly better to
// isolate a real SCC before ever resorting to an arbitrary, no-overlap-guarantee merge -
// symmetric to how Round 8 already placed SCC-detection before the (then only) merge
// search. FindMergePair itself is kept as the LAST option tried before CollapseAllGraph,
// exactly matching the source algorithm's step 5 ("lossy merge... last resort"): every
// safer, more structure-preserving option (simple-path, self-loop, exact-overlap merge,
// optional, SCC) has already been exhausted by the time it is reached. The termination
// measure (|InteriorNodes(g)|, |g.edges|) needs no change: an exact-overlap merge is
// still just a MergeAnyGraph application under the hood (InteriorNodesMergeAny already
// proves the interior-node-count reduction), so this round only changes WHEN that
// existing transformation is tried, never what it does.
//
// Empirically confirmed before/after via a scratch comparison probe (see GraphTests.dfy's
// TestAbcAdc, which now also checks the three counterexamples): before this round,
// InferViaBigramGraph({"abc", "adc"}) produced Star(Union(Union(Sym('a'),Sym('c')),
// Union(Sym('b'),Sym('d')))) - i.e. [acbd]*, a full wildcard over {a,b,c,d} - wrongly
// accepting "ac", "abdc", "abbc" (none of which are inputs). After this round it instead
// produces Concat(Concat(Sym('a'),Union(Sym('b'),Sym('d'))),Sym('c')) - i.e. a(b|d)c -
// which still accepts "abc"/"adc" but correctly rejects all three. Two other inputs from
// this project's history were also re-checked: {"cat", "car", "cab"}'s bigram graph
// already gives 't'/'r' identical parents ({a}) and identical children ({end}), and
// happened to already produce the same tight Concat(Concat(Sym('c'),Sym('a')),
// Union(Sym('b'),Union(Sym('t'),Sym('r')))) - i.e. ca(b|t|r) - correctly rejecting "ca",
// "catr", "catb" - both BEFORE and after this round (the old unprioritized FindMergePair
// happened, by search-order luck, to land on the same b/t/r-shaped result here; this
// round now gets there for a principled reason - FindExactMergePair - rather than by
// chance, so the result is no longer order-dependent). {"ABCDE", "ACDE", "ABE"}'s bigram
// graph, by contrast, has NO pair of nodes with identical predecessor AND successor sets
// even after its own simple-path contraction (C/D) fires, so FindExactMergePair never
// applies there and the result is unchanged before/after this round - still close to a
// full wildcard via the demoted FindMergePair/CollapseAllGraph. Tightening that case
// would need a genuinely different heuristic (e.g. step 5's original "largest overlap"
// candidate selection, choosing the LEAST damaging arbitrary pair rather than merely
// deprioritizing the search that finds one) - RESOLVED by Round 11 below.
//
// ROUND 11 finally implements the original algorithm's step 6 (this file's header above
// had, since Round 6, only ever implemented a blunter catch-all - CollapseAllGraph's
// "collapse literally everything remaining into one Star(Union(...)) wildcard node" -
// in its place, explicitly flagged there as future work). The gap this closes, found by
// direct testing: InferViaBigramGraph({"B", "C", "BC"}) produced the full wildcard
// Star(Union(Sym('B'),Sym('C'))) - i.e. [BC]* - wrongly accepting "CB", even though the
// OTHER, unrelated tiered implementation in this project gets the tight B?C? for this
// same input. Root cause: this input's bigram graph has node B with children {C, end}
// and node C with parents {start, B}; the direct edge B->C blocks MergeAny between them,
// C's two parents block simple-path contraction, and CanMakeOptional's precondition (as
// implemented since Round 4) requires a LITERAL bypass edge for every parent/child pair
// of the node being made optional - B's children are {C, end}, and while start->C exists,
// there is no DIRECT edge start->end (since "" was never a sample), even though
// start->C->end already provides the same bypass semantically. So every existing rule is
// stuck, and Round 7-10's driver fell all the way to the wildcard fallback.
//
// The fix: once simple-path/self-loop/exact-merge/optional/nontrivial-SCC-detection have
// ALL been tried and found nothing in a given pass, the remaining graph's interior is
// necessarily acyclic - every possible source of a cycle (a self-loop, or a genuine
// multi-node SCC) has already been ruled out THIS SAME pass by FindSelfLoopNode/
// FindNontrivialSCC, and a directed graph with neither is a DAG by definition. For an
// acyclic graph, ANY topological order of its interior nodes is automatically consistent
// with every walk through it: a walk following real edges can only visit nodes in an
// order compatible with every valid topological order (formally: no edge can ever run
// from a topologically-LATER node back to an earlier one - that is exactly what
// "topological order" means). So wrapping every remaining node in Opt and concatenating
// them in topological order is unconditionally sound, not just for graphs that already
// happen to look like a clean linear chain - the resulting regex accepts any subsequence
// of the topological order that appears in that relative order, which every actual walk's
// visited-interior-node sequence necessarily is (NoBackEdges - already an established
// invariant - pins the sentinels to the very front/back of any walk, so the walk's
// INTERIOR portion is exactly what needs to respect the order).
//
// New machinery: TopoSort(g) is a certifying-algorithm-style executable Kahn's-algorithm
// implementation - it repeatedly picks an as-yet-unplaced interior node with no remaining
// in-edges from other unplaced interior nodes (a decidable, executable check, in the same
// double-loop-over-an-enumeration style as FindSimplePathPair/FindMergePair/
// FindOptionalNode), and returns found := false if it ever gets stuck with nodes left
// over (a genuine cycle - not expected to happen given the priority chain above, but kept
// as a real, working fallback rather than assumed impossible). Its only two ensures
// clauses that matter downstream are a multiset-permutation fact (`order` contains every
// interior node exactly once) and a NO-BACK-EDGE fact stated directly against g.edges
// (for i < j, no edge from order[j] back to order[i]; folding in i == j too, i.e. no
// self-loop on any ordered node, costs nothing extra to prove - it is just the SAME
// "zero in-degree relative to what's still unplaced" check applied to the candidate
// itself - and is exactly what the soundness proof needs to rule out a node "reappearing
// later in a walk via its own self-loop). ChainWrapRegex(g, order) builds
// Concat(Opt(labels[order[0]]), Concat(Opt(labels[order[1]]), ... Eps)); ChainWrapSound
// proves it accepts every string GraphAccepts(g, ·) accepts, via a witness walk stripped
// of its start/end sentinels (StartOnlyAtFront/EndOnlyAtBack, already available since
// Round 7) and handed to ChainWrapAux - an induction over `order` that, at each step,
// either the remaining node-sequence's head equals order's head (consume it: match the
// corresponding piece of the string, recurse on both tails) or it doesn't (skip: order's
// head contributes "" via Opt, recurse with `order` advanced but the node-sequence
// unchanged) - licensed by ChainWrapOrderHeadOnlyAtFront, which shows order's current
// head can only ever occur at position 0 of such a sequence, never later (a later
// occurrence would need a real edge into it from the previous, also order-drawn,
// position, and every possible source of that edge is excluded by the no-back-edge/
// no-self-loop facts above). ChainWrapAllLabelsSore proves IsSore via the same repeated
// SymbolsDisjointIsSore pattern as CollapseAllAllLabelsSore/UnionAllLabelsIsSore (Opt, like
// Plus before it, leaves Symbols unchanged, confirmed against Regex.dfy).
//
// Driver placement: right where the driver previously fell through to CollapseAllGraph
// (after FindNontrivialSCC fails), TopoSort is now tried FIRST; on success,
// ChainWrapRegex(g, order) is the final answer (the loop terminates immediately - no
// further contraction is needed), and CollapseAllGraph is demoted to a defensive
// last-resort, reached only if TopoSort itself somehow fails (shouldn't happen given the
// priority chain, but the fallback path is still fully proven sound, not merely assumed
// unreachable). The old bare/arbitrary FindMergePair search (Round 10's demoted "lossy
// merge, last resort" step) is now DEAD CODE in practice: by the time the driver would
// have reached it, FindSelfLoopNode and FindNontrivialSCC have both already failed THIS
// SAME pass, which is exactly the condition under which TopoSort is mathematically
// guaranteed to succeed (the interior is a genuine DAG) - so control never reaches
// FindMergePair's call site any more. It is removed from the driver's loop entirely
// (rather than kept as extra-defensive dead weight after TopoSort) since leaving it in
// would be actively misleading about the driver's real priority chain; CanMergeAny/
// MergeAnyGraph and FindMergePair's own definition are left completely untouched (still
// used by FindExactMergePair/CanMergeExact, and harmless to leave defined even unused).
//
// Empirically confirmed before/after: InferViaBigramGraph({"B", "C", "BC"}) now produces
// Concat(Opt(Sym('B')),Concat(Opt(Sym('C')),Eps)) - i.e. B?C? - accepting ""/"B"/"C"/"BC"
// and correctly rejecting "CB" (previously accepted by the [BC]* wildcard). On
// {"ABCDE", "ACDE", "ABE"} (previously "close to a full wildcard", per Round 10's own
// comment above), this round now produces Concat(Opt(Sym('A')),Concat(Opt(Sym('B')),
// Concat(Opt(Concat(Sym('C'),Sym('D'))),Concat(Opt(Sym('E')),Eps)))) - i.e. A?B?(CD)?E? -
// which accepts all three samples and correctly rejects "ACBDE"/"ABCDEX"/"ABCE"/"ACDBE".
// This is NOT byte-identical to the other, unrelated tiered implementation's AB?C?D?E for
// this same input (that shape treats A and E as mandatory; this round's chain-wrap always
// wraps EVERY remaining node in Opt, including ones - like A and E here - that happen to
// appear on every walk, so this result also accepts e.g. "BCDE" and "ABCD", which
// AB?C?D?E would reject) - a known, deliberate conservative simplification of the general
// topological chain-wrap (detecting "this particular node is actually mandatory" is a
// separate, harder precision question, not attempted here), but still a dramatic
// tightening versus the wildcard it replaces. {"cat","car","cab"} and {"abc","adc"} are
// both unaffected (resolved earlier by FindExactMergePair, never reaching TopoSort at
// all), confirming no regression on inputs the pipeline already handled well.
module BigramGraph {
  import opened RegexCore

  // Node ids are plain integers so the two sentinels can live outside the range of any
  // character's code point: every character c is assigned the node id (c as int), which
  // is always non-negative (Dafny's char is a Unicode code point, cast to a non-negative
  // int), while the sentinels use the negative ids -1 and -2 - so a character node and a
  // sentinel node can never collide, and distinct characters always get distinct ids
  // (CharNode is injective on char, see CharNodeInjective below).
  const StartId: int := -1
  const EndId: int := -2

  function CharNode(c: char): int {
    c as int
  }

  lemma CharNodeInjective(c1: char, c2: char)
    requires c1 != c2
    ensures CharNode(c1) != CharNode(c2)
  {
    // (c as int) round-trips back to c via (n as char) for any char c, so two distinct
    // chars can never map to the same node id.
    assert (CharNode(c1) as char) == c1;
    assert (CharNode(c2) as char) == c2;
  }

  lemma CharNodeNotSentinel(c: char)
    ensures CharNode(c) != StartId && CharNode(c) != EndId
  {
    // Every char's code point is non-negative, while StartId/EndId are negative.
  }

  // ---- Graph representation ----

  datatype Graph = Graph(
    nodes: set<int>,
    labels: map<int, Regex>,
    edges: set<(int, int)>,
    start: int,
    end: int
  )

  predicate WF(g: Graph) {
    g.start in g.nodes && g.end in g.nodes && g.start != g.end &&
    g.labels.Keys == g.nodes &&
    (forall e :: e in g.edges ==> e.0 in g.nodes && e.1 in g.nodes)
  }

  // A walk is a sequence of (not necessarily distinct - the pre-contraction bigram graph
  // can have cycles and self-loops, e.g. a self-loop on the 'a' node is needed for the
  // input "aa") node ids, starting at g.start, ending at g.end, following real edges.
  predicate IsWalk(g: Graph, walk: seq<int>) {
    |walk| >= 2 &&
    walk[0] == g.start && walk[|walk| - 1] == g.end &&
    (forall i :: 0 <= i < |walk| ==> walk[i] in g.nodes) &&
    (forall i :: 0 <= i < |walk| - 1 ==> (walk[i], walk[i + 1]) in g.edges)
  }

  // w is accepted along this particular walk iff it can be split into |walk| consecutive
  // (possibly empty) pieces, one per walk step, each piece matched by that step's node's
  // Regex label. This is deliberately defined via an existential over an explicit,
  // already-chosen finite witness sequence (splits), NOT via structural recursion on the
  // walk or on the remaining string: a graph with cycles whose labels can match the empty
  // string (e.g. an all-Eps cycle) would make a naive "recurse and decrease on remaining
  // string length" definition not well-founded, since the string need never shrink as the
  // walk revisits nodes. Quantifying over a finite witness sidesteps this - no
  // termination argument is needed at all.
  ghost predicate WalkMatches(g: Graph, walk: seq<int>, w: string)
    requires WF(g)
    requires IsWalk(g, walk)
  {
    exists splits: seq<nat> ::
      |splits| == |walk| + 1 &&
      splits[0] == 0 && splits[|walk|] == |w| &&
      (forall i :: 0 <= i < |walk| ==>
        var lo := splits[i]; var hi := splits[i + 1];
        lo <= hi <= |w| && Matches(g.labels[walk[i]], w[lo..hi]))
  }

  ghost predicate GraphAccepts(g: Graph, w: string)
    requires WF(g)
  {
    exists walk: seq<int> :: IsWalk(g, walk) && WalkMatches(g, walk, w)
  }

  // ---- The two invariants that carry the whole project's soundness+soreness proof ----
  //
  // Once the full pipeline exists, every contraction will need to be shown to preserve
  // both of these; then the FINAL single-node graph's label is IsSore "for free": any
  // Concat/Union composition of labels drawn from a graph satisfying both invariants
  // stays IsSore, by repeated application of the already-proven SymbolsDisjointIsSore
  // (Regex.dfy). This round only establishes both for the freshly built bigram graph.

  predicate AllLabelsSore(g: Graph)
    requires WF(g)
  {
    forall n :: n in g.nodes ==> IsSore(g.labels[n])
  }

  predicate PairwiseDisjointLabels(g: Graph)
    requires WF(g)
  {
    forall n1, n2 :: n1 in g.nodes && n2 in g.nodes && n1 != n2 ==>
      forall c :: Symbols(g.labels[n1])[c] == 0 || Symbols(g.labels[n2])[c] == 0
  }

  // ---- Bigram graph construction ----
  //
  // The proof is split into one lemma per ensures clause (rather than one big inline
  // proof inside the method), each restating the graph's construction as explicit
  // requires clauses on its own constituent pieces - this keeps each verification
  // condition's SMT context small; cramming all four proofs into a single method body
  // timed out even at a 6x time-limit multiplier.

  function Alphabet(S: set<string>): set<char> {
    set w, i | w in S && 0 <= i < |w| :: w[i]
  }

  function NodesOf(alphabet: set<char>): set<int> {
    {StartId, EndId} + (set c | c in alphabet :: CharNode(c))
  }

  function LabelsOf(alphabet: set<char>): map<int, Regex> {
    map[StartId := Eps, EndId := Eps] + (map c | c in alphabet :: CharNode(c) := Sym(c))
  }

  function {:opaque} EdgesOf(S: set<string>): set<(int, int)> {
    (set w | w in S && w != "" :: (StartId, CharNode(w[0]))) +
    (set w | w in S && w != "" :: (CharNode(w[|w| - 1]), EndId)) +
    (set w, i {:trigger w[i]} {:trigger w[i + 1]} | w in S && 0 <= i < |w| - 1 ::
       (CharNode(w[i]), CharNode(w[i + 1]))) +
    (if "" in S then {(StartId, EndId)} else {})
  }

  // Opaque so its definition isn't auto-unfolded (and re-triggered) at every use site -
  // that caused genuine solver timeouts, not just slowness, when EdgesOf's double-bound
  // (w, i) comprehension got matched against repeatedly across a large proof context.
  // This lemma is the one place the definition is revealed; everywhere else uses this
  // membership characterization instead.
  lemma EdgesOfMem(S: set<string>, e: (int, int))
    ensures e in EdgesOf(S) <==>
      (exists w :: w in S && w != "" && e == (StartId, CharNode(w[0]))) ||
      (exists w :: w in S && w != "" && e == (CharNode(w[|w| - 1]), EndId)) ||
      (exists w, i :: w in S && 0 <= i < |w| - 1 && e == (CharNode(w[i]), CharNode(w[i + 1]))) ||
      ("" in S && e == (StartId, EndId))
  {
    reveal EdgesOf();
  }

  lemma EdgesOfStartIn(S: set<string>, w: string)
    requires w in S && w != ""
    ensures (StartId, CharNode(w[0])) in EdgesOf(S)
  {
    EdgesOfMem(S, (StartId, CharNode(w[0])));
  }

  lemma EdgesOfEndIn(S: set<string>, w: string)
    requires w in S && w != ""
    ensures (CharNode(w[|w| - 1]), EndId) in EdgesOf(S)
  {
    EdgesOfMem(S, (CharNode(w[|w| - 1]), EndId));
  }

  lemma EdgesOfMidIn(S: set<string>, w: string, i: int)
    requires w in S && 0 <= i < |w| - 1
    ensures (CharNode(w[i]), CharNode(w[i + 1])) in EdgesOf(S)
  {
    EdgesOfMem(S, (CharNode(w[i]), CharNode(w[i + 1])));
  }

  lemma BigramWF(S: set<string>, g: Graph)
    requires g.nodes == NodesOf(Alphabet(S))
    requires g.labels == LabelsOf(Alphabet(S))
    requires g.edges == EdgesOf(S)
    requires g.start == StartId && g.end == EndId
    ensures WF(g)
  {
    var alphabet := Alphabet(S);
    assert g.labels.Keys == g.nodes by {
      forall n | n in g.labels.Keys ensures n in g.nodes {
        if n != StartId && n != EndId {
          var c :| c in alphabet && CharNode(c) == n;
        }
      }
      forall n | n in g.nodes ensures n in g.labels.Keys {
        if n != StartId && n != EndId {
          var c :| c in alphabet && CharNode(c) == n;
        }
      }
    }
    forall e | e in g.edges ensures e.0 in g.nodes && e.1 in g.nodes {
      EdgesOfMem(S, e);
      if exists w :: w in S && w != "" && e == (StartId, CharNode(w[0])) {
        var w :| w in S && w != "" && e == (StartId, CharNode(w[0]));
        assert w[0] in alphabet;
      } else if exists w :: w in S && w != "" && e == (CharNode(w[|w| - 1]), EndId) {
        var w :| w in S && w != "" && e == (CharNode(w[|w| - 1]), EndId);
        assert w[|w| - 1] in alphabet;
      } else if exists w, i :: w in S && 0 <= i < |w| - 1 && e == (CharNode(w[i]), CharNode(w[i + 1])) {
        var w, i :| w in S && 0 <= i < |w| - 1 && e == (CharNode(w[i]), CharNode(w[i + 1]));
        assert w[i] in alphabet;
        assert w[i + 1] in alphabet;
      } else {
        assert "" in S && e == (StartId, EndId);
      }
    }
  }

  lemma BigramAllLabelsSore(S: set<string>, g: Graph)
    requires WF(g)
    requires g.nodes == NodesOf(Alphabet(S))
    requires g.labels == LabelsOf(Alphabet(S))
    ensures AllLabelsSore(g)
  {
    var alphabet := Alphabet(S);
    EpsIsSore();
    forall n | n in g.nodes ensures IsSore(g.labels[n]) {
      if n != StartId && n != EndId {
        var c :| c in alphabet && CharNode(c) == n;
        SingleSymIsSore(c);
      }
    }
  }

  lemma BigramPairwiseDisjoint(S: set<string>, g: Graph)
    requires WF(g)
    requires g.nodes == NodesOf(Alphabet(S))
    requires g.labels == LabelsOf(Alphabet(S))
    ensures PairwiseDisjointLabels(g)
  {
    var alphabet := Alphabet(S);
    forall n1, n2 | n1 in g.nodes && n2 in g.nodes && n1 != n2
      ensures forall c :: Symbols(g.labels[n1])[c] == 0 || Symbols(g.labels[n2])[c] == 0 {
      if n1 == StartId || n1 == EndId {
        assert Symbols(g.labels[n1]) == multiset{};
      } else if n2 == StartId || n2 == EndId {
        assert Symbols(g.labels[n2]) == multiset{};
      } else {
        var c1 :| c1 in alphabet && CharNode(c1) == n1;
        var c2 :| c2 in alphabet && CharNode(c2) == n2;
        assert c1 != c2 by { CharNodeInjective(c2, c1); }
        assert Symbols(g.labels[n1]) == multiset{c1};
        assert Symbols(g.labels[n2]) == multiset{c2};
      }
    }
  }

  lemma BigramAcceptsOne(S: set<string>, g: Graph, w: string)
    requires WF(g)
    requires g.nodes == NodesOf(Alphabet(S))
    requires g.labels == LabelsOf(Alphabet(S))
    requires g.edges == EdgesOf(S)
    requires g.start == StartId && g.end == EndId
    requires w in S
    ensures GraphAccepts(g, w)
  {
    var alphabet := Alphabet(S);
    if w == "" {
      var walk := [StartId, EndId];
      EdgesOfMem(S, (StartId, EndId));
      assert IsWalk(g, walk);
      var splits := [0, 0, 0];
      assert WalkMatches(g, walk, w) by {
        assert Matches(g.labels[walk[0]], w[splits[0]..splits[1]]);
        assert Matches(g.labels[walk[1]], w[splits[1]..splits[2]]);
      }
    } else {
      var k := |w|;
      var walk := [StartId] + seq(k, i requires 0 <= i < k => CharNode(w[i])) + [EndId];
      assert |walk| == k + 2;
      assert walk[0] == StartId;
      assert walk[k + 1] == EndId;
      forall i | 0 <= i < k ensures walk[i + 1] == CharNode(w[i]) {
      }

      assert IsWalk(g, walk) by {
        forall i | 0 <= i < |walk| ensures walk[i] in g.nodes {
          if i == 0 {
          } else if i == k + 1 {
          } else {
            assert w[i - 1] in alphabet;
          }
        }
        forall i | 0 <= i < |walk| - 1 ensures (walk[i], walk[i + 1]) in g.edges {
          if i == 0 {
            EdgesOfStartIn(S, w);
          } else if i == k {
            EdgesOfEndIn(S, w);
          } else {
            EdgesOfMidIn(S, w, i - 1);
          }
        }
      }

      var splits := [0, 0] + seq(k, i requires 0 <= i < k => i + 1) + [k];
      assert |splits| == k + 3 == |walk| + 1;
      assert splits[0] == 0;
      assert splits[|walk|] == k;

      forall i {:trigger walk[i]} | 0 <= i < |walk|
        ensures 0 <= splits[i] <= splits[i + 1] <= |w|
        ensures Matches(g.labels[walk[i]], w[splits[i]..splits[i + 1]])
      {
        if i == 0 {
          assert splits[0] == 0 && splits[1] == 0;
          assert g.labels[walk[0]] == Eps;
          assert w[0..0] == "";
        } else if i == k + 1 {
          assert splits[k + 1] == k && splits[k + 2] == k;
          assert g.labels[walk[k + 1]] == Eps;
          assert w[k..k] == "";
        } else {
          // 1 <= i <= k: walk[i] = CharNode(w[i-1]), splits[i] = i-1, splits[i+1] = i.
          assert splits[i] == i - 1;
          assert splits[i + 1] == i;
          assert walk[i] == CharNode(w[i - 1]);
          assert g.labels[walk[i]] == Sym(w[i - 1]);
          assert w[i - 1..i] == [w[i - 1]];
        }
      }
      assert WalkMatches(g, walk, w) by {
        assert |splits| == |walk| + 1 && splits[0] == 0 && splits[|walk|] == |w|;
      }
    }
  }

  method BuildBigramGraph(S: set<string>) returns (g: Graph)
    ensures WF(g)
    ensures AllLabelsSore(g)
    ensures PairwiseDisjointLabels(g)
    ensures forall w :: w in S ==> GraphAccepts(g, w)
    ensures NoBackEdges(g)
    ensures g.labels[g.start] == Eps
    ensures g.labels[g.end] == Eps
    ensures InteriorNodes(g) == {} ==> forall w :: w in S ==> w == ""
    ensures InteriorNodes(g) != {} ==> exists w0 :: w0 in S && w0 != ""
  {
    var alphabet := Alphabet(S);
    var nodes := NodesOf(alphabet);
    var labels := LabelsOf(alphabet);
    var edges := EdgesOf(S);

    g := Graph(nodes, labels, edges, StartId, EndId);

    BigramWF(S, g);
    BigramAllLabelsSore(S, g);
    BigramPairwiseDisjoint(S, g);
    forall w | w in S ensures GraphAccepts(g, w) {
      BigramAcceptsOne(S, g, w);
    }
    BigramNoBackEdges(S, g);
    if InteriorNodes(g) == {} {
      BigramInteriorNodesEmptyImpliesAllEmpty(S, g);
    } else {
      BigramInteriorNodesNonEmpty(S, g);
    }
  }

  lemma BigramInteriorNodesEmptyImpliesAllEmpty(S: set<string>, g: Graph)
    requires WF(g)
    requires g.nodes == NodesOf(Alphabet(S))
    requires g.start == StartId && g.end == EndId
    requires InteriorNodes(g) == {}
    ensures forall w :: w in S ==> w == ""
  {
    var alphabet := Alphabet(S);
    assert InteriorNodes(g) == g.nodes - {StartId, EndId};
    assert g.nodes == {StartId, EndId} + (set c | c in alphabet :: CharNode(c));
    forall c | c in alphabet ensures CharNode(c) != StartId && CharNode(c) != EndId {
      CharNodeNotSentinel(c);
    }
    assert InteriorNodes(g) == (set c | c in alphabet :: CharNode(c));
    assert (set c | c in alphabet :: CharNode(c)) == {};
    assert alphabet == {} by {
      if alphabet != {} {
        var c :| c in alphabet;
        assert CharNode(c) in InteriorNodes(g);
        assert false;
      }
    }
    forall w | w in S ensures w == "" {
      if w != "" {
        assert w[0] in alphabet;
      }
    }
  }

  lemma BigramInteriorNodesNonEmpty(S: set<string>, g: Graph)
    requires WF(g)
    requires g.nodes == NodesOf(Alphabet(S))
    requires g.start == StartId && g.end == EndId
    requires InteriorNodes(g) != {}
    ensures exists w0 :: w0 in S && w0 != ""
  {
    var alphabet := Alphabet(S);
    assert InteriorNodes(g) == g.nodes - {StartId, EndId};
    assert g.nodes == {StartId, EndId} + (set c | c in alphabet :: CharNode(c));
    forall c | c in alphabet ensures CharNode(c) != StartId && CharNode(c) != EndId {
      CharNodeNotSentinel(c);
    }
    assert InteriorNodes(g) == (set c | c in alphabet :: CharNode(c));
    assert (set c | c in alphabet :: CharNode(c)) != {};
    assert alphabet != {};
    var c :| c in alphabet;
    var w, i :| w in S && 0 <= i < |w| && w[i] == c;
    assert w != "";
  }

  // ==================================================================================
  // Round 2: simple-path contraction (algorithm step 2.1)
  // ==================================================================================

  // ---- Fresh node ids ----

  ghost function SetMax(s: set<int>): int
    requires s != {}
    ensures SetMax(s) in s
    ensures forall x :: x in s ==> x <= SetMax(s)
    decreases s
  {
    var pick :| pick in s;
    var rest := s - {pick};
    if rest == {} then
      assert s == {pick};
      pick
    else
      var m := SetMax(rest);
      assert s == rest + {pick};
      if pick >= m then pick else m
  }

  ghost function FreshNode(nodes: set<int>): int
    ensures FreshNode(nodes) !in nodes
  {
    if nodes == {} then 0
    else SetMax(nodes) + 1
  }

  // ---- The rule ----

  predicate CanContractSimplePath(g: Graph, x: int, y: int)
    requires WF(g)
  {
    x in g.nodes && y in g.nodes && x != y &&
    x != g.start && x != g.end && y != g.start && y != g.end &&
    (x, y) in g.edges &&
    (y, x) !in g.edges &&
    (forall n :: n in g.nodes && (n, y) in g.edges ==> n == x) &&
    (forall n :: n in g.nodes && (x, n) in g.edges ==> n == y)
  }

  ghost function ContractSimplePathGraph(g: Graph, x: int, y: int): Graph
    requires WF(g)
    requires CanContractSimplePath(g, x, y)
  {
    var m := FreshNode(g.nodes);
    var nodes' := g.nodes - {x, y} + {m};
    var labels' := (map n | n in g.nodes - {x, y} :: n := g.labels[n])
                     [m := Concat(g.labels[x], g.labels[y])];
    var untouched := set e | e in g.edges && e.0 != x && e.0 != y && e.1 != x && e.1 != y :: e;
    var into_m := set a | a in g.nodes && (a, x) in g.edges :: (a, m);
    var outof_m := set b | b in g.nodes && (y, b) in g.edges :: (m, b);
    Graph(nodes', labels', untouched + into_m + outof_m, g.start, g.end)
  }

  lemma ContractSimplePathWF(g: Graph, x: int, y: int)
    requires WF(g)
    requires CanContractSimplePath(g, x, y)
    ensures WF(ContractSimplePathGraph(g, x, y))
  {
    var g' := ContractSimplePathGraph(g, x, y);
    var m := FreshNode(g.nodes);
    assert g'.start in g'.nodes;
    assert g'.end in g'.nodes;
    forall e | e in g'.edges ensures e.0 in g'.nodes && e.1 in g'.nodes {
      if e.0 != m && e.1 != m {
        // untouched edge: both endpoints were in g.nodes and != x,y (else it would not
        // have survived the "untouched" filter), so still in g'.nodes.
        assert e.0 != x && e.0 != y && e.1 != x && e.1 != y;
      } else if e.1 == m {
        // e came from into_m: e == (a, m) for some a with (a,x) in g.edges.
        var a :| a in g.nodes && (a, x) in g.edges && e == (a, m);
        // a cannot be x (no self-loop: x's only outgoing edge is to y, so (x,x) in
        // g.edges would force x == y, excluded) or y (that would be edge (y,x), which
        // CanContractSimplePath excludes).
        assert a != x by {
          if a == x {
            assert (x, x) in g.edges;
          }
        }
        assert a != y;
      } else {
        // e came from outof_m: e == (m, b) for some b with (y,b) in g.edges.
        var b :| b in g.nodes && (y, b) in g.edges && e == (m, b);
        assert b != y by {
          if b == y {
            assert (y, y) in g.edges;
          }
        }
        assert b != x;
      }
    }
  }

  lemma ContractSimplePathAllLabelsSore(g: Graph, x: int, y: int)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanContractSimplePath(g, x, y)
    ensures WF(ContractSimplePathGraph(g, x, y))
    ensures AllLabelsSore(ContractSimplePathGraph(g, x, y))
  {
    ContractSimplePathWF(g, x, y);
    var g' := ContractSimplePathGraph(g, x, y);
    var m := FreshNode(g.nodes);
    forall n | n in g'.nodes ensures IsSore(g'.labels[n]) {
      if n == m {
        assert forall c :: Symbols(g.labels[x])[c] == 0 || Symbols(g.labels[y])[c] == 0;
        SymbolsDisjointIsSore(g.labels[x], g.labels[y]);
      }
    }
  }

  lemma ContractSimplePathPairwiseDisjoint(g: Graph, x: int, y: int)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanContractSimplePath(g, x, y)
    ensures WF(ContractSimplePathGraph(g, x, y))
    ensures PairwiseDisjointLabels(ContractSimplePathGraph(g, x, y))
  {
    ContractSimplePathWF(g, x, y);
    var g' := ContractSimplePathGraph(g, x, y);
    var m := FreshNode(g.nodes);
    forall n1, n2 | n1 in g'.nodes && n2 in g'.nodes && n1 != n2
      ensures forall c :: Symbols(g'.labels[n1])[c] == 0 || Symbols(g'.labels[n2])[c] == 0
    {
      if n1 == m {
        assert g'.labels[n1] == Concat(g.labels[x], g.labels[y]);
        assert Symbols(g'.labels[n1]) == Symbols(g.labels[x]) + Symbols(g.labels[y]);
        forall c ensures Symbols(g'.labels[n1])[c] == 0 || Symbols(g'.labels[n2])[c] == 0 {
          if Symbols(g.labels[x])[c] > 0 {
            assert Symbols(g.labels[n2])[c] == 0;
          } else if Symbols(g.labels[y])[c] > 0 {
            assert Symbols(g.labels[n2])[c] == 0;
          }
        }
      } else if n2 == m {
        assert g'.labels[n2] == Concat(g.labels[x], g.labels[y]);
        assert Symbols(g'.labels[n2]) == Symbols(g.labels[x]) + Symbols(g.labels[y]);
        forall c ensures Symbols(g'.labels[n1])[c] == 0 || Symbols(g'.labels[n2])[c] == 0 {
          if Symbols(g.labels[x])[c] > 0 {
            assert Symbols(g.labels[n1])[c] == 0;
          } else if Symbols(g.labels[y])[c] > 0 {
            assert Symbols(g.labels[n1])[c] == 0;
          }
        }
      } else {
        assert g'.labels[n1] == g.labels[n1];
        assert g'.labels[n2] == g.labels[n2];
      }
    }
  }

  // ---- Soundness preservation ----

  // Every occurrence of x in a valid walk is immediately followed by y (x's only
  // outgoing edge goes to y, and x can never be the walk's last element since
  // x != g.end), and every occurrence of y is immediately preceded by x (symmetric,
  // via y's only incoming edge and y != g.start). This is what makes the "contract
  // every consecutive [x,y] pair" transformation below well-defined and total.
  lemma OccurrencePairing(g: Graph, x: int, y: int, walk: seq<int>)
    requires WF(g)
    requires CanContractSimplePath(g, x, y)
    requires IsWalk(g, walk)
    ensures forall i :: 0 <= i < |walk| && walk[i] == x ==> i < |walk| - 1 && walk[i + 1] == y
    ensures forall i :: 0 <= i < |walk| && walk[i] == y ==> i > 0 && walk[i - 1] == x
  {
    forall i | 0 <= i < |walk| && walk[i] == x ensures i < |walk| - 1 && walk[i + 1] == y {
      assert i != |walk| - 1;
      assert (walk[i], walk[i + 1]) in g.edges;
    }
    forall i | 0 <= i < |walk| && walk[i] == y ensures i > 0 && walk[i - 1] == x {
      assert i != 0;
      assert (walk[i - 1], walk[i]) in g.edges;
    }
  }

  // A step sequence that need not start at g.start or end at g.end (unlike IsWalk) -
  // the general shape the induction below actually needs, since a suffix of a walk
  // isn't itself an IsWalk.
  predicate ValidSteps(g: Graph, steps: seq<int>)
    requires WF(g)
  {
    |steps| >= 1 &&
    (forall i :: 0 <= i < |steps| ==> steps[i] in g.nodes) &&
    (forall i :: 0 <= i < |steps| - 1 ==> (steps[i], steps[i + 1]) in g.edges)
  }

  function ContractWalk(walk: seq<int>, x: int, y: int, m: int): seq<int>
    decreases |walk|
  {
    if |walk| < 2 then walk
    else if walk[0] == x && walk[1] == y then [m] + ContractWalk(walk[2..], x, y, m)
    else [walk[0]] + ContractWalk(walk[1..], x, y, m)
  }

  function ContractSplits(walk: seq<int>, splits: seq<nat>, x: int, y: int): seq<nat>
    requires |splits| == |walk| + 1
    decreases |walk|
  {
    if |walk| < 2 then splits
    else if walk[0] == x && walk[1] == y then [splits[0]] + ContractSplits(walk[2..], splits[2..], x, y)
    else [splits[0]] + ContractSplits(walk[1..], splits[1..], x, y)
  }

  // A step sequence together with a splits witness showing w matches along it,
  // piece by piece - the "per-index" facts bundled into one named predicate so the
  // (fiddly, shifted-index) reasoning about dropping a step is proved exactly once
  // below (StepsOkDropFirst), instead of being re-derived with slightly different
  // index shifts at every use site.
  predicate StepsOk(g: Graph, walk: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
  {
    |walk| >= 1 && |splits| == |walk| + 1 &&
    (forall i :: 0 <= i < |walk| ==> walk[i] in g.nodes) &&
    (forall i :: 0 <= i < |walk| ==>
      var lo := splits[i]; var hi := splits[i + 1];
      lo <= hi <= |w| && Matches(g.labels[walk[i]], w[lo..hi]))
  }

  lemma StepsOkDropFirst(g: Graph, walk: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
    requires StepsOk(g, walk, splits, w)
    requires |walk| >= 2
    ensures StepsOk(g, walk[1..], splits[1..], w)
  {
    var walk2 := walk[1..];
    var splits2 := splits[1..];
    forall i | 0 <= i < |walk2| ensures walk2[i] in g.nodes {
      assert walk2[i] == walk[i + 1];
    }
    forall i | 0 <= i < |walk2|
      ensures var lo := splits2[i]; var hi := splits2[i + 1]; lo <= hi <= |w| && Matches(g.labels[walk2[i]], w[lo..hi])
    {
      assert walk2[i] == walk[i + 1];
      assert splits2[i] == splits[i + 1];
      assert splits2[i + 1] == splits[i + 2];
    }
  }

  // Extracts StepsOk's per-index fact at one fixed, concrete index, as its own lemma
  // call rather than relying on Z3 to auto-instantiate StepsOk's internal forall from
  // inside another, enclosing forall/loop body. The two shapes are logically
  // equivalent, but this one has proved more robust across different verifier
  // invocation modes (observed empirically: a couple of call sites elsewhere in this
  // file that inlined this instantiation directly verified fine under `dafny verify`
  // but intermittently failed under `dafny build`/`dafny test`, and switching them to
  // call this lemma instead fixed it) - isolating the instantiation into its own small,
  // self-contained proof obligation sidesteps whatever specific difference in trigger
  // firing or fuel the two invocation modes have.
  lemma StepsOkAt(g: Graph, walk: seq<int>, splits: seq<nat>, w: string, i: int)
    requires WF(g)
    requires StepsOk(g, walk, splits, w)
    requires 0 <= i < |walk|
    ensures splits[i] <= splits[i + 1] <= |w|
    ensures Matches(g.labels[walk[i]], w[splits[i]..splits[i + 1]])
  {
  }

  // The main induction: a ValidSteps segment in g, together with a splits witness
  // showing w's pieces match along it, contracts to a ValidSteps segment in g' with a
  // (shorter) splits witness showing the SAME w still matches along it.
  lemma {:timeLimitMultiplier 8} ContractStepsPreserves(g: Graph, x: int, y: int, m: int, g': Graph,
                                walk: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
    requires CanContractSimplePath(g, x, y)
    requires m == FreshNode(g.nodes)
    requires g' == ContractSimplePathGraph(g, x, y)
    requires ValidSteps(g, walk)
    requires forall i :: 0 <= i < |walk| && walk[i] == x ==> i < |walk| - 1 && walk[i + 1] == y
    requires forall i :: 0 <= i < |walk| && walk[i] == y ==> i > 0 && walk[i - 1] == x
    requires StepsOk(g, walk, splits, w)
    ensures WF(g')
    ensures ValidSteps(g', ContractWalk(walk, x, y, m))
    ensures StepsOk(g', ContractWalk(walk, x, y, m), ContractSplits(walk, splits, x, y), w)
    ensures ContractSplits(walk, splits, x, y)[0] == splits[0]
    ensures ContractSplits(walk, splits, x, y)[|ContractWalk(walk, x, y, m)|] == splits[|walk|]
    decreases |walk|
  {
    ContractSimplePathWF(g, x, y);
    var walk' := ContractWalk(walk, x, y, m);
    var splits' := ContractSplits(walk, splits, x, y);

    if |walk| < 2 {
      // ValidSteps requires |walk| >= 1, so |walk| == 1: both ContractWalk and
      // ContractSplits hit their base case unchanged.
      assert walk' == walk;
      assert splits' == splits;
      assert walk[0] != x by {
        // the "occurrence pairing" requires clause, instantiated at i = 0: if
        // walk[0] == x it would force 0 < |walk| - 1 == 0, a contradiction.
      }
      assert walk[0] != y by {
        // instantiated at i = 0: if walk[0] == y it would force 0 > 0, a contradiction.
      }
      assert ValidSteps(g', walk') by {
        assert walk[0] in g.nodes && walk[0] != x && walk[0] != y;
      }
      assert StepsOk(g', walk', splits', w) by {
        forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
        }
        forall i | 0 <= i < |walk'|
          ensures var lo := splits'[i]; var hi := splits'[i + 1];
                  lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
        {
          assert g'.labels[walk[i]] == g.labels[walk[i]];
        }
      }
    } else if walk[0] == x && walk[1] == y {
      // walk[1] == y is forced anyway by occurrence pairing, matching ContractWalk's
      // own case split.
      var restWalk := walk[2..];
      var restSplits := splits[2..];
      assert walk' == [m] + ContractWalk(restWalk, x, y, m);
      assert splits' == [splits[0]] + ContractSplits(restWalk, restSplits, x, y);
      var restWalk' := ContractWalk(restWalk, x, y, m);
      var restSplits' := ContractSplits(restWalk, restSplits, x, y);

      // StepsOk(g, walk, splits, w) at i = 0 and i = 1 gives exactly the two facts
      // needed to combine x's and y's matches into m's.
      StepsOkAt(g, walk, splits, w, 0);
      StepsOkAt(g, walk, splits, w, 1);
      assert splits[0] <= splits[1] <= |w|;
      assert splits[1] <= splits[2] <= |w|;
      assert g'.labels[m] == Concat(g.labels[x], g.labels[y]);
      assert Matches(g.labels[x], w[splits[0]..splits[1]]);
      assert Matches(g.labels[y], w[splits[1]..splits[2]]);
      assert Matches(g'.labels[m], w[splits[0]..splits[2]]) by {
        assert 0 <= splits[1] - splits[0] <= splits[2] - splits[0];
        assert w[splits[0]..splits[2]][..splits[1] - splits[0]] == w[splits[0]..splits[1]];
        assert w[splits[0]..splits[2]][splits[1] - splits[0]..] == w[splits[1]..splits[2]];
      }

      if |restWalk| == 0 {
        // restWalk == []: ContractWalk/ContractSplits both hit their base case.
        assert restWalk' == [];
        assert restSplits' == restSplits;
        assert restSplits == [splits[2]];
        assert walk' == [m];
        assert splits' == [splits[0], splits[2]];
        assert ValidSteps(g', walk') by {
          assert m in g'.nodes;
        }
        assert StepsOk(g', walk', splits', w) by {
          forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
          }
          forall i | 0 <= i < |walk'|
            ensures var lo := splits'[i]; var hi := splits'[i + 1];
                    lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
          {
            // |walk'| == 1, so i == 0 is the only case; already established above.
          }
        }
      } else {
        // restWalk == (walk[1..])[1..] and restSplits == (splits[1..])[1..], so two
        // applications of StepsOkDropFirst give StepsOk(g, restWalk, restSplits, w).
        StepsOkDropFirst(g, walk, splits, w);
        StepsOkDropFirst(g, walk[1..], splits[1..], w);
        assert (walk[1..])[1..] == restWalk;
        assert (splits[1..])[1..] == restSplits;

        forall i | 0 <= i < |restWalk| && restWalk[i] == x ensures i < |restWalk| - 1 && restWalk[i + 1] == y {
          assert walk[i + 2] == restWalk[i];
        }
        forall i | 0 <= i < |restWalk| && restWalk[i] == y ensures i > 0 && restWalk[i - 1] == x {
          assert walk[i + 2] == restWalk[i];
        }
        ContractStepsPreserves(g, x, y, m, g', restWalk, restSplits, w);
        assert walk' == [m] + restWalk';
        assert splits' == [splits[0]] + restSplits';
        assert ValidSteps(g', walk') by {
          assert m in g'.nodes;
          assert (m, restWalk'[0]) in g'.edges by {
            assert (y, restWalk[0]) in g.edges;
          }
        }
        assert StepsOk(g', walk', splits', w) by {
          forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
            if i == 0 {
            } else {
              assert walk'[i] == restWalk'[i - 1];
            }
          }
          forall i | 0 <= i < |walk'|
            ensures var lo := splits'[i]; var hi := splits'[i + 1];
                    lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
          {
            if i == 0 {
              assert splits'[0] == splits[0] && splits'[1] == restSplits'[0];
              assert restSplits'[0] == restSplits[0] == splits[2];
              var lo := splits'[0]; var hi := splits'[1];
              assert lo == splits[0] && hi == splits[2];
              assert Matches(g'.labels[m], w[lo..hi]);
              assert walk'[0] == m;
              assert Matches(g'.labels[walk'[0]], w[lo..hi]);
            } else {
              assert walk'[i] == restWalk'[i - 1];
              assert splits'[i] == restSplits'[i - 1];
              assert splits'[i + 1] == restSplits'[i];
              var lo := splits'[i]; var hi := splits'[i + 1];
              assert lo == restSplits'[i - 1] && hi == restSplits'[i];
              assert Matches(g'.labels[walk'[i]], w[lo..hi]);
            }
          }
        }
      }
    } else {
      // walk[0] is untouched; recurse on the tail.
      var restWalk := walk[1..];
      var restSplits := splits[1..];
      assert walk[0] != x && walk[0] != y;
      assert walk' == [walk[0]] + ContractWalk(restWalk, x, y, m);
      assert splits' == [splits[0]] + ContractSplits(restWalk, restSplits, x, y);
      var restWalk' := ContractWalk(restWalk, x, y, m);
      var restSplits' := ContractSplits(restWalk, restSplits, x, y);
      assert g'.labels[walk[0]] == g.labels[walk[0]];

      if |restWalk| == 0 {
        assert restWalk' == [];
        assert restSplits' == restSplits;
        assert walk' == [walk[0]];
        assert splits' == splits;
        assert ValidSteps(g', walk') by {
          assert walk[0] in g.nodes && walk[0] != x && walk[0] != y;
        }
        assert StepsOk(g', walk', splits', w) by {
          forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
          }
          forall i | 0 <= i < |walk'|
            ensures var lo := splits'[i]; var hi := splits'[i + 1];
                    lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
          {
          }
        }
      } else {
        forall i | 0 <= i < |restWalk| && restWalk[i] == x ensures i < |restWalk| - 1 && restWalk[i + 1] == y {
        }
        forall i | 0 <= i < |restWalk| && restWalk[i] == y ensures i > 0 && restWalk[i - 1] == x {
        }
        StepsOkDropFirst(g, walk, splits, w);
        // StepsOk(g, walk[1..], splits[1..], w) is exactly StepsOk(g, restWalk, restSplits, w).
        ContractStepsPreserves(g, x, y, m, g', restWalk, restSplits, w);
        assert walk' == [walk[0]] + restWalk';
        assert splits' == [splits[0]] + restSplits';
        assert ValidSteps(g', walk') by {
          assert walk[0] in g.nodes && walk[0] != x && walk[0] != y;
          assert (walk[0], restWalk'[0]) in g'.edges by {
            assert (walk[0], restWalk[0]) in g.edges;
          }
        }
        assert StepsOk(g', walk', splits', w) by {
          forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
            if i == 0 {
            } else {
              assert walk'[i] == restWalk'[i - 1];
            }
          }
          forall i | 0 <= i < |walk'|
            ensures var lo := splits'[i]; var hi := splits'[i + 1];
                    lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
          {
            if i == 0 {
            } else {
              assert walk'[i] == restWalk'[i - 1];
              assert splits'[i] == restSplits'[i - 1];
              assert splits'[i + 1] == restSplits'[i];
            }
          }
        }
      }
    }
  }

  lemma ContractSimplePathSound(g: Graph, x: int, y: int, w: string)
    requires WF(g)
    requires CanContractSimplePath(g, x, y)
    requires GraphAccepts(g, w)
    ensures GraphAccepts(ContractSimplePathGraph(g, x, y), w)
  {
    var g' := ContractSimplePathGraph(g, x, y);
    ContractSimplePathWF(g, x, y);
    var m := FreshNode(g.nodes);
    var walk :| IsWalk(g, walk) && WalkMatches(g, walk, w);
    var splits: seq<nat> :| |splits| == |walk| + 1 &&
      splits[0] == 0 && splits[|walk|] == |w| &&
      (forall i :: 0 <= i < |walk| ==>
        var lo := splits[i]; var hi := splits[i + 1];
        lo <= hi <= |w| && Matches(g.labels[walk[i]], w[lo..hi]));
    OccurrencePairing(g, x, y, walk);
    assert StepsOk(g, walk, splits, w) by {
      forall i | 0 <= i < |walk| ensures walk[i] in g.nodes {
      }
      forall i | 0 <= i < |walk|
        ensures var lo := splits[i]; var hi := splits[i + 1]; lo <= hi <= |w| && Matches(g.labels[walk[i]], w[lo..hi])
      {
      }
    }
    ContractStepsPreserves(g, x, y, m, g', walk, splits, w);
    var walk' := ContractWalk(walk, x, y, m);
    var splits' := ContractSplits(walk, splits, x, y);
    // The endpoints are structurally untouched: walk[0] == g.start and
    // walk[|walk|-1] == g.end, and neither g.start nor g.end is x or y, so
    // ContractWalk never merges them away.
    assert walk[0] == g.start && walk[0] != x && walk[0] != y;
    assert walk[|walk| - 1] == g.end && walk[|walk| - 1] != x && walk[|walk| - 1] != y;
    assert walk'[0] == g.start by {
      ContractWalkFirstUnchanged(walk, x, y, m);
    }
    assert walk'[|walk'| - 1] == g.end by {
      ContractWalkLastUnchanged(walk, x, y, m);
    }
    assert IsWalk(g', walk');
    assert splits'[0] == 0;
    assert splits'[|walk'|] == |w|;
    assert WalkMatches(g', walk', w) by {
      forall i | 0 <= i < |walk'|
        ensures var lo := splits'[i]; var hi := splits'[i + 1];
                lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
      {
      }
    }
  }

  lemma ContractWalkFirstUnchanged(walk: seq<int>, x: int, y: int, m: int)
    requires |walk| >= 1
    requires walk[0] != x
    ensures ContractWalk(walk, x, y, m)[0] == walk[0]
  {
  }

  lemma ContractWalkLastUnchanged(walk: seq<int>, x: int, y: int, m: int)
    requires |walk| >= 1
    requires forall i :: 0 <= i < |walk| && walk[i] == y ==> i > 0 && walk[i - 1] == x
    requires walk[|walk| - 1] != x
    requires walk[|walk| - 1] != y
    ensures var walk' := ContractWalk(walk, x, y, m); walk'[|walk'| - 1] == walk[|walk| - 1]
    decreases |walk|
  {
    if |walk| < 2 {
    } else if walk[0] == x && walk[1] == y {
      var rest := walk[2..];
      if |rest| == 0 {
      } else {
        forall i | 0 <= i < |rest| && rest[i] == y ensures i > 0 && rest[i - 1] == x {
        }
        ContractWalkLastUnchanged(rest, x, y, m);
      }
    } else {
      var rest := walk[1..];
      if |rest| == 0 {
      } else {
        forall i | 0 <= i < |rest| && rest[i] == y ensures i > 0 && rest[i - 1] == x {
        }
        ContractWalkLastUnchanged(rest, x, y, m);
      }
    }
  }

  // ==================================================================================
  // Round 3: OR-merge of any two non-adjacent nodes (algorithm step 2.2, generalized)
  // ==================================================================================

  function Preds(g: Graph, n: int): set<int>
    requires WF(g)
  {
    set p | p in g.nodes && (p, n) in g.edges
  }

  function Succs(g: Graph, n: int): set<int>
    requires WF(g)
  {
    set c | c in g.nodes && (n, c) in g.edges
  }

  // Unlike the textbook "same parents/same children" OR-merge, this does NOT require
  // Preds(g,a) == Preds(g,b) or Succs(g,a) == Succs(g,b) - any two distinct, non-sentinel
  // nodes with no edge directly between them (in either direction) and no self-loop on
  // either qualify. The no-self-loop conjuncts are new versus what an exact-overlap
  // precondition would need to state explicitly: under Preds(g,a) == Preds(g,b) a
  // self-loop on a would force a in Preds(g,a) == Preds(g,b), i.e. (a,b) in g.edges,
  // already excluded - so the old predicate got "no self-loop" for free as a consequence.
  // Without the equality, that derivation no longer goes through, so it is required
  // directly here instead; MergeAnyGraph's into_m/outof_m construction below relies on it
  // to avoid ever producing an edge whose endpoint is the removed node a or b rather than
  // the merged node m (see MergeAnyWF).
  predicate CanMergeAny(g: Graph, a: int, b: int)
    requires WF(g)
  {
    a in g.nodes && b in g.nodes && a != b &&
    a != g.start && a != g.end && b != g.start && b != g.end &&
    (a, b) !in g.edges && (b, a) !in g.edges &&
    (a, a) !in g.edges && (b, b) !in g.edges
  }

  ghost function MergeAnyGraph(g: Graph, a: int, b: int): Graph
    requires WF(g)
    requires CanMergeAny(g, a, b)
  {
    var m := FreshNode(g.nodes);
    var nodes' := g.nodes - {a, b} + {m};
    var labels' := (map n | n in g.nodes - {a, b} :: n := g.labels[n])
                     [m := Union(g.labels[a], g.labels[b])];
    var untouched := set e | e in g.edges && e.0 != a && e.0 != b && e.1 != a && e.1 != b :: e;
    var into_m := set p | p in g.nodes && ((p, a) in g.edges || (p, b) in g.edges) :: (p, m);
    var outof_m := set c | c in g.nodes && ((a, c) in g.edges || (b, c) in g.edges) :: (m, c);
    Graph(nodes', labels', untouched + into_m + outof_m, g.start, g.end)
  }

  lemma MergeAnyWF(g: Graph, a: int, b: int)
    requires WF(g)
    requires CanMergeAny(g, a, b)
    ensures WF(MergeAnyGraph(g, a, b))
  {
    var g' := MergeAnyGraph(g, a, b);
    var m := FreshNode(g.nodes);
    assert g'.start in g'.nodes && g'.end in g'.nodes;
    forall e | e in g'.edges ensures e.0 in g'.nodes && e.1 in g'.nodes {
      if e.0 != m && e.1 != m {
        assert e.0 != a && e.0 != b && e.1 != a && e.1 != b;
      } else if e.1 == m {
        var p :| p in g.nodes && ((p, a) in g.edges || (p, b) in g.edges) && e == (p, m);
        assert p != a by {
          if p == a {
            assert (a, a) in g.edges || (a, b) in g.edges;
          }
        }
        assert p != b by {
          if p == b {
            assert (b, a) in g.edges || (b, b) in g.edges;
          }
        }
      } else {
        var c :| c in g.nodes && ((a, c) in g.edges || (b, c) in g.edges) && e == (m, c);
        assert c != a by {
          if c == a {
            assert (a, a) in g.edges || (b, a) in g.edges;
          }
        }
        assert c != b by {
          if c == b {
            assert (a, b) in g.edges || (b, b) in g.edges;
          }
        }
      }
    }
  }

  lemma MergeAnyAllLabelsSore(g: Graph, a: int, b: int)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanMergeAny(g, a, b)
    ensures WF(MergeAnyGraph(g, a, b))
    ensures AllLabelsSore(MergeAnyGraph(g, a, b))
  {
    MergeAnyWF(g, a, b);
    var g' := MergeAnyGraph(g, a, b);
    var m := FreshNode(g.nodes);
    forall n | n in g'.nodes ensures IsSore(g'.labels[n]) {
      if n == m {
        assert forall c :: Symbols(g.labels[a])[c] == 0 || Symbols(g.labels[b])[c] == 0;
        SymbolsDisjointIsSore(g.labels[a], g.labels[b]);
      }
    }
  }

  lemma MergeAnyPairwiseDisjoint(g: Graph, a: int, b: int)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanMergeAny(g, a, b)
    ensures WF(MergeAnyGraph(g, a, b))
    ensures PairwiseDisjointLabels(MergeAnyGraph(g, a, b))
  {
    MergeAnyWF(g, a, b);
    var g' := MergeAnyGraph(g, a, b);
    var m := FreshNode(g.nodes);
    forall n1, n2 | n1 in g'.nodes && n2 in g'.nodes && n1 != n2
      ensures forall c :: Symbols(g'.labels[n1])[c] == 0 || Symbols(g'.labels[n2])[c] == 0
    {
      if n1 == m {
        assert g'.labels[n1] == Union(g.labels[a], g.labels[b]);
        assert Symbols(g'.labels[n1]) == Symbols(g.labels[a]) + Symbols(g.labels[b]);
        forall c ensures Symbols(g'.labels[n1])[c] == 0 || Symbols(g'.labels[n2])[c] == 0 {
          if Symbols(g.labels[a])[c] > 0 {
            assert Symbols(g.labels[n2])[c] == 0;
          } else if Symbols(g.labels[b])[c] > 0 {
            assert Symbols(g.labels[n2])[c] == 0;
          }
        }
      } else if n2 == m {
        assert g'.labels[n2] == Union(g.labels[a], g.labels[b]);
        assert Symbols(g'.labels[n2]) == Symbols(g.labels[a]) + Symbols(g.labels[b]);
        forall c ensures Symbols(g'.labels[n1])[c] == 0 || Symbols(g'.labels[n2])[c] == 0 {
          if Symbols(g.labels[a])[c] > 0 {
            assert Symbols(g.labels[n1])[c] == 0;
          } else if Symbols(g.labels[b])[c] > 0 {
            assert Symbols(g.labels[n1])[c] == 0;
          }
        }
      } else {
        assert g'.labels[n1] == g.labels[n1];
        assert g'.labels[n2] == g.labels[n2];
      }
    }
  }

  // ---- Soundness preservation ----

  // Relabel every occurrence of a or b (at the same position) to m; every other
  // position is untouched. Unlike ContractWalk, this never changes the walk's length.
  function RelabelWalk(walk: seq<int>, a: int, b: int, m: int): seq<int>
  {
    seq(|walk|, i requires 0 <= i < |walk| => if walk[i] == a || walk[i] == b then m else walk[i])
  }

  lemma {:timeLimitMultiplier 10} MergeAnyStepsPreserves(g: Graph, a: int, b: int, m: int, g': Graph,
                                walk: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
    requires CanMergeAny(g, a, b)
    requires m == FreshNode(g.nodes)
    requires g' == MergeAnyGraph(g, a, b)
    requires ValidSteps(g, walk)
    requires StepsOk(g, walk, splits, w)
    ensures WF(g')
    ensures ValidSteps(g', RelabelWalk(walk, a, b, m))
    ensures StepsOk(g', RelabelWalk(walk, a, b, m), splits, w)
  {
    MergeAnyWF(g, a, b);
    var walk' := RelabelWalk(walk, a, b, m);
    assert |walk'| == |walk|;

    forall i | 0 <= i < |walk| - 1 ensures (walk'[i], walk'[i + 1]) in g'.edges {
      var u, v := walk[i], walk[i + 1];
      assert (u, v) in g.edges;
      if u != a && u != b && v != a && v != b {
        assert walk'[i] == u && walk'[i + 1] == v;
      } else if (u == a || u == b) && v != a && v != b {
        // (u,v) in g.edges with u in {a,b} directly witnesses membership in outof_m for
        // c = v - no need for Succs(g,a) == Succs(g,b) at all, unlike the exact-overlap
        // case: whichever of a/b u actually is, that side's own edge (u,v) suffices.
        assert (a, v) in g.edges || (b, v) in g.edges;
        assert walk'[i] == m && walk'[i + 1] == v;
      } else if u != a && u != b && (v == a || v == b) {
        assert (u, a) in g.edges || (u, b) in g.edges;
        assert walk'[i] == u && walk'[i + 1] == m;
      } else {
        // Both u and v in {a, b}: impossible, since every such combination requires an
        // edge directly between a and b, or a self-loop on a or b, all excluded by
        // CanMergeAny.
        assert false by {
          if u == a && v == a {
          } else if u == a && v == b {
            assert (a, b) in g.edges;
          } else if u == b && v == a {
            assert (b, a) in g.edges;
          } else {
          }
        }
      }
    }
    assert ValidSteps(g', walk') by {
      forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
        if walk[i] == a || walk[i] == b {
        } else {
          assert walk[i] in g.nodes && walk[i] != a && walk[i] != b;
        }
      }
    }

    assert StepsOk(g', walk', splits, w) by {
      forall i | 0 <= i < |walk| ensures walk'[i] in g'.nodes {
        if walk[i] == a || walk[i] == b {
        } else {
          assert walk[i] in g.nodes && walk[i] != a && walk[i] != b;
        }
      }
      forall i | 0 <= i < |walk|
        ensures var lo := splits[i]; var hi := splits[i + 1];
                lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
      {
        StepsOkAt(g, walk, splits, w, i);
        var lo := splits[i]; var hi := splits[i + 1];
        assert lo <= hi <= |w|;
        assert Matches(g.labels[walk[i]], w[lo..hi]);
        if walk[i] == a {
          assert walk'[i] == m;
          assert g'.labels[m] == Union(g.labels[a], g.labels[b]);
          assert Matches(g'.labels[walk'[i]], w[lo..hi]);
        } else if walk[i] == b {
          assert walk'[i] == m;
          assert g'.labels[m] == Union(g.labels[a], g.labels[b]);
          assert Matches(g'.labels[walk'[i]], w[lo..hi]);
        } else {
          assert walk'[i] == walk[i];
          assert g'.labels[walk[i]] == g.labels[walk[i]];
          assert Matches(g'.labels[walk'[i]], w[lo..hi]);
        }
      }
    }
  }

  lemma MergeAnySound(g: Graph, a: int, b: int, w: string)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanMergeAny(g, a, b)
    requires GraphAccepts(g, w)
    ensures WF(MergeAnyGraph(g, a, b))
    ensures GraphAccepts(MergeAnyGraph(g, a, b), w)
  {
    var g' := MergeAnyGraph(g, a, b);
    MergeAnyWF(g, a, b);
    var m := FreshNode(g.nodes);
    var walk :| IsWalk(g, walk) && WalkMatches(g, walk, w);
    var splits: seq<nat> :| |splits| == |walk| + 1 &&
      splits[0] == 0 && splits[|walk|] == |w| &&
      (forall i :: 0 <= i < |walk| ==>
        var lo := splits[i]; var hi := splits[i + 1];
        lo <= hi <= |w| && Matches(g.labels[walk[i]], w[lo..hi]));
    assert StepsOk(g, walk, splits, w) by {
      forall i | 0 <= i < |walk| ensures walk[i] in g.nodes {
      }
    }
    MergeAnyStepsPreserves(g, a, b, m, g', walk, splits, w);
    var walk' := RelabelWalk(walk, a, b, m);
    // The endpoints are untouched: g.start/g.end are never a or b.
    assert walk[0] == g.start && walk[0] != a && walk[0] != b;
    assert walk[|walk| - 1] == g.end && walk[|walk| - 1] != a && walk[|walk| - 1] != b;
    assert walk'[0] == g.start;
    assert walk'[|walk'| - 1] == g.end;
    assert IsWalk(g', walk');
    assert WalkMatches(g', walk', w) by {
      forall i | 0 <= i < |walk'|
        ensures var lo := splits[i]; var hi := splits[i + 1];
                lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
      {
      }
    }
  }

  // ---- Round 10 addition: the "exact-overlap" special case, tried at higher priority
  // than the bare CanMergeAny search (see this file's Round 10 header comment for the
  // motivating bug/fix). CanMergeExact is nothing more than CanMergeAny with the two
  // extra Preds/Succs equality conjuncts the textbook "same parents/same children"
  // OR-merge (algorithm step 2.2 as originally stated) requires - so it needs no new
  // graph transformation, WF/AllLabelsSore/PairwiseDisjointLabels/soundness proof, or
  // termination argument: MergeAnyGraph/MergeAnyWF/MergeAnyAllLabelsSore/
  // MergeAnyPairwiseDisjoint/MergeAnySound/InteriorNodesMergeAny/LoopStepMergeAny all
  // already apply unchanged to any pair satisfying CanMergeAny, and CanMergeExact
  // implies CanMergeAny directly from its own definition.
  predicate CanMergeExact(g: Graph, a: int, b: int)
    requires WF(g)
  {
    CanMergeAny(g, a, b) && Preds(g, a) == Preds(g, b) && Succs(g, a) == Succs(g, b)
  }

  // ==================================================================================
  // Round 4: optional contraction (algorithm step 2.3)
  // ==================================================================================

  predicate CanMakeOptional(g: Graph, v: int)
    requires WF(g)
  {
    v in g.nodes && v != g.start && v != g.end &&
    Preds(g, v) != {} && Succs(g, v) != {} &&
    (v, v) !in g.edges &&
    (forall p, c :: p in Preds(g, v) && c in Succs(g, v) ==> (p, c) in g.edges)
  }

  ghost function MakeOptionalGraph(g: Graph, v: int): Graph
    requires WF(g)
    requires CanMakeOptional(g, v)
  {
    var labels' := g.labels[v := Opt(g.labels[v])];
    var bypass := set p, c | p in Preds(g, v) && c in Succs(g, v) :: (p, c);
    Graph(g.nodes, labels', g.edges - bypass, g.start, g.end)
  }

  lemma MakeOptionalWF(g: Graph, v: int)
    requires WF(g)
    requires CanMakeOptional(g, v)
    ensures WF(MakeOptionalGraph(g, v))
  {
    var g' := MakeOptionalGraph(g, v);
    assert g'.start in g'.nodes && g'.end in g'.nodes;
    forall e | e in g'.edges ensures e.0 in g'.nodes && e.1 in g'.nodes {
      assert e in g.edges;
    }
  }

  lemma MakeOptionalAllLabelsSore(g: Graph, v: int)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanMakeOptional(g, v)
    ensures WF(MakeOptionalGraph(g, v))
    ensures AllLabelsSore(MakeOptionalGraph(g, v))
  {
    MakeOptionalWF(g, v);
    var g' := MakeOptionalGraph(g, v);
    forall n | n in g'.nodes ensures IsSore(g'.labels[n]) {
      if n == v {
        OptIsSore(g.labels[v]);
      }
    }
  }

  lemma MakeOptionalPairwiseDisjoint(g: Graph, v: int)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanMakeOptional(g, v)
    ensures WF(MakeOptionalGraph(g, v))
    ensures PairwiseDisjointLabels(MakeOptionalGraph(g, v))
  {
    MakeOptionalWF(g, v);
    var g' := MakeOptionalGraph(g, v);
    forall n1, n2 | n1 in g'.nodes && n2 in g'.nodes && n1 != n2
      ensures forall c :: Symbols(g'.labels[n1])[c] == 0 || Symbols(g'.labels[n2])[c] == 0
    {
      if n1 == v {
        assert Symbols(g'.labels[n1]) == Symbols(g.labels[v]);
      } else if n2 == v {
        assert Symbols(g'.labels[n2]) == Symbols(g.labels[v]);
      }
    }
  }

  // ---- Soundness preservation ----

  // Insert v between walk[i] and walk[i+1] whenever that step is a bypass edge (walk[i]
  // a parent of v, walk[i+1] a child of v) - every other step is left untouched. Unlike
  // ContractWalk/RelabelWalk, this can only ever GROW the walk (by exactly one element
  // per bypass point), never shrink it.
  function InsertOptional(walk: seq<int>, v: int, preds: set<int>, succs: set<int>): seq<int>
    decreases |walk|
  {
    if |walk| <= 1 then walk
    else
      var rest := InsertOptional(walk[1..], v, preds, succs);
      if walk[0] in preds && walk[1] in succs then [walk[0], v] + rest else [walk[0]] + rest
  }

  function InsertOptionalSplits(walk: seq<int>, splits: seq<nat>, v: int, preds: set<int>, succs: set<int>): seq<nat>
    requires |splits| == |walk| + 1
    decreases |walk|
  {
    if |walk| <= 1 then splits
    else
      var restSplits := InsertOptionalSplits(walk[1..], splits[1..], v, preds, succs);
      if walk[0] in preds && walk[1] in succs then [splits[0], splits[1]] + restSplits
      else [splits[0]] + restSplits
  }

  lemma {:timeLimitMultiplier 8} InsertOptionalStepsPreserves(g: Graph, v: int, g': Graph,
                                      walk: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
    requires CanMakeOptional(g, v)
    requires g' == MakeOptionalGraph(g, v)
    requires ValidSteps(g, walk)
    requires StepsOk(g, walk, splits, w)
    ensures WF(g')
    ensures ValidSteps(g', InsertOptional(walk, v, Preds(g, v), Succs(g, v)))
    ensures StepsOk(g', InsertOptional(walk, v, Preds(g, v), Succs(g, v)),
                    InsertOptionalSplits(walk, splits, v, Preds(g, v), Succs(g, v)), w)
    ensures InsertOptionalSplits(walk, splits, v, Preds(g, v), Succs(g, v))[0] == splits[0]
    ensures InsertOptionalSplits(walk, splits, v, Preds(g, v), Succs(g, v))
              [|InsertOptional(walk, v, Preds(g, v), Succs(g, v))|] == splits[|walk|]
    decreases |walk|
  {
    MakeOptionalWF(g, v);
    var preds, succs := Preds(g, v), Succs(g, v);
    var walk' := InsertOptional(walk, v, preds, succs);
    var splits' := InsertOptionalSplits(walk, splits, v, preds, succs);

    if |walk| <= 1 {
      assert walk' == walk;
      assert splits' == splits;
      assert ValidSteps(g', walk') by {
        assert walk[0] in g.nodes;
      }
      assert StepsOk(g', walk', splits', w) by {
        forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
        }
        forall i | 0 <= i < |walk'|
          ensures var lo := splits'[i]; var hi := splits'[i + 1];
                  lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
        {
          if walk[i] == v {
            assert g'.labels[v] == Opt(g.labels[v]);
            OptSound(g.labels[v], w[splits[i]..splits[i + 1]]);
          } else {
            assert g'.labels[walk[i]] == g.labels[walk[i]];
          }
        }
      }
    } else {
      var restWalk := walk[1..];
      var restSplits := splits[1..];
      StepsOkDropFirst(g, walk, splits, w);
      assert ValidSteps(g, restWalk);
      InsertOptionalStepsPreserves(g, v, g', restWalk, restSplits, w);
      var restWalk' := InsertOptional(restWalk, v, preds, succs);
      var restSplits' := InsertOptionalSplits(restWalk, restSplits, v, preds, succs);
      assert restWalk'[0] == restWalk[0];
      assert restSplits'[0] == restSplits[0];

      if walk[0] in preds && walk[1] in succs {
        assert walk' == [walk[0], v] + restWalk';
        assert splits' == [splits[0], splits[1]] + restSplits';
        assert (walk[0], v) in g.edges;
        assert (v, walk[1]) in g.edges;
        assert ValidSteps(g', walk') by {
          assert walk[0] in g.nodes && v in g.nodes;
          assert (walk[0], v) in g'.edges by {
            assert (walk[0], v) !in (set p, c | p in preds && c in succs :: (p, c)) by {
              // (walk[0], v) is never itself a bypass edge - a bypass edge's second
              // component is always in succs, but v !in succs (v has no self-loop
              // under CanMakeOptional... actually v could be its own child in a cycle;
              // ruled out separately below if needed - here we only need the pair
              // (walk[0], v) not to match the SHAPE (p, c) with c in succs, i.e. v in
              // succs would be required, which we rule out next).
              if v in succs {
                assert (v, v) in g.edges;
              }
            }
          }
          assert (v, walk[1]) in g'.edges by {
            assert (v, walk[1]) !in (set p, c | p in preds && c in succs :: (p, c)) by {
              if v in preds {
                assert (v, v) in g.edges;
              }
            }
          }
          assert restWalk'[0] == walk[1];
        }
        assert StepsOk(g', walk', splits', w) by {
          forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
            if i == 0 {
            } else if i == 1 {
            } else {
              assert walk'[i] == restWalk'[i - 2];
            }
          }
          forall i | 0 <= i < |walk'|
            ensures var lo := splits'[i]; var hi := splits'[i + 1];
                    lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
          {
            if i == 0 {
              assert walk[0] != v by {
                if walk[0] == v {
                  assert (v, v) in g.edges;
                }
              }
              assert g'.labels[walk[0]] == g.labels[walk[0]];
            } else if i == 1 {
              assert g'.labels[v] == Opt(g.labels[v]);
              OptSoundEps(g.labels[v]);
            } else {
              assert walk'[i] == restWalk'[i - 2];
              assert splits'[i] == restSplits'[i - 2];
              assert splits'[i + 1] == restSplits'[i - 1];
            }
          }
        }
      } else {
        assert walk' == [walk[0]] + restWalk';
        assert splits' == [splits[0]] + restSplits';
        assert ValidSteps(g', walk') by {
          assert walk[0] in g.nodes;
          assert (walk[0], restWalk[0]) in g.edges;
          assert (walk[0], restWalk[0]) in g'.edges by {
            assert (walk[0], restWalk[0]) !in (set p, c | p in preds && c in succs :: (p, c));
          }
        }
        assert StepsOk(g', walk', splits', w) by {
          assert |walk'| >= 1;
          assert |splits'| == |walk'| + 1;
          assert g'.nodes == g.nodes;
          forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
            if i == 0 {
            } else {
              assert walk'[i] == restWalk'[i - 1];
            }
          }
          forall i | 0 <= i < |walk'|
            ensures var lo := splits'[i]; var hi := splits'[i + 1];
                    lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
          {
            if i == 0 {
              if walk[0] == v {
                assert g'.labels[v] == Opt(g.labels[v]);
                OptSound(g.labels[v], w[splits[0]..splits[1]]);
              } else {
                assert g'.labels[walk[0]] == g.labels[walk[0]];
              }
            } else {
              assert walk'[i] == restWalk'[i - 1];
              assert splits'[i] == restSplits'[i - 1];
              assert splits'[i + 1] == restSplits'[i];
            }
          }
        }
      }
    }
  }

  lemma MakeOptionalSound(g: Graph, v: int, w: string)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanMakeOptional(g, v)
    requires GraphAccepts(g, w)
    ensures WF(MakeOptionalGraph(g, v))
    ensures GraphAccepts(MakeOptionalGraph(g, v), w)
  {
    var g' := MakeOptionalGraph(g, v);
    MakeOptionalWF(g, v);
    var walk :| IsWalk(g, walk) && WalkMatches(g, walk, w);
    assert IsWalk(g, walk);
    assert WalkMatches(g, walk, w);
    var splits: seq<nat> :| |splits| == |walk| + 1 &&
      splits[0] == 0 && splits[|walk|] == |w| &&
      (forall i :: 0 <= i < |walk| ==>
        var lo := splits[i]; var hi := splits[i + 1];
        lo <= hi <= |w| && Matches(g.labels[walk[i]], w[lo..hi]));
    assert StepsOk(g, walk, splits, w) by {
      forall i | 0 <= i < |walk| ensures walk[i] in g.nodes {
      }
    }
    InsertOptionalStepsPreserves(g, v, g', walk, splits, w);
    var preds, succs := Preds(g, v), Succs(g, v);
    var walk' := InsertOptional(walk, v, preds, succs);
    var splits' := InsertOptionalSplits(walk, splits, v, preds, succs);
    assert walk[0] == g.start && walk[0] != v;
    assert walk[|walk| - 1] == g.end && walk[|walk| - 1] != v;
    assert walk'[0] == g.start by {
      InsertOptionalFirstUnchanged(walk, v, preds, succs);
    }
    assert walk'[|walk'| - 1] == g.end by {
      InsertOptionalLastUnchanged(walk, v, preds, succs);
    }
    assert IsWalk(g', walk');
    assert splits'[0] == 0;
    assert splits'[|walk'|] == |w|;
    assert WalkMatches(g', walk', w) by {
      forall i | 0 <= i < |walk'|
        ensures var lo := splits'[i]; var hi := splits'[i + 1];
                lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
      {
      }
    }
  }

  lemma InsertOptionalFirstUnchanged(walk: seq<int>, v: int, preds: set<int>, succs: set<int>)
    requires |walk| >= 1
    ensures InsertOptional(walk, v, preds, succs)[0] == walk[0]
  {
  }

  lemma InsertOptionalLastUnchanged(walk: seq<int>, v: int, preds: set<int>, succs: set<int>)
    requires |walk| >= 1
    ensures var walk' := InsertOptional(walk, v, preds, succs); walk'[|walk'| - 1] == walk[|walk| - 1]
    decreases |walk|
  {
    if |walk| <= 1 {
    } else {
      InsertOptionalLastUnchanged(walk[1..], v, preds, succs);
    }
  }

  // ==================================================================================
  // Round 5: SCC contraction (algorithm step 3)
  // ==================================================================================

  predicate CanContractSCC(g: Graph, C: set<int>)
    requires WF(g)
  {
    C <= g.nodes && C != {} && g.start !in C && g.end !in C
  }

  // UnionAllLabels folds over a SEQUENCE of node ids, not a set - deterministic
  // sequence indexing (cs[0], cs[1..]) avoids the ambiguity of a set-based `:|` pick,
  // whose witness a caller cannot assume matches any independently-chosen witness of
  // its own (an earlier draft tried to reason about UnionAllLabels via its own,
  // separately-picked witness, which is unsound in general - two different `:|`
  // extractions from the same set are not guaranteed to agree). This mirrors
  // Chain.dfy's UnionAll(cs: seq<char>) exactly, just with graph node labels instead
  // of single characters as the leaves.
  // All three facts needed everywhere SetToSeq is used are bundled as ensures on the
  // function itself (rather than proved by separate lemmas) so they are automatically
  // available to ANY caller - including other functions (like ContractSCCGraph below),
  // which cannot call lemmas from within their own body, only rely on ensures clauses.
  ghost function SetToSeq(s: set<int>): seq<int>
    ensures forall x :: x in SetToSeq(s) ==> x in s
    ensures forall x :: x in s ==> x in SetToSeq(s)
    ensures forall i, j :: 0 <= i < |SetToSeq(s)| && 0 <= j < |SetToSeq(s)| && i != j ==>
              SetToSeq(s)[i] != SetToSeq(s)[j]
    decreases s
  {
    if s == {} then []
    else
      var x :| x in s;
      var restSeq := SetToSeq(s - {x});
      assert forall y :: y in restSeq ==> y in s - {x};
      [x] + restSeq
  }

  function UnionAllLabels(g: Graph, cs: seq<int>): Regex
    requires WF(g)
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    decreases cs
  {
    if cs == [] then Empty
    else if |cs| == 1 then g.labels[cs[0]]
    else Union(g.labels[cs[0]], UnionAllLabels(g, cs[1..]))
  }

  lemma UnionAllLabelsSound(g: Graph, cs: seq<int>, c: int, s: string)
    requires WF(g)
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    requires c in cs
    requires Matches(g.labels[c], s)
    ensures Matches(UnionAllLabels(g, cs), s)
    decreases cs
  {
    if cs[0] == c {
    } else {
      UnionAllLabelsSound(g, cs[1..], c, s);
    }
  }

  lemma UnionAllLabelsSymbolsMem(g: Graph, cs: seq<int>, ch: char)
    requires WF(g)
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    ensures ch in Symbols(UnionAllLabels(g, cs)) <==>
              (exists i :: 0 <= i < |cs| && ch in Symbols(g.labels[cs[i]]))
    decreases cs
  {
    if cs == [] {
    } else if |cs| == 1 {
    } else {
      UnionAllLabelsSymbolsMem(g, cs[1..], ch);
    }
  }

  lemma UnionAllLabelsIsSore(g: Graph, cs: seq<int>)
    requires WF(g)
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires forall i, j :: 0 <= i < |cs| && 0 <= j < |cs| && i != j ==> cs[i] != cs[j]
    ensures IsSore(UnionAllLabels(g, cs))
    decreases cs
  {
    if cs == [] {
      EmptyIsSore();
    } else if |cs| == 1 {
    } else {
      var rest := cs[1..];
      forall i, j | 0 <= i < |rest| && 0 <= j < |rest| && i != j ensures rest[i] != rest[j] {
        assert cs[i + 1] == rest[i] && cs[j + 1] == rest[j];
      }
      UnionAllLabelsIsSore(g, rest);
      forall ch ensures Symbols(g.labels[cs[0]])[ch] == 0 || Symbols(UnionAllLabels(g, rest))[ch] == 0 {
        if Symbols(g.labels[cs[0]])[ch] > 0 && Symbols(UnionAllLabels(g, rest))[ch] > 0 {
          UnionAllLabelsSymbolsMem(g, rest, ch);
          var idx :| 0 <= idx < |rest| && ch in Symbols(g.labels[rest[idx]]);
          assert rest[idx] != cs[0] by {
            assert cs[idx + 1] == rest[idx];
          }
          assert Symbols(g.labels[cs[0]])[ch] == 0 || Symbols(g.labels[rest[idx]])[ch] == 0;
          assert false;
        }
      }
      SymbolsDisjointIsSore(g.labels[cs[0]], UnionAllLabels(g, rest));
    }
  }

  ghost function ContractSCCGraph(g: Graph, C: set<int>): Graph
    requires WF(g)
    requires CanContractSCC(g, C)
  {
    var cs := SetToSeq(C);
    var m := FreshNode(g.nodes);
    var nodes' := g.nodes - C + {m};
    var labels' := (map n | n in g.nodes - C :: n := g.labels[n])[m := Star(UnionAllLabels(g, cs))];
    var untouched := set e | e in g.edges && e.0 !in C && e.1 !in C :: e;
    var into_m := set p | p in g.nodes && p !in C && (exists c :: c in C && (p, c) in g.edges) :: (p, m);
    var outof_m := set q | q in g.nodes && q !in C && (exists c :: c in C && (c, q) in g.edges) :: (m, q);
    Graph(nodes', labels', untouched + into_m + outof_m, g.start, g.end)
  }

  lemma ContractSCCWF(g: Graph, C: set<int>)
    requires WF(g)
    requires CanContractSCC(g, C)
    ensures WF(ContractSCCGraph(g, C))
  {
    var g' := ContractSCCGraph(g, C);
    var m := FreshNode(g.nodes);
    assert g'.start in g'.nodes && g'.end in g'.nodes;
    forall e | e in g'.edges ensures e.0 in g'.nodes && e.1 in g'.nodes {
      if e.0 != m && e.1 != m {
        assert e.0 !in C && e.1 !in C;
      } else if e.1 == m {
        var p :| p in g.nodes && p !in C && (exists c :: c in C && (p, c) in g.edges) && e == (p, m);
      } else {
        var q :| q in g.nodes && q !in C && (exists c :: c in C && (c, q) in g.edges) && e == (m, q);
      }
    }
  }

  lemma ContractSCCAllLabelsSore(g: Graph, C: set<int>)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanContractSCC(g, C)
    ensures WF(ContractSCCGraph(g, C))
    ensures AllLabelsSore(ContractSCCGraph(g, C))
  {
    ContractSCCWF(g, C);
    var g' := ContractSCCGraph(g, C);
    var m := FreshNode(g.nodes);
    var cs := SetToSeq(C);
    forall n | n in g'.nodes ensures IsSore(g'.labels[n]) {
      if n == m {
        UnionAllLabelsIsSore(g, cs);
        StarIsSore(UnionAllLabels(g, cs));
      }
    }
  }

  lemma ContractSCCPairwiseDisjoint(g: Graph, C: set<int>)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanContractSCC(g, C)
    ensures WF(ContractSCCGraph(g, C))
    ensures PairwiseDisjointLabels(ContractSCCGraph(g, C))
  {
    ContractSCCWF(g, C);
    var g' := ContractSCCGraph(g, C);
    var m := FreshNode(g.nodes);
    var cs := SetToSeq(C);
    forall n1, n2 | n1 in g'.nodes && n2 in g'.nodes && n1 != n2
      ensures forall ch :: Symbols(g'.labels[n1])[ch] == 0 || Symbols(g'.labels[n2])[ch] == 0
    {
      if n1 == m {
        assert g'.labels[n1] == Star(UnionAllLabels(g, cs));
        assert Symbols(g'.labels[n1]) == Symbols(UnionAllLabels(g, cs));
        forall ch ensures Symbols(g'.labels[n1])[ch] == 0 || Symbols(g'.labels[n2])[ch] == 0 {
          if Symbols(g'.labels[n1])[ch] > 0 {
            UnionAllLabelsSymbolsMem(g, cs, ch);
            var idx :| 0 <= idx < |cs| && ch in Symbols(g.labels[cs[idx]]);
            assert Symbols(g.labels[cs[idx]])[ch] == 0 || Symbols(g.labels[n2])[ch] == 0;
            assert Symbols(g.labels[cs[idx]])[ch] > 0;
          }
        }
      } else if n2 == m {
        assert g'.labels[n2] == Star(UnionAllLabels(g, cs));
        assert Symbols(g'.labels[n2]) == Symbols(UnionAllLabels(g, cs));
        forall ch ensures Symbols(g'.labels[n1])[ch] == 0 || Symbols(g'.labels[n2])[ch] == 0 {
          if Symbols(g'.labels[n2])[ch] > 0 {
            UnionAllLabelsSymbolsMem(g, cs, ch);
            var idx :| 0 <= idx < |cs| && ch in Symbols(g.labels[cs[idx]]);
            assert Symbols(g.labels[cs[idx]])[ch] == 0 || Symbols(g.labels[n1])[ch] == 0;
            assert Symbols(g.labels[cs[idx]])[ch] > 0;
          }
        }
      } else {
        assert g'.labels[n1] == g.labels[n1];
        assert g'.labels[n2] == g.labels[n2];
      }
    }
  }

  // Membership facts about ContractSCCGraph(g,C)'s edges, factored out into small,
  // single-purpose lemmas (each with an explicit witness passed in, not searched for via
  // `exists`) so that CollapseStepsPreserves - a large, self-recursive lemma - doesn't
  // need to re-derive them by re-unfolding ContractSCCGraph's comprehension-heavy body
  // (in particular the existentially-quantified into_m/outof_m sets) from scratch at
  // every one of its recursive calls. This is exactly what caused it to time out.
  lemma ContractSCCEdgeUntouched(g: Graph, C: set<int>, a: int, b: int)
    requires WF(g)
    requires CanContractSCC(g, C)
    requires (a, b) in g.edges && a !in C && b !in C
    ensures (a, b) in ContractSCCGraph(g, C).edges
  {
  }

  lemma ContractSCCEdgeIntoM(g: Graph, C: set<int>, p: int, c: int)
    requires WF(g)
    requires CanContractSCC(g, C)
    requires p in g.nodes && p !in C && c in C && (p, c) in g.edges
    ensures (p, FreshNode(g.nodes)) in ContractSCCGraph(g, C).edges
  {
  }

  lemma ContractSCCEdgeOutOfM(g: Graph, C: set<int>, q: int, c: int)
    requires WF(g)
    requires CanContractSCC(g, C)
    requires q in g.nodes && q !in C && c in C && (c, q) in g.edges
    ensures (FreshNode(g.nodes), q) in ContractSCCGraph(g, C).edges
  {
  }

  // ---- Soundness preservation ----

  function SkipCRun(walk: seq<int>, C: set<int>): seq<int>
    requires |walk| >= 1 && walk[0] in C
    ensures |SkipCRun(walk, C)| < |walk|
    decreases |walk|
  {
    if |walk| >= 2 && walk[1] in C then SkipCRun(walk[1..], C) else walk[1..]
  }

  // The maximal C-run starting at walk[0] really is maximal: the element right after it
  // (if any) is not in C. Needed so CollapseStepsPreservesRun can conclude the collapsed
  // walk's next step, after the merged SCC node, is a genuinely untouched node.
  lemma SkipCRunHeadNotInC(walk: seq<int>, C: set<int>)
    requires |walk| >= 1 && walk[0] in C
    requires |SkipCRun(walk, C)| >= 1
    ensures SkipCRun(walk, C)[0] !in C
    decreases |walk|
  {
    if |walk| >= 2 && walk[1] in C {
      SkipCRunHeadNotInC(walk[1..], C);
    }
  }

  function CollapseRuns(walk: seq<int>, C: set<int>, m: int): seq<int>
    decreases |walk|
  {
    if |walk| == 0 then []
    else if walk[0] in C then [m] + CollapseRuns(SkipCRun(walk, C), C, m)
    else [walk[0]] + CollapseRuns(walk[1..], C, m)
  }

  function SkipCSplits(walk: seq<int>, splits: seq<nat>, C: set<int>): seq<nat>
    requires |walk| >= 1 && walk[0] in C
    requires |splits| == |walk| + 1
    ensures |SkipCSplits(walk, splits, C)| == |SkipCRun(walk, C)| + 1
    decreases |walk|
  {
    if |walk| >= 2 && walk[1] in C then SkipCSplits(walk[1..], splits[1..], C) else splits[1..]
  }

  function CollapseSplits(walk: seq<int>, splits: seq<nat>, C: set<int>, m: int): seq<nat>
    requires |splits| == |walk| + 1
    decreases |walk|
  {
    if |walk| == 0 then splits
    else if walk[0] in C then [splits[0]] + CollapseSplits(SkipCRun(walk, C), SkipCSplits(walk, splits, C), C, m)
    else [splits[0]] + CollapseSplits(walk[1..], splits[1..], C, m)
  }

  // If every step of `run` matches its own label and all its nodes are in C, the whole
  // run's concatenated substring matches Star(UnionAllLabels(g,C)) - built up one
  // run-step at a time via Star's own existential definition.
  lemma StarOfUnionAccepts(g: Graph, C: set<int>, cs: seq<int>, run: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
    requires C <= g.nodes
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    requires forall x :: x in C <==> x in cs
    requires forall i :: 0 <= i < |run| ==> run[i] in C
    requires |splits| == |run| + 1
    requires splits[0] <= |w|
    requires forall i :: 0 <= i < |run| ==>
               var lo := splits[i]; var hi := splits[i + 1];
               lo <= hi <= |w| && Matches(g.labels[run[i]], w[lo..hi])
    ensures splits[0] <= splits[|run|] <= |w|
    ensures Matches(Star(UnionAllLabels(g, cs)), w[splits[0]..splits[|run|]])
    decreases |run|
  {
    if |run| == 0 {
      assert w[splits[0]..splits[0]] == "";
    } else {
      StarOfUnionAccepts(g, C, cs, run[1..], splits[1..], w);
      assert Matches(g.labels[run[0]], w[splits[0]..splits[1]]);
      assert run[0] in cs;
      UnionAllLabelsSound(g, cs, run[0], w[splits[0]..splits[1]]);
      assert Matches(UnionAllLabels(g, cs), w[splits[0]..splits[1]]);
      assert Matches(Star(UnionAllLabels(g, cs)), w[splits[1]..splits[|run|]]);
      assert Matches(Star(UnionAllLabels(g, cs)), w[splits[0]..splits[|run|]]) by {
        assert 0 <= splits[1] - splits[0] <= splits[|run|] - splits[0];
        assert w[splits[0]..splits[|run|]][..splits[1] - splits[0]] == w[splits[0]..splits[1]];
        assert w[splits[0]..splits[|run|]][splits[1] - splits[0]..] == w[splits[1]..splits[|run|]];
      }
    }
  }

  // Dispatcher: CollapseStepsPreserves just picks which of the two case-specific lemmas
  // below applies. It, and they, are mutually recursive (each case's recursive step
  // calls back into the dispatcher on a strictly shorter walk, and the dispatcher calls
  // whichever case-lemma applies on the SAME walk) - exactly the "solve directly vs.
  // dispatch-then-recurse" shape already handled elsewhere in this project (see
  // Infer.dfy's InferGroup/InferGroupPositionalSplit/InferGroups) via a lexicographic
  // (|walk|, tag) decreases clause: the dispatcher uses tag 1, the case lemmas use tag 0,
  // so a same-length dispatch (tag 1 -> tag 0) is licensed by the tag alone, while every
  // recursive call back into the dispatcher (strictly shorter walk) is licensed by length
  // alone regardless of tags. This whole three-lemma split (rather than one big lemma)
  // is itself the fix for a genuine 30s solver timeout the single-lemma version hit -
  // splitting let each case's proof obligations be checked independently instead of as
  // one combined goal.
  lemma CollapseStepsPreserves(g: Graph, C: set<int>, m: int, g': Graph,
                                walk: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
    requires CanContractSCC(g, C)
    requires m == FreshNode(g.nodes)
    requires g' == ContractSCCGraph(g, C)
    requires ValidSteps(g, walk)
    requires StepsOk(g, walk, splits, w)
    ensures WF(g')
    ensures ValidSteps(g', CollapseRuns(walk, C, m))
    ensures StepsOk(g', CollapseRuns(walk, C, m), CollapseSplits(walk, splits, C, m), w)
    ensures CollapseSplits(walk, splits, C, m)[0] == splits[0]
    ensures CollapseSplits(walk, splits, C, m)[|CollapseRuns(walk, C, m)|] == splits[|walk|]
    decreases |walk|, 1
  {
    if |walk| == 0 {
      // ValidSteps requires |walk| >= 1, so this case is vacuous - nothing to prove.
    } else if walk[0] !in C {
      CollapseStepsPreservesUntouched(g, C, m, g', walk, splits, w);
    } else {
      CollapseStepsPreservesRun(g, C, m, g', walk, splits, w);
    }
  }

  lemma CollapseStepsPreservesUntouched(g: Graph, C: set<int>, m: int, g': Graph,
                                walk: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
    requires CanContractSCC(g, C)
    requires m == FreshNode(g.nodes)
    requires g' == ContractSCCGraph(g, C)
    requires ValidSteps(g, walk)
    requires StepsOk(g, walk, splits, w)
    requires |walk| >= 1 && walk[0] !in C
    ensures WF(g')
    ensures ValidSteps(g', CollapseRuns(walk, C, m))
    ensures StepsOk(g', CollapseRuns(walk, C, m), CollapseSplits(walk, splits, C, m), w)
    ensures CollapseSplits(walk, splits, C, m)[0] == splits[0]
    ensures CollapseSplits(walk, splits, C, m)[|CollapseRuns(walk, C, m)|] == splits[|walk|]
    decreases |walk|, 0
  {
    ContractSCCWF(g, C);
    var walk' := CollapseRuns(walk, C, m);
    var splits' := CollapseSplits(walk, splits, C, m);
    {
      var restWalk := walk[1..];
      var restSplits := splits[1..];
      if |restWalk| == 0 {
        assert walk' == [walk[0]] + CollapseRuns(restWalk, C, m);
        assert CollapseRuns(restWalk, C, m) == [];
        assert walk' == [walk[0]];
        assert splits' == [splits[0]] + CollapseSplits(restWalk, restSplits, C, m);
        assert CollapseSplits(restWalk, restSplits, C, m) == restSplits;
        assert splits' == [splits[0]] + restSplits;
        assert splits == [splits[0]] + restSplits;
        assert splits' == splits;
        assert ValidSteps(g', walk') by {
          assert walk[0] in g.nodes && walk[0] !in C;
        }
        assert StepsOk(g', walk', splits', w) by {
          assert |walk'| >= 1;
          assert |splits'| == |walk'| + 1;
          forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
          }
          forall i | 0 <= i < |walk'|
            ensures var lo := splits'[i]; var hi := splits'[i + 1];
                    lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
          {
            assert g'.labels[walk[0]] == g.labels[walk[0]];
          }
        }
      } else {
        StepsOkDropFirst(g, walk, splits, w);
        assert ValidSteps(g, restWalk) by {
          forall i | 0 <= i < |restWalk| ensures restWalk[i] in g.nodes {
            assert restWalk[i] == walk[i + 1];
          }
          forall i | 0 <= i < |restWalk| - 1 ensures (restWalk[i], restWalk[i + 1]) in g.edges {
            assert restWalk[i] == walk[i + 1] && restWalk[i + 1] == walk[i + 2];
          }
        }
        CollapseStepsPreserves(g, C, m, g', restWalk, restSplits, w);
        var restWalk' := CollapseRuns(restWalk, C, m);
        var restSplits' := CollapseSplits(restWalk, restSplits, C, m);
        assert walk' == [walk[0]] + restWalk';
        assert splits' == [splits[0]] + restSplits';
        assert ValidSteps(g', walk') by {
          assert walk[0] in g.nodes && walk[0] !in C;
          assert (walk[0], restWalk[0]) in g.edges;
          assert (walk[0], restWalk'[0]) in g'.edges by {
            if restWalk[0] in C {
              ContractSCCEdgeIntoM(g, C, walk[0], restWalk[0]);
              assert restWalk'[0] == m;
            } else {
              ContractSCCEdgeUntouched(g, C, walk[0], restWalk[0]);
              assert restWalk'[0] == restWalk[0];
            }
          }
        }
        assert StepsOk(g', walk', splits', w) by {
          assert |walk'| >= 1;
          assert |splits'| == |walk'| + 1;
          forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
            if i == 0 {
            } else {
              assert walk'[i] == restWalk'[i - 1];
            }
          }
          forall i | 0 <= i < |walk'|
            ensures var lo := splits'[i]; var hi := splits'[i + 1];
                    lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
          {
            if i == 0 {
              assert g'.labels[walk[0]] == g.labels[walk[0]];
            } else {
              assert walk'[i] == restWalk'[i - 1];
              assert splits'[i] == restSplits'[i - 1];
              assert splits'[i + 1] == restSplits'[i];
            }
          }
        }
      }
    }
  }

  lemma {:timeLimitMultiplier 12} CollapseStepsPreservesRun(g: Graph, C: set<int>, m: int, g': Graph,
                                walk: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
    requires CanContractSCC(g, C)
    requires m == FreshNode(g.nodes)
    requires g' == ContractSCCGraph(g, C)
    requires ValidSteps(g, walk)
    requires StepsOk(g, walk, splits, w)
    requires |walk| >= 1 && walk[0] in C
    ensures WF(g')
    ensures ValidSteps(g', CollapseRuns(walk, C, m))
    ensures StepsOk(g', CollapseRuns(walk, C, m), CollapseSplits(walk, splits, C, m), w)
    ensures CollapseSplits(walk, splits, C, m)[0] == splits[0]
    ensures CollapseSplits(walk, splits, C, m)[|CollapseRuns(walk, C, m)|] == splits[|walk|]
    decreases |walk|, 0
  {
    ContractSCCWF(g, C);
    var cs := SetToSeq(C);
    var walk' := CollapseRuns(walk, C, m);
    var splits' := CollapseSplits(walk, splits, C, m);
    {
      // walk[0] in C: collapse the whole maximal C-run starting here into one m.
      var afterRun := SkipCRun(walk, C);
      var afterSplits := SkipCSplits(walk, splits, C);
      var k := |walk| - |afterRun|;
      assert k >= 1;
      RunIsAllC(walk, C, k);
      assert afterRun == walk[k..];
      SkipCSplitsIsSuffix(walk, splits, C);
      assert afterSplits == splits[k..];
      var run := walk[..k];
      var runSplits := splits[..k + 1];
      forall i | 0 <= i < k ensures run[i] in C {
        assert run[i] == walk[i];
      }
      forall i | 0 <= i < k
        ensures var lo := runSplits[i]; var hi := runSplits[i + 1];
                lo <= hi <= |w| && Matches(g.labels[run[i]], w[lo..hi])
      {
        StepsOkAt(g, walk, splits, w, i);
        assert run[i] == walk[i];
        assert runSplits[i] == splits[i];
        assert runSplits[i + 1] == splits[i + 1];
      }
      assert runSplits[0] == splits[0];
      assert runSplits[k] == splits[k];
      assert splits[0] <= |w| by {
        assert 0 <= 0 < k;
        assert var lo := runSplits[0]; var hi := runSplits[1]; lo <= hi <= |w|;
      }
      StarOfUnionAccepts(g, C, cs, run, runSplits, w);
      assert splits[0] <= splits[k] <= |w| by {
        assert runSplits[0] <= runSplits[k] <= |w|;
      }
      assert Matches(Star(UnionAllLabels(g, cs)), w[splits[0]..splits[k]]) by {
        assert w[splits[0]..splits[k]] == w[runSplits[0]..runSplits[k]];
      }
      assert g'.labels[m] == Star(UnionAllLabels(g, cs));

      if |afterRun| == 0 {
        assert walk' == [m] + CollapseRuns(afterRun, C, m);
        assert CollapseRuns(afterRun, C, m) == [];
        assert walk' == [m];
        assert splits' == [splits[0], splits[k]];
        assert k == |walk|;
        assert ValidSteps(g', walk') by {
          assert m in g'.nodes;
        }
        assert StepsOk(g', walk', splits', w) by {
          forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
          }
          forall i | 0 <= i < |walk'|
            ensures var lo := splits'[i]; var hi := splits'[i + 1];
                    lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
          {
          }
        }
      } else {
        assert ValidSteps(g, afterRun) by {
          forall i | 0 <= i < |afterRun| ensures afterRun[i] in g.nodes {
            assert afterRun[i] == walk[k + i];
          }
          forall i | 0 <= i < |afterRun| - 1 ensures (afterRun[i], afterRun[i + 1]) in g.edges {
            assert afterRun[i] == walk[k + i] && afterRun[i + 1] == walk[k + i + 1];
          }
        }
        assert StepsOk(g, afterRun, afterSplits, w) by {
          forall i | 0 <= i < |afterRun| ensures afterRun[i] in g.nodes {
            assert afterRun[i] == walk[k + i];
          }
          forall i | 0 <= i < |afterRun|
            ensures var lo := afterSplits[i]; var hi := afterSplits[i + 1];
                    lo <= hi <= |w| && Matches(g.labels[afterRun[i]], w[lo..hi])
          {
            StepsOkAt(g, walk, splits, w, k + i);
            assert afterRun[i] == walk[k + i];
            assert afterSplits[i] == splits[k + i];
            assert afterSplits[i + 1] == splits[k + i + 1];
          }
        }
        CollapseStepsPreserves(g, C, m, g', afterRun, afterSplits, w);
        var afterWalk' := CollapseRuns(afterRun, C, m);
        var afterSplits' := CollapseSplits(afterRun, afterSplits, C, m);
        assert walk' == [m] + afterWalk';
        assert splits' == [splits[0], splits[k]] + afterSplits'[1..];
        assert afterSplits'[0] == afterSplits[0] == splits[k];
        assert ValidSteps(g', walk') by {
          assert m in g'.nodes;
          assert (m, afterWalk'[0]) in g'.edges by {
            assert afterRun[0] !in C by {
              SkipCRunHeadNotInC(walk, C);
            }
            assert run[k - 1] in C;
            assert (run[k - 1], afterRun[0]) in g.edges by {
              assert (walk[k - 1], walk[k]) in g.edges;
            }
            if afterWalk'[0] == afterRun[0] {
              ContractSCCEdgeOutOfM(g, C, afterRun[0], run[k - 1]);
            } else {
              // afterRun[0] itself starts a further, disjoint C-run only if afterRun[0]
              // in C, which contradicts afterRun[0] !in C established above - so
              // afterWalk'[0] == afterRun[0] always holds here.
            }
          }
        }
        assert StepsOk(g', walk', splits', w) by {
          forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
            if i == 0 {
            } else {
              assert walk'[i] == afterWalk'[i - 1];
            }
          }
          forall i | 0 <= i < |walk'|
            ensures var lo := splits'[i]; var hi := splits'[i + 1];
                    lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
          {
            if i == 0 {
            } else {
              assert walk'[i] == afterWalk'[i - 1];
              assert splits'[i] == afterSplits'[i - 1];
              assert splits'[i + 1] == afterSplits'[i];
              StepsOkAt(g', afterWalk', afterSplits', w, i - 1);
            }
          }
        }
      }
    }
  }

  // walk[..k] (the first k elements) are all in C, where k = |walk| - |SkipCRun(walk,C)|
  // (the length of the maximal C-run starting at walk[0]).
  lemma RunIsAllC(walk: seq<int>, C: set<int>, k: int)
    requires |walk| >= 1 && walk[0] in C
    requires k == |walk| - |SkipCRun(walk, C)|
    ensures 1 <= k <= |walk|
    ensures forall i :: 0 <= i < k ==> walk[i] in C
    ensures SkipCRun(walk, C) == walk[k..]
    decreases |walk|
  {
    if |walk| < 2 || walk[1] !in C {
      assert SkipCRun(walk, C) == walk[1..];
    } else {
      RunIsAllC(walk[1..], C, k - 1);
    }
  }

  // The splits-side counterpart of RunIsAllC: SkipCSplits drops exactly the same
  // number of leading split-points as SkipCRun drops walk-elements.
  lemma SkipCSplitsIsSuffix(walk: seq<int>, splits: seq<nat>, C: set<int>)
    requires |walk| >= 1 && walk[0] in C
    requires |splits| == |walk| + 1
    ensures SkipCSplits(walk, splits, C) == splits[|walk| - |SkipCRun(walk, C)|..]
    decreases |walk|
  {
    if |walk| < 2 || walk[1] !in C {
      assert SkipCRun(walk, C) == walk[1..];
      assert SkipCSplits(walk, splits, C) == splits[1..];
    } else {
      SkipCSplitsIsSuffix(walk[1..], splits[1..], C);
    }
  }

  lemma ContractSCCSound(g: Graph, C: set<int>, w: string)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanContractSCC(g, C)
    requires GraphAccepts(g, w)
    ensures WF(ContractSCCGraph(g, C))
    ensures GraphAccepts(ContractSCCGraph(g, C), w)
  {
    var g' := ContractSCCGraph(g, C);
    ContractSCCWF(g, C);
    var m := FreshNode(g.nodes);
    var walk :| IsWalk(g, walk) && WalkMatches(g, walk, w);
    assert IsWalk(g, walk);
    assert WalkMatches(g, walk, w);
    var splits: seq<nat> :| |splits| == |walk| + 1 &&
      splits[0] == 0 && splits[|walk|] == |w| &&
      (forall i :: 0 <= i < |walk| ==>
        var lo := splits[i]; var hi := splits[i + 1];
        lo <= hi <= |w| && Matches(g.labels[walk[i]], w[lo..hi]));
    assert StepsOk(g, walk, splits, w) by {
      forall i | 0 <= i < |walk| ensures walk[i] in g.nodes {
      }
    }
    CollapseStepsPreserves(g, C, m, g', walk, splits, w);
    var walk' := CollapseRuns(walk, C, m);
    var splits' := CollapseSplits(walk, splits, C, m);
    assert walk[0] == g.start && walk[0] !in C;
    assert walk[|walk| - 1] == g.end && walk[|walk| - 1] !in C;
    assert walk'[0] == g.start by {
      CollapseRunsFirstUnchanged(walk, C, m);
    }
    assert walk'[|walk'| - 1] == g.end by {
      CollapseRunsLastUnchanged(walk, C, m);
    }
    assert IsWalk(g', walk');
    assert splits'[0] == 0;
    assert splits'[|walk'|] == |w|;
    assert WalkMatches(g', walk', w) by {
      forall i | 0 <= i < |walk'|
        ensures var lo := splits'[i]; var hi := splits'[i + 1];
                lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
      {
      }
    }
  }

  lemma CollapseRunsFirstUnchanged(walk: seq<int>, C: set<int>, m: int)
    requires |walk| >= 1
    requires walk[0] !in C
    ensures CollapseRuns(walk, C, m)[0] == walk[0]
  {
  }

  lemma CollapseRunsLastUnchanged(walk: seq<int>, C: set<int>, m: int)
    requires |walk| >= 1
    requires walk[|walk| - 1] !in C
    ensures var walk' := CollapseRuns(walk, C, m); walk'[|walk'| - 1] == walk[|walk| - 1]
    decreases |walk|
  {
    if walk[0] !in C {
      if |walk| == 1 {
      } else {
        CollapseRunsLastUnchanged(walk[1..], C, m);
      }
    } else {
      var afterRun := SkipCRun(walk, C);
      var k := |walk| - |afterRun|;
      assert |afterRun| < |walk|;
      assert |afterRun| >= 1 by {
        if |afterRun| == 0 {
          assert walk[|walk| - 1] in C by { RunEndsInC(walk, C); }
        }
      }
      RunIsAllC(walk, C, k);
      assert afterRun == walk[k..];
      assert afterRun[|afterRun| - 1] == walk[|walk| - 1];
      CollapseRunsLastUnchanged(afterRun, C, m);
    }
  }

  lemma RunEndsInC(walk: seq<int>, C: set<int>)
    requires |walk| >= 1 && walk[0] in C
    requires |SkipCRun(walk, C)| == 0
    ensures walk[|walk| - 1] in C
    decreases |walk|
  {
    if |walk| < 2 || walk[1] !in C {
    } else {
      RunEndsInC(walk[1..], C);
    }
  }

  // ==================================================================================
  // Round 6: collapse-everything fallback (always available, regardless of structure)
  // ==================================================================================
  //
  // The full pipeline (future work) repeatedly applies whichever of Rounds 2-5's rules
  // applies, aiming to reduce the graph to a single interior node. Proving that this
  // specific rule set ALWAYS succeeds at that (i.e. always bottoms out in a clean chain)
  // is a hard combinatorial classification claim, not attempted here. Instead, this round
  // adds an always-sound fallback that needs no such claim: collapse EVERY remaining
  // interior node into one node in a single step, regardless of the graph's structure
  // (connected, disconnected, cyclic, acyclic, whatever) - this guarantees the pipeline
  // can always reach a single interior node in one more step whenever it gets stuck.
  //
  // This turns out to be close to free: CanContractSCC(g, C) (Round 5) never actually
  // required C to be a genuine strongly-connected-component - its precondition is just
  // "C is a nonempty subset of g's non-sentinel nodes" (see CanContractSCC above), which
  // C := InteriorNodes(g) satisfies trivially whenever there is any interior node left at
  // all. So CollapseAllGraph below is defined directly as
  // ContractSCCGraph(g, InteriorNodes(g)), and all four of its invariant/soundness lemmas
  // are one-line wrappers around the already-proven ContractSCCWF/AllLabelsSore/
  // PairwiseDisjoint/Sound - no new walk-transform reasoning (CollapseRuns/SkipCRun/
  // StarOfUnionAccepts, etc.) was needed at all, since that machinery is already fully
  // general in C.
  //
  // Also proved here: SingleInteriorWalkShape/SingleInteriorNodeAccepts, the "last mile"
  // fact that once a graph has been reduced to a SINGLE interior node m, GraphAccepts
  // collapses to a direct fact about m's own label - no more walk/graph reasoning needed.
  // This does need two extra hypotheses beyond just InteriorNodes(g) == {m} (which alone
  // is NOT enough: a graph with a single interior node m could still, for instance, have
  // a direct g.start -> g.end bypass edge coexisting with m, or non-Eps labels on the
  // sentinels, in which case GraphAccepts(g,w) could hold for some w with m never visited
  // at all - a genuine counterexample to the naive statement). The two extra hypotheses
  // (g.labels[g.start] == Eps, g.labels[g.end] == Eps, and g.edges containing exactly the
  // two edges g.start -> m -> g.end) hold throughout this whole pipeline in practice - no
  // round from BuildBigramGraph through CollapseAllGraph ever changes g.start's or
  // g.end's label away from Eps (every contraction rule's precondition explicitly
  // excludes the sentinels from the node/set being touched), and reaching a genuinely
  // single interior node with no leftover bypass is exactly the "clean chain" shape the
  // top-level pipeline is aiming to reach - so this lemma is stated with the hypotheses
  // that make it actually true, ready for a future round to discharge them once it
  // threads those two facts through as additional standing invariants.

  function InteriorNodes(g: Graph): set<int>
    requires WF(g)
  {
    g.nodes - {g.start, g.end}
  }

  ghost function CollapseAllGraph(g: Graph): Graph
    requires WF(g)
    requires InteriorNodes(g) != {}
  {
    ContractSCCGraph(g, InteriorNodes(g))
  }

  lemma CollapseAllWF(g: Graph)
    requires WF(g)
    requires InteriorNodes(g) != {}
    ensures WF(CollapseAllGraph(g))
  {
    assert CanContractSCC(g, InteriorNodes(g));
    ContractSCCWF(g, InteriorNodes(g));
  }

  lemma CollapseAllAllLabelsSore(g: Graph)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires InteriorNodes(g) != {}
    ensures WF(CollapseAllGraph(g))
    ensures AllLabelsSore(CollapseAllGraph(g))
  {
    assert CanContractSCC(g, InteriorNodes(g));
    ContractSCCAllLabelsSore(g, InteriorNodes(g));
  }

  lemma CollapseAllPairwiseDisjoint(g: Graph)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires InteriorNodes(g) != {}
    ensures WF(CollapseAllGraph(g))
    ensures PairwiseDisjointLabels(CollapseAllGraph(g))
  {
    assert CanContractSCC(g, InteriorNodes(g));
    ContractSCCPairwiseDisjoint(g, InteriorNodes(g));
  }

  // Like ContractSCCSound/MergeAnySound/MakeOptionalSound, this carries AllLabelsSore/
  // PairwiseDisjointLabels as preconditions too, matching this file's existing "…Sound"
  // lemma convention (ContractSimplePathSound is the one exception that doesn't need
  // them) - CollapseAllSound just forwards to ContractSCCSound, which requires them.
  lemma CollapseAllSound(g: Graph, w: string)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires InteriorNodes(g) != {}
    requires GraphAccepts(g, w)
    ensures WF(CollapseAllGraph(g))
    ensures GraphAccepts(CollapseAllGraph(g), w)
  {
    assert CanContractSCC(g, InteriorNodes(g));
    ContractSCCSound(g, InteriorNodes(g), w);
  }

  // ---- The "last mile" fact: a single interior node's own label already IS the answer ----

  // With g.edges containing exactly these two edges, g.start has no other outgoing edge
  // and g.end has no incoming edge from anywhere but m, so any start-to-end walk is
  // forced to be exactly [g.start, m, g.end] - proved directly (no induction needed) by
  // chasing the unique successor at each of the first three positions and then ruling out
  // a fourth, since g.end (the only possible value at position 2) has no outgoing edge at
  // all under this edge set.
  lemma SingleInteriorWalkShape(g: Graph, m: int, walk: seq<int>)
    requires WF(g)
    requires InteriorNodes(g) == {m}
    requires g.edges == {(g.start, m), (m, g.end)}
    requires IsWalk(g, walk)
    ensures walk == [g.start, m, g.end]
  {
    assert m != g.start && m != g.end;
    assert walk[0] == g.start;
    assert |walk| >= 2;
    assert (walk[0], walk[1]) in g.edges;
    assert walk[1] == m by {
      if walk[1] != m {
        assert (g.start, walk[1]) == (m, g.end);
      }
    }
    assert |walk| != 2 by {
      if |walk| == 2 {
        assert walk[|walk| - 1] == g.end;
        assert walk[1] == g.end;
      }
    }
    assert |walk| >= 3;
    assert (walk[1], walk[2]) in g.edges;
    assert walk[2] == g.end by {
      if walk[2] != g.end {
        assert (m, walk[2]) == (g.start, m);
      }
    }
    assert |walk| == 3 by {
      if |walk| > 3 {
        assert (walk[2], walk[3]) in g.edges;
        assert (g.end, walk[3]) == (g.start, m) || (g.end, walk[3]) == (m, g.end);
      }
    }
    assert walk == [walk[0], walk[1], walk[2]];
  }

  lemma SingleInteriorNodeAccepts(g: Graph, m: int, w: string)
    requires WF(g)
    requires InteriorNodes(g) == {m}
    requires g.labels[g.start] == Eps
    requires g.labels[g.end] == Eps
    requires g.edges == {(g.start, m), (m, g.end)}
    requires GraphAccepts(g, w)
    ensures Matches(g.labels[m], w)
  {
    var walk :| IsWalk(g, walk) && WalkMatches(g, walk, w);
    SingleInteriorWalkShape(g, m, walk);
    var splits: seq<nat> :| |splits| == |walk| + 1 &&
      splits[0] == 0 && splits[|walk|] == |w| &&
      (forall i :: 0 <= i < |walk| ==>
        var lo := splits[i]; var hi := splits[i + 1];
        lo <= hi <= |w| && Matches(g.labels[walk[i]], w[lo..hi]));
    assert walk == [g.start, m, g.end];
    assert Matches(g.labels[g.start], w[splits[0]..splits[1]]);
    assert Matches(g.labels[m], w[splits[1]..splits[2]]);
    assert Matches(g.labels[g.end], w[splits[2]..splits[3]]);
    assert splits[0] == 0;
    assert splits[3] == |w|;
    assert splits[1] == 0 by {
      assert w[splits[0]..splits[1]] == "";
    }
    assert splits[2] == |w| by {
      assert w[splits[2]..splits[3]] == "";
    }
    assert w[splits[1]..splits[2]] == w;
  }

  // ==================================================================================
  // Round 7: wiring everything into a real, executable, tested top-level method
  // ==================================================================================
  //
  // Rounds 1-6 built only GHOST machinery: predicates/ghost functions/lemmas proving
  // each contraction preserves AllLabelsSore/PairwiseDisjointLabels/GraphAccepts, but
  // nothing that could actually run. This round adds InferViaBigramGraph, an executable
  // `method` that repeatedly applies whichever of the three easy, decidable
  // contractions (simple-path, general OR-merge, optional - in that priority order) is
  // currently findable, falling back to CollapseAllGraph whenever none of the three
  // applies and interior nodes remain, until exactly one interior node is left; that
  // node's label (after a small canonicalization step, see below) is the answer.
  // Precision/tightness is explicitly NOT this round's goal (CollapseAllGraph may fire
  // on genuinely cyclic OR acyclic leftover structure alike, producing a looser regex
  // than a real SCC-detection pass would) - only soundness and single-occurrence-ness
  // are proved, matching this file's existing "propose heuristically, prove whatever
  // was proposed is sound" separation of concerns. Real SCC-detection (Tarjan's
  // algorithm or similar, to tighten results on genuinely cyclic inputs) remains
  // deferred future work, exactly as Round 5/6's comments already say.
  //
  // The main new difficulty, not present in Rounds 1-6 at all: Rounds 1-6's
  // ContractSimplePathGraph/MergeAnyGraph/MakeOptionalGraph/ContractSCCGraph/
  // CollapseAllGraph are all `ghost function`s (their fresh-node allocation goes
  // through FreshNode/SetMax, which pick set elements via `:|` inside a *function*
  // body - not compilable), so a real executable method cannot call them directly to
  // build its graph. Rather than touch any of that already-proven ghost code (risking
  // regressions in 2000+ lines of existing proof), this round adds a PARALLEL
  // executable construction for each transform (ExecContractSimplePath/ExecMergeAny/
  // ExecMakeOptional/ExecCollapseAll below) that computes the identical graph value at
  // runtime, and bridges each one to its ghost counterpart via a plain equality
  // (`g2 == ContractSimplePathGraph(g, x, y)`, etc.) established by proving the
  // executable fresh-node search (ExecFreshNode, a `method` - methods CAN compile `:|`
  // over a finite domain) computes the exact same value as the ghost FreshNode
  // (ExecFreshNodeIsFreshNode, via SetMax's uniqueness as the dominating element of a
  // finite set). Once that equality is established, every already-proven Round 1-6
  // lemma (…WF/…AllLabelsSore/…PairwiseDisjoint/…Sound) applies directly to the
  // executable result by substitution - no new soundness proof machinery was needed,
  // only this bridge.
  //
  // The other new difficulty: SingleInteriorNodeAccepts (Round 6) needs the final
  // single-interior-node graph's edges to be EXACTLY {(start,m),(m,end)} - not
  // automatically true of whichever node ends up last, since (a) a node could still
  // carry a self-loop forward untouched if it was never chosen as a contraction
  // candidate (self-loops are explicitly excluded from all three easy contractions'
  // preconditions), and (b) a direct start->end "bypass" edge (arising whenever "" is
  // one of the samples together with other, non-empty samples) has no reason to have
  // been consumed by anything. Both are handled by a two-step canonicalization once the
  // main loop reaches a single interior node: if that node has a self-loop, one more
  // CollapseAllGraph application (contracting the singleton {m} into a fresh, and hence
  // as a matter of construction always self-loop-free, node) absorbs it via Star; if a
  // start->end bypass remains, CanMakeOptional now applies to the (self-loop-free)
  // node directly (proved via NoBackEdges, a new structural invariant below - no edge's
  // target is g.start and no edge's source is g.end, true of the base bigram graph and
  // preserved by every contraction essentially "for free" from fresh-node-ness alone -
  // maintained as a loop invariant so it is available at the end - combined with the
  // fact that some sample string in S is non-empty, whose accepted walk is then FORCED
  // to pass through the sole interior node, establishing both a start->m and an m->end
  // edge unconditionally) and removes it. Either way, the loop invariant AllLabelsSore
  // then gives IsSore(r) "for free", exactly as this file's Round 1 header predicted.

  // ---- Executable fresh-node search (a `method`, so `:|` over a finite set compiles) ----

  method ExecFreshNode(nodes: set<int>) returns (m: int)
    ensures nodes == {} ==> m == 0
    ensures nodes != {} ==> m - 1 in nodes && (forall x :: x in nodes ==> x <= m - 1)
    ensures m !in nodes
  {
    if nodes == {} {
      m := 0;
    } else {
      var x :| x in nodes;
      var mx := x;
      var seen := {x};
      var rem := nodes - {x};
      while rem != {}
        invariant seen + rem == nodes
        invariant mx in seen
        invariant forall y :: y in seen ==> y <= mx
        decreases rem
      {
        var y :| y in rem;
        rem := rem - {y};
        seen := seen + {y};
        if y > mx {
          mx := y;
        }
      }
      assert seen == nodes;
      m := mx + 1;
    }
  }

  lemma SetMaxUnique(s: set<int>, m1: int, m2: int)
    requires s != {}
    requires m1 in s && (forall x :: x in s ==> x <= m1)
    requires m2 in s && (forall x :: x in s ==> x <= m2)
    ensures m1 == m2
  {
  }

  // Bridges ExecFreshNode's runtime result to the ghost FreshNode/SetMax used inside
  // ContractSimplePathGraph/MergeAnyGraph/ContractSCCGraph's own definitions - this is
  // what lets the executable graph-builder methods below prove their output equals the
  // corresponding ghost function's result, and so directly inherit all of that ghost
  // function's already-proven properties.
  lemma ExecFreshNodeIsFreshNode(nodes: set<int>, m: int)
    requires nodes == {} ==> m == 0
    requires nodes != {} ==> m - 1 in nodes && (forall x :: x in nodes ==> x <= m - 1)
    ensures m == FreshNode(nodes)
  {
    if nodes != {} {
      var sm := SetMax(nodes);
      SetMaxUnique(nodes, m - 1, sm);
    }
  }

  // ---- Executable set-to-seq conversion (order is irrelevant - only used for search) ----

  method SetToSeqExec(s: set<int>) returns (r: seq<int>)
    ensures forall x :: x in r <==> x in s
    ensures forall i :: 0 <= i < |r| ==> r[i] in s
    ensures forall i, j :: 0 <= i < |r| && 0 <= j < |r| && i != j ==> r[i] != r[j]
  {
    r := [];
    var rem := s;
    while rem != {}
      invariant forall x :: x in r <==> x in (s - rem)
      invariant forall i, j :: 0 <= i < |r| && 0 <= j < |r| && i != j ==> r[i] != r[j]
      decreases rem
    {
      var x :| x in rem;
      assert x !in r by {
        assert x !in s - rem;
      }
      r := r + [x];
      rem := rem - {x};
    }
  }

  // ---- NoBackEdges: no edge targets g.start, no edge sources g.end. Holds of the base
  // bigram graph and is preserved by every contraction, essentially "for free" from
  // fresh-node-ness (the newly introduced node is never g.start/g.end, and the OTHER
  // endpoint of any into_m/outof_m edge is inherited from an already-NoBackEdges-
  // respecting old edge) - needed at the very end to pin down the final single-
  // interior-node graph's edge shape (see the big comment above).

  predicate NoBackEdges(g: Graph)
    requires WF(g)
  {
    (forall e :: e in g.edges ==> e.1 != g.start) &&
    (forall e :: e in g.edges ==> e.0 != g.end)
  }

  lemma BigramNoBackEdges(S: set<string>, g: Graph)
    requires WF(g)
    requires g.edges == EdgesOf(S)
    requires g.start == StartId && g.end == EndId
    ensures NoBackEdges(g)
  {
    forall e | e in g.edges ensures e.1 != g.start {
      EdgesOfMem(S, e);
      if exists w :: w in S && w != "" && e == (StartId, CharNode(w[0])) {
        var w :| w in S && w != "" && e == (StartId, CharNode(w[0]));
        CharNodeNotSentinel(w[0]);
      } else if exists w :: w in S && w != "" && e == (CharNode(w[|w| - 1]), EndId) {
      } else if exists w, i :: w in S && 0 <= i < |w| - 1 && e == (CharNode(w[i]), CharNode(w[i + 1])) {
        var w, i :| w in S && 0 <= i < |w| - 1 && e == (CharNode(w[i]), CharNode(w[i + 1]));
        CharNodeNotSentinel(w[i + 1]);
      } else {
        assert "" in S && e == (StartId, EndId);
      }
    }
    forall e | e in g.edges ensures e.0 != g.end {
      EdgesOfMem(S, e);
      if exists w :: w in S && w != "" && e == (StartId, CharNode(w[0])) {
      } else if exists w :: w in S && w != "" && e == (CharNode(w[|w| - 1]), EndId) {
        var w :| w in S && w != "" && e == (CharNode(w[|w| - 1]), EndId);
        CharNodeNotSentinel(w[|w| - 1]);
      } else if exists w, i :: w in S && 0 <= i < |w| - 1 && e == (CharNode(w[i]), CharNode(w[i + 1])) {
        var w, i :| w in S && 0 <= i < |w| - 1 && e == (CharNode(w[i]), CharNode(w[i + 1]));
        CharNodeNotSentinel(w[i]);
      } else {
        assert "" in S && e == (StartId, EndId);
      }
    }
  }

  lemma ContractSimplePathNoBackEdges(g: Graph, x: int, y: int)
    requires WF(g)
    requires CanContractSimplePath(g, x, y)
    requires NoBackEdges(g)
    ensures NoBackEdges(ContractSimplePathGraph(g, x, y))
  {
    var g' := ContractSimplePathGraph(g, x, y);
    var m := FreshNode(g.nodes);
    forall e | e in g'.edges ensures e.1 != g.start {
      if e.0 != m && e.1 != m {
      } else if e.1 == m {
      } else {
        var b :| b in g.nodes && (y, b) in g.edges && e == (m, b);
      }
    }
    forall e | e in g'.edges ensures e.0 != g.end {
      if e.0 != m && e.1 != m {
      } else if e.1 == m {
        var a :| a in g.nodes && (a, x) in g.edges && e == (a, m);
      } else {
      }
    }
  }

  lemma MergeAnyNoBackEdges(g: Graph, a: int, b: int)
    requires WF(g)
    requires CanMergeAny(g, a, b)
    requires NoBackEdges(g)
    ensures NoBackEdges(MergeAnyGraph(g, a, b))
  {
    var g' := MergeAnyGraph(g, a, b);
    var m := FreshNode(g.nodes);
    forall e | e in g'.edges ensures e.1 != g.start {
      if e.0 != m && e.1 != m {
      } else if e.1 == m {
      } else {
        var c :| c in g.nodes && ((a, c) in g.edges || (b, c) in g.edges) && e == (m, c);
      }
    }
    forall e | e in g'.edges ensures e.0 != g.end {
      if e.0 != m && e.1 != m {
      } else if e.1 == m {
        var p :| p in g.nodes && ((p, a) in g.edges || (p, b) in g.edges) && e == (p, m);
      } else {
      }
    }
  }

  lemma MakeOptionalNoBackEdges(g: Graph, v: int)
    requires WF(g)
    requires CanMakeOptional(g, v)
    requires NoBackEdges(g)
    ensures NoBackEdges(MakeOptionalGraph(g, v))
  {
  }

  lemma ContractSCCNoBackEdges(g: Graph, C: set<int>)
    requires WF(g)
    requires CanContractSCC(g, C)
    requires NoBackEdges(g)
    ensures NoBackEdges(ContractSCCGraph(g, C))
  {
    var g' := ContractSCCGraph(g, C);
    var m := FreshNode(g.nodes);
    forall e | e in g'.edges ensures e.1 != g.start {
      if e.0 != m && e.1 != m {
      } else if e.1 == m {
      } else {
        var q :| q in g.nodes && q !in C && (exists c :: c in C && (c, q) in g.edges) && e == (m, q);
      }
    }
    forall e | e in g'.edges ensures e.0 != g.end {
      if e.0 != m && e.1 != m {
      } else if e.1 == m {
        var p :| p in g.nodes && p !in C && (exists c :: c in C && (p, c) in g.edges) && e == (p, m);
      } else {
      }
    }
  }

  lemma CollapseAllNoBackEdges(g: Graph)
    requires WF(g)
    requires InteriorNodes(g) != {}
    requires NoBackEdges(g)
    ensures NoBackEdges(CollapseAllGraph(g))
  {
    ContractSCCNoBackEdges(g, InteriorNodes(g));
  }

  // A freshly-introduced merge node is never given a self-loop, regardless of which of
  // the three multi-node transforms produced it - into_m/outof_m only ever draw their
  // OTHER endpoint from the OLD node set, which m (being fresh) can never be a member
  // of, and "untouched" only ever contains OLD edges (which by definition of "old"
  // cannot mention m either).
  lemma ContractSCCNoSelfLoopOnFreshNode(g: Graph, C: set<int>)
    requires WF(g)
    requires CanContractSCC(g, C)
    ensures (FreshNode(g.nodes), FreshNode(g.nodes)) !in ContractSCCGraph(g, C).edges
  {
    var g' := ContractSCCGraph(g, C);
    var m := FreshNode(g.nodes);
    if (m, m) in g'.edges {
      if m !in C && m !in C {
        // it would have to be "untouched", but untouched edges are old edges, and m is
        // not an old node.
      }
    }
  }

  lemma CollapseAllNoSelfLoopOnFreshNode(g: Graph)
    requires WF(g)
    requires InteriorNodes(g) != {}
    ensures (FreshNode(g.nodes), FreshNode(g.nodes)) !in CollapseAllGraph(g).edges
  {
    ContractSCCNoSelfLoopOnFreshNode(g, InteriorNodes(g));
  }

  // ---- Small set-cardinality helpers, used below to justify the loop's termination ----

  lemma CardRemoveOne(s: set<int>, x: int)
    requires x in s
    ensures |s - {x}| == |s| - 1
  {
    assert s == (s - {x}) + {x};
  }

  lemma CardAddOne(s: set<int>, x: int)
    requires x !in s
    ensures |s + {x}| == |s| + 1
  {
  }

  lemma CardRemoveTwo(s: set<int>, x: int, y: int)
    requires x in s && y in s && x != y
    ensures |s - {x, y}| == |s| - 2
  {
    CardRemoveOne(s, x);
    CardRemoveOne(s - {x}, y);
    assert s - {x, y} == (s - {x}) - {y};
  }

  lemma CardEdgesRemoveNonempty(s: set<(int, int)>, t: set<(int, int)>)
    requires t <= s
    requires t != {}
    ensures |s - t| < |s|
  {
    var x :| x in t;
    assert x in s;
    assert s - t <= s - {x};
    assert |s - {x}| == |s| - 1 by {
      assert s == (s - {x}) + {x};
    }
    assert |s - t| <= |s - {x}|;
  }

  // ---- Interior-node-count bookkeeping for each transform's termination measure ----

  lemma InteriorNodesContractSimplePath(g: Graph, x: int, y: int)
    requires WF(g)
    requires CanContractSimplePath(g, x, y)
    ensures InteriorNodes(ContractSimplePathGraph(g, x, y)) == InteriorNodes(g) - {x, y} + {FreshNode(g.nodes)}
    ensures |InteriorNodes(ContractSimplePathGraph(g, x, y))| == |InteriorNodes(g)| - 1
  {
    var g' := ContractSimplePathGraph(g, x, y);
    var m := FreshNode(g.nodes);
    assert g'.nodes == g.nodes - {x, y} + {m};
    assert m != g.start && m != g.end;
    assert x != g.start && x != g.end && y != g.start && y != g.end;
    assert InteriorNodes(g') == InteriorNodes(g) - {x, y} + {m};
    assert x in InteriorNodes(g) && y in InteriorNodes(g) && x != y;
    assert m !in InteriorNodes(g);
    CardRemoveTwo(InteriorNodes(g), x, y);
    CardAddOne(InteriorNodes(g) - {x, y}, m);
  }

  lemma InteriorNodesMergeAny(g: Graph, a: int, b: int)
    requires WF(g)
    requires CanMergeAny(g, a, b)
    ensures InteriorNodes(MergeAnyGraph(g, a, b)) == InteriorNodes(g) - {a, b} + {FreshNode(g.nodes)}
    ensures |InteriorNodes(MergeAnyGraph(g, a, b))| == |InteriorNodes(g)| - 1
  {
    var g' := MergeAnyGraph(g, a, b);
    var m := FreshNode(g.nodes);
    assert g'.nodes == g.nodes - {a, b} + {m};
    assert m != g.start && m != g.end;
    assert a != g.start && a != g.end && b != g.start && b != g.end;
    assert InteriorNodes(g') == InteriorNodes(g) - {a, b} + {m};
    assert a in InteriorNodes(g) && b in InteriorNodes(g) && a != b;
    assert m !in InteriorNodes(g);
    CardRemoveTwo(InteriorNodes(g), a, b);
    CardAddOne(InteriorNodes(g) - {a, b}, m);
  }

  lemma InteriorNodesMakeOptional(g: Graph, v: int)
    requires WF(g)
    requires CanMakeOptional(g, v)
    ensures InteriorNodes(MakeOptionalGraph(g, v)) == InteriorNodes(g)
  {
  }

  lemma EdgeCountMakeOptional(g: Graph, v: int)
    requires WF(g)
    requires CanMakeOptional(g, v)
    ensures |MakeOptionalGraph(g, v).edges| < |g.edges|
  {
    var g' := MakeOptionalGraph(g, v);
    var bypass := set p, c | p in Preds(g, v) && c in Succs(g, v) :: (p, c);
    assert g'.edges == g.edges - bypass;
    assert bypass <= g.edges by {
      forall e | e in bypass ensures e in g.edges {
        var p, c :| p in Preds(g, v) && c in Succs(g, v) && e == (p, c);
        assert (p, c) in g.edges;
      }
    }
    var p0 :| p0 in Preds(g, v);
    var c0 :| c0 in Succs(g, v);
    assert (p0, c0) in bypass;
    assert bypass != {};
    CardEdgesRemoveNonempty(g.edges, bypass);
  }

  lemma InteriorNodesCollapseAll(g: Graph)
    requires WF(g)
    requires InteriorNodes(g) != {}
    ensures InteriorNodes(CollapseAllGraph(g)) == {FreshNode(g.nodes)}
    ensures |InteriorNodes(CollapseAllGraph(g))| == 1
  {
    var C := InteriorNodes(g);
    var g' := ContractSCCGraph(g, C);
    var m := FreshNode(g.nodes);
    assert g'.nodes == g.nodes - C + {m};
    assert m != g.start && m != g.end;
    assert InteriorNodes(g') == InteriorNodes(g) - C + {m};
    assert InteriorNodes(g) - C == {};
    assert InteriorNodes(g') == {m};
  }

  // ---- Matches-equivalence infrastructure ----
  //
  // ContractSCCGraph(g, C)'s label at the merged node is Star(UnionAllLabels(g, cs))
  // for cs := SetToSeq(C) - a ghost function using `:|` internally, so an executable
  // builder cannot reproduce that EXACT sequence (only an arbitrary, but equally valid,
  // enumeration of the same set C). Rather than re-derive the whole SCC
  // soundness/single-occurrence proof for an arbitrary enumeration (duplicating
  // CollapseStepsPreserves and friends), this shows the executable construction's label
  // at the merged node is language-EQUIVALENT (same Matches behavior) to
  // ContractSCCGraph's, and that GraphAccepts is preserved when a single node's label is
  // swapped for a Matches-equivalent one - which lets the executable result inherit
  // ContractSCCSound directly, no matter which enumeration order it happened to use.

  lemma UnionAllLabelsMatchesIff(g: Graph, cs: seq<int>, s: string)
    requires WF(g)
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    ensures Matches(UnionAllLabels(g, cs), s) <==> (exists i :: 0 <= i < |cs| && Matches(g.labels[cs[i]], s))
    decreases cs
  {
    if cs == [] {
    } else if |cs| == 1 {
    } else {
      UnionAllLabelsMatchesIff(g, cs[1..], s);
      forall i | 0 <= i < |cs[1..]| && Matches(g.labels[cs[1..][i]], s)
        ensures exists j :: 0 <= j < |cs| && Matches(g.labels[cs[j]], s)
      {
        assert cs[1..][i] == cs[i + 1];
      }
    }
  }

  lemma UnionAllLabelsPermInvariant(g: Graph, cs1: seq<int>, cs2: seq<int>, s: string)
    requires WF(g)
    requires forall i :: 0 <= i < |cs1| ==> cs1[i] in g.nodes
    requires forall i :: 0 <= i < |cs2| ==> cs2[i] in g.nodes
    requires forall x :: x in cs1 <==> x in cs2
    ensures Matches(UnionAllLabels(g, cs1), s) <==> Matches(UnionAllLabels(g, cs2), s)
  {
    UnionAllLabelsMatchesIff(g, cs1, s);
    UnionAllLabelsMatchesIff(g, cs2, s);
    if exists i :: 0 <= i < |cs1| && Matches(g.labels[cs1[i]], s) {
      var i :| 0 <= i < |cs1| && Matches(g.labels[cs1[i]], s);
      assert cs1[i] in cs1;
      assert cs1[i] in cs2;
      var j :| 0 <= j < |cs2| && cs2[j] == cs1[i];
    }
    if exists j :: 0 <= j < |cs2| && Matches(g.labels[cs2[j]], s) {
      var j :| 0 <= j < |cs2| && Matches(g.labels[cs2[j]], s);
      assert cs2[j] in cs2;
      assert cs2[j] in cs1;
      var i :| 0 <= i < |cs1| && cs1[i] == cs2[j];
    }
  }

  lemma MatchesEquivStar(r1: Regex, r2: Regex, s: string)
    requires forall t :: Matches(r1, t) <==> Matches(r2, t)
    ensures Matches(Star(r1), s) <==> Matches(Star(r2), s)
    decreases |s|
  {
    if s == "" {
    } else {
      forall i | 0 < i <= |s|
        ensures (Matches(r1, s[..i]) && Matches(Star(r1), s[i..])) <==>
                (Matches(r2, s[..i]) && Matches(Star(r2), s[i..]))
      {
        MatchesEquivStar(r1, r2, s[i..]);
      }
    }
  }

  // If g1 and g2 agree on everything except possibly the label of one node m (and even
  // there only up to Matches-equivalence), they accept exactly the same strings - the
  // walk/split witness for one is literally the same witness for the other, since
  // WalkMatches/GraphAccepts only ever inspect labels via Matches calls.
  lemma GraphAcceptsRelabelEquiv(g1: Graph, g2: Graph, m: int, w: string)
    requires WF(g1) && WF(g2)
    requires g1.nodes == g2.nodes
    requires g1.edges == g2.edges
    requires g1.start == g2.start && g1.end == g2.end
    requires m in g1.nodes
    requires forall n :: n in g1.nodes && n != m ==> g1.labels[n] == g2.labels[n]
    requires forall s :: Matches(g1.labels[m], s) <==> Matches(g2.labels[m], s)
    ensures GraphAccepts(g1, w) <==> GraphAccepts(g2, w)
  {
    if GraphAccepts(g1, w) {
      var walk :| IsWalk(g1, walk) && WalkMatches(g1, walk, w);
      assert IsWalk(g2, walk);
      var splits: seq<nat> :| |splits| == |walk| + 1 &&
        splits[0] == 0 && splits[|walk|] == |w| &&
        (forall i :: 0 <= i < |walk| ==>
          var lo := splits[i]; var hi := splits[i + 1];
          lo <= hi <= |w| && Matches(g1.labels[walk[i]], w[lo..hi]));
      assert WalkMatches(g2, walk, w) by {
        forall i | 0 <= i < |walk|
          ensures var lo := splits[i]; var hi := splits[i + 1];
                  lo <= hi <= |w| && Matches(g2.labels[walk[i]], w[lo..hi])
        {
        }
      }
    }
    if GraphAccepts(g2, w) {
      var walk :| IsWalk(g2, walk) && WalkMatches(g2, walk, w);
      assert IsWalk(g1, walk);
      var splits: seq<nat> :| |splits| == |walk| + 1 &&
        splits[0] == 0 && splits[|walk|] == |w| &&
        (forall i :: 0 <= i < |walk| ==>
          var lo := splits[i]; var hi := splits[i + 1];
          lo <= hi <= |w| && Matches(g2.labels[walk[i]], w[lo..hi]));
      assert WalkMatches(g1, walk, w) by {
        forall i | 0 <= i < |walk|
          ensures var lo := splits[i]; var hi := splits[i + 1];
                  lo <= hi <= |w| && Matches(g1.labels[walk[i]], w[lo..hi])
        {
        }
      }
    }
  }

  // ---- Executable graph builders ----
  //
  // Each of these computes, at runtime, the exact same Graph value as the corresponding
  // ghost function (proved via the `ensures ... == ...Graph(...)` clause below), by
  // using ExecFreshNode (a method, so its internal `:|` compiles) bridged to FreshNode
  // via ExecFreshNodeIsFreshNode, then mirroring the ghost function's own
  // nodes'/labels'/edges' construction verbatim. Everything each ghost function's
  // lemmas (…WF/…AllLabelsSore/…PairwiseDisjoint/…Sound) already proved about
  // ContractSimplePathGraph/MergeAnyGraph/MakeOptionalGraph therefore applies directly
  // to these methods' results by substitution.

  method ExecContractSimplePath(g: Graph, x: int, y: int) returns (g2: Graph)
    requires WF(g)
    requires CanContractSimplePath(g, x, y)
    ensures g2 == ContractSimplePathGraph(g, x, y)
  {
    var m := ExecFreshNode(g.nodes);
    ExecFreshNodeIsFreshNode(g.nodes, m);
    var nodes' := g.nodes - {x, y} + {m};
    var labels' := (map n | n in g.nodes - {x, y} :: n := g.labels[n])
                     [m := Concat(g.labels[x], g.labels[y])];
    var untouched := set e | e in g.edges && e.0 != x && e.0 != y && e.1 != x && e.1 != y :: e;
    var into_m := set a | a in g.nodes && (a, x) in g.edges :: (a, m);
    var outof_m := set b | b in g.nodes && (y, b) in g.edges :: (m, b);
    g2 := Graph(nodes', labels', untouched + into_m + outof_m, g.start, g.end);
  }

  method ExecMergeAny(g: Graph, a: int, b: int) returns (g2: Graph)
    requires WF(g)
    requires CanMergeAny(g, a, b)
    ensures g2 == MergeAnyGraph(g, a, b)
  {
    var m := ExecFreshNode(g.nodes);
    ExecFreshNodeIsFreshNode(g.nodes, m);
    var nodes' := g.nodes - {a, b} + {m};
    var labels' := (map n | n in g.nodes - {a, b} :: n := g.labels[n])
                     [m := Union(g.labels[a], g.labels[b])];
    var untouched := set e | e in g.edges && e.0 != a && e.0 != b && e.1 != a && e.1 != b :: e;
    var into_m := set p | p in g.nodes && ((p, a) in g.edges || (p, b) in g.edges) :: (p, m);
    var outof_m := set c | c in g.nodes && ((a, c) in g.edges || (b, c) in g.edges) :: (m, c);
    g2 := Graph(nodes', labels', untouched + into_m + outof_m, g.start, g.end);
  }

  method ExecMakeOptional(g: Graph, v: int) returns (g2: Graph)
    requires WF(g)
    requires CanMakeOptional(g, v)
    ensures g2 == MakeOptionalGraph(g, v)
  {
    var labels' := g.labels[v := Opt(g.labels[v])];
    var bypass := set p, c | p in Preds(g, v) && c in Succs(g, v) :: (p, c);
    g2 := Graph(g.nodes, labels', g.edges - bypass, g.start, g.end);
  }

  // ExecCollapseAll cannot be proved equal to CollapseAllGraph(g) bit-for-bit: both
  // build their merged node's label via UnionAllLabels(g, cs) for some enumeration cs of
  // InteriorNodes(g), but CollapseAllGraph's cs comes from the ghost SetToSeq (an
  // unpredictable, unreproducible `:|` pick), while this method uses SetToSeqExec's own
  // (equally valid, but generally different) enumeration order. Every OTHER field
  // (nodes, edges, start, end, and every other node's label) is built with the exact
  // same formula in both, so the two graphs are identical except possibly at the merged
  // node's label - and even there, only up to Matches-equivalence (both are a Union
  // over the same underlying node set, just folded in a different order), which is all
  // GraphAccepts preservation actually needs (see GraphAcceptsRelabelEquiv above). WF,
  // AllLabelsSore, PairwiseDisjointLabels, NoBackEdges and single-occurrence at the
  // merged node are all reproved directly here instead (each already has a fully
  // cs-generic proof available - UnionAllLabelsIsSore/UnionAllLabelsSymbolsMem take an
  // arbitrary enumeration as a parameter already), so none of that needs to go through
  // the ghost function at all. The construction itself is factored into named
  // (non-ghost, so both the executable method and its proof lemmas can share the exact
  // same expressions) functions below, and its proof is split into one lemma per
  // ensures clause - bundling everything into a single method body timed out, exactly
  // the same failure mode this file's Round 1 header comment already warns about for
  // BuildBigramGraph.

  function CollapseUntouched(g: Graph, C: set<int>): set<(int, int)>
    requires WF(g)
  {
    set e | e in g.edges && e.0 !in C && e.1 !in C :: e
  }

  function CollapseIntoM(g: Graph, C: set<int>, m: int): set<(int, int)>
    requires WF(g)
  {
    set p | p in g.nodes && p !in C && (exists c :: c in C && (p, c) in g.edges) :: (p, m)
  }

  function CollapseOutOfM(g: Graph, C: set<int>, m: int): set<(int, int)>
    requires WF(g)
  {
    set q | q in g.nodes && q !in C && (exists c :: c in C && (c, q) in g.edges) :: (m, q)
  }

  function CollapseNodes(g: Graph, C: set<int>, m: int): set<int>
    requires WF(g)
  {
    g.nodes - C + {m}
  }

  function CollapseEdges(g: Graph, C: set<int>, m: int): set<(int, int)>
    requires WF(g)
  {
    CollapseUntouched(g, C) + CollapseIntoM(g, C, m) + CollapseOutOfM(g, C, m)
  }

  function CollapseLabels(g: Graph, C: set<int>, m: int, cs: seq<int>): map<int, Regex>
    requires WF(g)
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
  {
    (map n | n in g.nodes - C :: n := g.labels[n])[m := Star(UnionAllLabels(g, cs))]
  }

  // ExecCollapseAll's postcondition needs a ghost expression it can name without
  // re-running ExecFreshNode (which, being nondeterministic in its choice of witness at
  // each loop step, cannot itself appear in a `function`/ghost expression position) -
  // this is exactly FreshNode(nodes), exposed under a name that makes the connection to
  // ExecFreshNode's own runtime result explicit at call sites via the lemma below.
  ghost function ExecFreshNodeGhostValue(nodes: set<int>): int
  {
    FreshNode(nodes)
  }

  lemma ExecFreshNodeGhostValueEq(nodes: set<int>, m: int)
    requires nodes == {} ==> m == 0
    requires nodes != {} ==> m - 1 in nodes && (forall x :: x in nodes ==> x <= m - 1)
    ensures m == ExecFreshNodeGhostValue(nodes)
  {
    ExecFreshNodeIsFreshNode(nodes, m);
  }

  lemma ExecCollapseAllWF(g: Graph, C: set<int>, m: int, cs: seq<int>, g2: Graph)
    requires WF(g)
    requires CanContractSCC(g, C)
    requires m !in g.nodes
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    requires g2 == Graph(CollapseNodes(g, C, m), CollapseLabels(g, C, m, cs), CollapseEdges(g, C, m), g.start, g.end)
    ensures WF(g2)
  {
    assert g2.labels.Keys == g2.nodes;
    forall e | e in g2.edges ensures e.0 in g2.nodes && e.1 in g2.nodes {
      if e.0 != m && e.1 != m {
      } else if e.1 == m {
        var p :| p in g.nodes && p !in C && (exists c :: c in C && (p, c) in g.edges) && e == (p, m);
      } else {
        var q :| q in g.nodes && q !in C && (exists c :: c in C && (c, q) in g.edges) && e == (m, q);
      }
    }
  }

  lemma ExecCollapseAllSoreDisjoint(g: Graph, C: set<int>, m: int, cs: seq<int>, g2: Graph)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanContractSCC(g, C)
    requires m !in g.nodes
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    requires forall i, j :: 0 <= i < |cs| && 0 <= j < |cs| && i != j ==> cs[i] != cs[j]
    requires forall x :: x in cs <==> x in C
    requires g2 == Graph(CollapseNodes(g, C, m), CollapseLabels(g, C, m, cs), CollapseEdges(g, C, m), g.start, g.end)
    ensures WF(g2)
    ensures AllLabelsSore(g2)
    ensures PairwiseDisjointLabels(g2)
  {
    ExecCollapseAllWF(g, C, m, cs, g2);
    UnionAllLabelsIsSore(g, cs);
    StarIsSore(UnionAllLabels(g, cs));
    forall n | n in g2.nodes ensures IsSore(g2.labels[n]) {
    }
    forall n1, n2 | n1 in g2.nodes && n2 in g2.nodes && n1 != n2
      ensures forall ch :: Symbols(g2.labels[n1])[ch] == 0 || Symbols(g2.labels[n2])[ch] == 0
    {
      if n1 == m {
        assert n2 in g.nodes - C;
        forall ch ensures Symbols(g2.labels[n1])[ch] == 0 || Symbols(g2.labels[n2])[ch] == 0 {
          if Symbols(g2.labels[n1])[ch] > 0 {
            UnionAllLabelsSymbolsMem(g, cs, ch);
            var idx :| 0 <= idx < |cs| && ch in Symbols(g.labels[cs[idx]]);
            assert cs[idx] in C && cs[idx] in g.nodes && cs[idx] != n2;
            assert Symbols(g.labels[cs[idx]])[ch] == 0 || Symbols(g.labels[n2])[ch] == 0;
          }
        }
      } else if n2 == m {
        assert n1 in g.nodes - C;
        forall ch ensures Symbols(g2.labels[n1])[ch] == 0 || Symbols(g2.labels[n2])[ch] == 0 {
          if Symbols(g2.labels[n2])[ch] > 0 {
            UnionAllLabelsSymbolsMem(g, cs, ch);
            var idx :| 0 <= idx < |cs| && ch in Symbols(g.labels[cs[idx]]);
            assert cs[idx] in C && cs[idx] in g.nodes && cs[idx] != n1;
            assert Symbols(g.labels[cs[idx]])[ch] == 0 || Symbols(g.labels[n1])[ch] == 0;
          }
        }
      }
    }
  }

  lemma ExecCollapseAllNoBackEdges(g: Graph, C: set<int>, m: int, cs: seq<int>, g2: Graph)
    requires WF(g)
    requires NoBackEdges(g)
    requires CanContractSCC(g, C)
    requires m !in g.nodes
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    requires g2 == Graph(CollapseNodes(g, C, m), CollapseLabels(g, C, m, cs), CollapseEdges(g, C, m), g.start, g.end)
    ensures WF(g2)
    ensures NoBackEdges(g2)
  {
    ExecCollapseAllWF(g, C, m, cs, g2);
    forall e | e in g2.edges ensures e.1 != g.start {
      if e.0 != m && e.1 != m {
      } else if e.1 == m {
      } else {
        var q :| q in g.nodes && q !in C && (exists c :: c in C && (c, q) in g.edges) && e == (m, q);
      }
    }
    forall e | e in g2.edges ensures e.0 != g.end {
      if e.0 != m && e.1 != m {
      } else if e.1 == m {
        var p :| p in g.nodes && p !in C && (exists c :: c in C && (p, c) in g.edges) && e == (p, m);
      } else {
      }
    }
  }

  lemma ExecCollapseAllInterior(g: Graph, C: set<int>, m: int, cs: seq<int>, g2: Graph)
    requires WF(g)
    requires CanContractSCC(g, C)
    requires C == InteriorNodes(g)
    requires m !in g.nodes
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    requires g2 == Graph(CollapseNodes(g, C, m), CollapseLabels(g, C, m, cs), CollapseEdges(g, C, m), g.start, g.end)
    ensures WF(g2)
    ensures InteriorNodes(g2) == {m}
    ensures (m, m) !in g2.edges
  {
    ExecCollapseAllWF(g, C, m, cs, g2);
    assert m != g.start && m != g.end;
    assert InteriorNodes(g) - C == {};
    if (m, m) in g2.edges {
      assert m !in C;
    }
  }

  lemma ExecCollapseAllSentinels(g: Graph, C: set<int>, m: int, cs: seq<int>, g2: Graph)
    requires WF(g)
    requires CanContractSCC(g, C)
    requires m !in g.nodes
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    requires g2 == Graph(CollapseNodes(g, C, m), CollapseLabels(g, C, m, cs), CollapseEdges(g, C, m), g.start, g.end)
    ensures WF(g2)
    ensures g.start in g2.nodes && g.end in g2.nodes
    ensures g2.labels[g.start] == g.labels[g.start]
    ensures g2.labels[g.end] == g.labels[g.end]
  {
    ExecCollapseAllWF(g, C, m, cs, g2);
    assert g.start !in C && g.end !in C;
  }

  lemma ExecCollapseAllSoundOne(g: Graph, C: set<int>, m: int, cs: seq<int>, g2: Graph, w: string)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanContractSCC(g, C)
    requires m !in g.nodes
    requires m == FreshNode(g.nodes)
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    requires forall x :: x in cs <==> x in C
    requires g2 == Graph(CollapseNodes(g, C, m), CollapseLabels(g, C, m, cs), CollapseEdges(g, C, m), g.start, g.end)
    requires GraphAccepts(g, w)
    ensures WF(g2)
    ensures GraphAccepts(g2, w)
  {
    ExecCollapseAllWF(g, C, m, cs, g2);
    ContractSCCSound(g, C, w);
    var gGhost := ContractSCCGraph(g, C);
    var csGhost := SetToSeq(C);
    assert gGhost.nodes == g2.nodes;
    assert gGhost.edges == g2.edges;
    assert gGhost.start == g2.start && gGhost.end == g2.end;
    assert forall n :: n in gGhost.nodes && n != m ==> gGhost.labels[n] == g2.labels[n];
    assert forall s :: Matches(gGhost.labels[m], s) <==> Matches(g2.labels[m], s) by {
      assert gGhost.labels[m] == Star(UnionAllLabels(g, csGhost));
      assert g2.labels[m] == Star(UnionAllLabels(g, cs));
      forall s ensures Matches(Star(UnionAllLabels(g, csGhost)), s) <==> Matches(Star(UnionAllLabels(g, cs)), s) {
        assert forall t :: Matches(UnionAllLabels(g, csGhost), t) <==> Matches(UnionAllLabels(g, cs), t) by {
          forall t ensures Matches(UnionAllLabels(g, csGhost), t) <==> Matches(UnionAllLabels(g, cs), t) {
            UnionAllLabelsPermInvariant(g, csGhost, cs, t);
          }
        }
        MatchesEquivStar(UnionAllLabels(g, csGhost), UnionAllLabels(g, cs), s);
      }
    }
    GraphAcceptsRelabelEquiv(gGhost, g2, m, w);
  }

  method ExecCollapseAll(g: Graph) returns (g2: Graph)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires NoBackEdges(g)
    requires InteriorNodes(g) != {}
    ensures WF(g2)
    ensures AllLabelsSore(g2)
    ensures PairwiseDisjointLabels(g2)
    ensures NoBackEdges(g2)
    ensures InteriorNodes(g2) == {ExecFreshNodeGhostValue(g.nodes)}
    ensures (ExecFreshNodeGhostValue(g.nodes), ExecFreshNodeGhostValue(g.nodes)) !in g2.edges
    ensures g.start in g2.nodes && g.end in g2.nodes
    ensures g2.start == g.start
    ensures g2.end == g.end
    ensures g2.labels[g.start] == g.labels[g.start]
    ensures g2.labels[g.end] == g.labels[g.end]
    ensures forall w :: GraphAccepts(g, w) ==> GraphAccepts(g2, w)
  {
    var C := InteriorNodes(g);
    var cs := SetToSeqExec(C);
    var m := ExecFreshNode(g.nodes);
    ExecFreshNodeIsFreshNode(g.nodes, m);
    ExecFreshNodeGhostValueEq(g.nodes, m);

    g2 := Graph(CollapseNodes(g, C, m), CollapseLabels(g, C, m, cs), CollapseEdges(g, C, m), g.start, g.end);

    ExecCollapseAllSoreDisjoint(g, C, m, cs, g2);
    ExecCollapseAllNoBackEdges(g, C, m, cs, g2);
    ExecCollapseAllInterior(g, C, m, cs, g2);
    ExecCollapseAllSentinels(g, C, m, cs, g2);
    forall w | GraphAccepts(g, w) ensures GraphAccepts(g2, w) {
      ExecCollapseAllSoundOne(g, C, m, cs, g2, w);
    }
  }

  // ---- Executable search: "is one of the three easy contractions currently
  // findable, and where" - a straightforward double loop (single loop for the
  // one-node search) over an enumeration of g.nodes, checking the corresponding
  // Can... predicate (itself a plain, non-ghost predicate, so directly callable at
  // runtime) for each candidate, short-circuiting on the first hit. Exact search
  // order doesn't matter for correctness - any valid witness works.

  method FindSimplePathPair(g: Graph) returns (found: bool, x: int, y: int)
    requires WF(g)
    ensures found ==> CanContractSimplePath(g, x, y)
  {
    found := false;
    x := 0;
    y := 0;
    var xs := SetToSeqExec(g.nodes);
    var i := 0;
    while i < |xs| && !found
      invariant 0 <= i <= |xs|
      invariant found ==> CanContractSimplePath(g, x, y)
    {
      var j := 0;
      while j < |xs| && !found
        invariant 0 <= j <= |xs|
        invariant found ==> CanContractSimplePath(g, x, y)
      {
        if CanContractSimplePath(g, xs[i], xs[j]) {
          found := true;
          x := xs[i];
          y := xs[j];
        }
        j := j + 1;
      }
      i := i + 1;
    }
  }

  // Tried BEFORE FindMergePair (see Round 10 header comment): the safe, "lossless"
  // exact-overlap case, kept in the same iteration-based search style as the other
  // Find... methods here. CanMergeExact's definition already includes CanMergeAny(g,a,b)
  // as a conjunct, so the second ensures clause follows immediately from the first.
  method FindExactMergePair(g: Graph) returns (found: bool, a: int, b: int)
    requires WF(g)
    ensures found ==> CanMergeExact(g, a, b)
    ensures found ==> CanMergeAny(g, a, b)
  {
    found := false;
    a := 0;
    b := 0;
    var xs := SetToSeqExec(g.nodes);
    var i := 0;
    while i < |xs| && !found
      invariant 0 <= i <= |xs|
      invariant found ==> CanMergeExact(g, a, b)
      invariant found ==> CanMergeAny(g, a, b)
    {
      var j := 0;
      while j < |xs| && !found
        invariant 0 <= j <= |xs|
        invariant found ==> CanMergeExact(g, a, b)
        invariant found ==> CanMergeAny(g, a, b)
      {
        if CanMergeExact(g, xs[i], xs[j]) {
          found := true;
          a := xs[i];
          b := xs[j];
        }
        j := j + 1;
      }
      i := i + 1;
    }
  }

  // The bare, arbitrary/lossy CanMergeAny search - demoted (Round 10) to run only after
  // FindExactMergePair (and everything else safer) has failed; see this file's Round 10
  // header comment.
  method FindMergePair(g: Graph) returns (found: bool, a: int, b: int)
    requires WF(g)
    ensures found ==> CanMergeAny(g, a, b)
  {
    found := false;
    a := 0;
    b := 0;
    var xs := SetToSeqExec(g.nodes);
    var i := 0;
    while i < |xs| && !found
      invariant 0 <= i <= |xs|
      invariant found ==> CanMergeAny(g, a, b)
    {
      var j := 0;
      while j < |xs| && !found
        invariant 0 <= j <= |xs|
        invariant found ==> CanMergeAny(g, a, b)
      {
        if CanMergeAny(g, xs[i], xs[j]) {
          found := true;
          a := xs[i];
          b := xs[j];
        }
        j := j + 1;
      }
      i := i + 1;
    }
  }

  method FindOptionalNode(g: Graph) returns (found: bool, v: int)
    requires WF(g)
    ensures found ==> CanMakeOptional(g, v)
  {
    found := false;
    v := 0;
    var xs := SetToSeqExec(g.nodes);
    var i := 0;
    while i < |xs| && !found
      invariant 0 <= i <= |xs|
      invariant found ==> CanMakeOptional(g, v)
    {
      if CanMakeOptional(g, xs[i]) {
        found := true;
        v := xs[i];
      }
      i := i + 1;
    }
  }

  // ---- Sentinel-label/endpoint preservation for the three exact-equality transforms ----
  // (ExecCollapseAll's own version of this, ExecCollapseAllSentinels, already exists above.)

  lemma ContractSimplePathSentinels(g: Graph, x: int, y: int)
    requires WF(g)
    requires CanContractSimplePath(g, x, y)
    ensures WF(ContractSimplePathGraph(g, x, y))
    ensures ContractSimplePathGraph(g, x, y).start == g.start
    ensures ContractSimplePathGraph(g, x, y).end == g.end
    ensures ContractSimplePathGraph(g, x, y).labels[g.start] == g.labels[g.start]
    ensures ContractSimplePathGraph(g, x, y).labels[g.end] == g.labels[g.end]
  {
    ContractSimplePathWF(g, x, y);
  }

  lemma MergeAnySentinels(g: Graph, a: int, b: int)
    requires WF(g)
    requires CanMergeAny(g, a, b)
    ensures WF(MergeAnyGraph(g, a, b))
    ensures MergeAnyGraph(g, a, b).start == g.start
    ensures MergeAnyGraph(g, a, b).end == g.end
    ensures MergeAnyGraph(g, a, b).labels[g.start] == g.labels[g.start]
    ensures MergeAnyGraph(g, a, b).labels[g.end] == g.labels[g.end]
  {
    MergeAnyWF(g, a, b);
  }

  lemma MakeOptionalSentinels(g: Graph, v: int)
    requires WF(g)
    requires CanMakeOptional(g, v)
    ensures WF(MakeOptionalGraph(g, v))
    ensures MakeOptionalGraph(g, v).start == g.start
    ensures MakeOptionalGraph(g, v).end == g.end
    ensures MakeOptionalGraph(g, v).labels[g.start] == g.labels[g.start]
    ensures MakeOptionalGraph(g, v).labels[g.end] == g.labels[g.end]
  {
    MakeOptionalWF(g, v);
  }

  // ---- Walk-shape reasoning, used only once the main loop has reduced the graph to a
  // single interior node, to pin down that graph's edges exactly (see the "finishing"
  // comment on InferViaBigramGraph below). ----

  lemma StartOnlyAtFront(g: Graph, walk: seq<int>)
    requires WF(g)
    requires NoBackEdges(g)
    requires IsWalk(g, walk)
    ensures forall i :: 0 < i < |walk| ==> walk[i] != g.start
  {
    forall i | 0 < i < |walk| ensures walk[i] != g.start {
      assert (walk[i - 1], walk[i]) in g.edges;
    }
  }

  lemma EndOnlyAtBack(g: Graph, walk: seq<int>)
    requires WF(g)
    requires NoBackEdges(g)
    requires IsWalk(g, walk)
    ensures forall i :: 0 <= i < |walk| - 1 ==> walk[i] != g.end
  {
    forall i | 0 <= i < |walk| - 1 ensures walk[i] != g.end {
      assert (walk[i], walk[i + 1]) in g.edges;
    }
  }

  lemma SingletonSetChar(s: set<int>, m: int)
    requires |s| == 1
    requires m in s
    ensures s == {m}
  {
    forall y | y in s ensures y == m {
      if y != m {
        assert {y, m} <= s;
        assert |{y, m}| == 2;
        assert s == {y, m} + (s - {y, m});
        assert |s| == |{y, m}| + |s - {y, m}|;
      }
    }
  }

  // Once the graph has been reduced to a single interior node m, and some sample
  // string is non-empty, the walk accepting it cannot be the trivial [start,end]
  // 2-step walk (that can only match "", both sentinels being Eps) - so it must pass
  // through an interior node, which (there being only one) must be m; combined with
  // NoBackEdges (which forces g.start to appear only at position 0 of any walk, and
  // g.end only at the last position), this pins down walk[1] and walk[|walk|-2] as m
  // exactly, giving both (g.start, m) and (m, g.end) as real edges.
  lemma FinalNodeHasNeighbors(g: Graph, m: int, w0: string)
    requires WF(g)
    requires NoBackEdges(g)
    requires InteriorNodes(g) == {m}
    requires g.labels[g.start] == Eps
    requires g.labels[g.end] == Eps
    requires w0 != ""
    requires GraphAccepts(g, w0)
    ensures (g.start, m) in g.edges
    ensures (m, g.end) in g.edges
  {
    assert g.start in g.nodes && g.end in g.nodes;
    assert g.nodes == InteriorNodes(g) + {g.start, g.end};
    assert g.nodes == {g.start, g.end, m};
    var walk :| IsWalk(g, walk) && WalkMatches(g, walk, w0);
    var splits: seq<nat> :| |splits| == |walk| + 1 &&
      splits[0] == 0 && splits[|walk|] == |w0| &&
      (forall i :: 0 <= i < |walk| ==>
        var lo := splits[i]; var hi := splits[i + 1];
        lo <= hi <= |w0| && Matches(g.labels[walk[i]], w0[lo..hi]));
    assert |walk| != 2 by {
      if |walk| == 2 {
        assert walk[0] == g.start && walk[1] == g.end;
        assert Matches(g.labels[walk[0]], w0[splits[0]..splits[1]]);
        assert Matches(g.labels[walk[1]], w0[splits[1]..splits[2]]);
        assert splits[0] == 0 && splits[2] == |w0|;
        assert splits[1] == 0 by {
          assert w0[splits[0]..splits[1]] == "";
        }
        assert w0[splits[1]..splits[2]] == "";
        assert w0 == "";
      }
    }
    assert |walk| >= 3;
    StartOnlyAtFront(g, walk);
    EndOnlyAtBack(g, walk);
    assert walk[1] in g.nodes;
    assert walk[1] != g.start;
    assert walk[1] != g.end;
    assert walk[1] == m;
    assert (g.start, m) in g.edges by {
      assert (walk[0], walk[1]) in g.edges;
      assert walk[0] == g.start;
    }
    assert walk[|walk| - 2] in g.nodes;
    assert walk[|walk| - 2] != g.start;
    assert walk[|walk| - 2] != g.end;
    assert walk[|walk| - 2] == m;
    assert (m, g.end) in g.edges by {
      assert (walk[|walk| - 2], walk[|walk| - 1]) in g.edges;
      assert walk[|walk| - 1] == g.end;
    }
  }

  // Once the graph has a single interior node m with no self-loop, its edges are
  // exactly {(start,m),(m,end)} plus possibly a leftover direct start->end bypass.
  lemma FinalGraphEdgesEnumerated(g: Graph, m: int)
    requires WF(g)
    requires NoBackEdges(g)
    requires InteriorNodes(g) == {m}
    requires (m, m) !in g.edges
    ensures g.edges <= {(g.start, m), (m, g.end), (g.start, g.end)}
  {
    assert g.start in g.nodes && g.end in g.nodes;
    assert g.nodes == InteriorNodes(g) + {g.start, g.end};
    assert g.nodes == {g.start, g.end, m};
    forall e | e in g.edges ensures e in {(g.start, m), (m, g.end), (g.start, g.end)} {
      assert e.0 in g.nodes && e.1 in g.nodes;
      assert e.1 != g.start;
      assert e.0 != g.end;
      if e.0 == m && e.1 == m {
        assert false;
      }
    }
  }

  // Combines FinalNodeHasNeighbors and FinalGraphEdgesEnumerated: once the graph has
  // one self-loop-free interior node m and some sample string is non-empty, and a
  // direct start->end bypass edge is present, m qualifies for optional-contraction
  // (Preds(g,m) and Succs(g,m) are forced to be exactly {g.start} and {g.end}
  // respectively, so the "every parent connects to every child" bypass condition
  // reduces to exactly the presence of that one edge).
  lemma FinalNodeCanMakeOptional(g: Graph, m: int, w0: string)
    requires WF(g)
    requires NoBackEdges(g)
    requires InteriorNodes(g) == {m}
    requires g.labels[g.start] == Eps
    requires g.labels[g.end] == Eps
    requires (m, m) !in g.edges
    requires w0 != ""
    requires GraphAccepts(g, w0)
    requires (g.start, g.end) in g.edges
    ensures CanMakeOptional(g, m)
  {
    FinalNodeHasNeighbors(g, m, w0);
    FinalGraphEdgesEnumerated(g, m);
    assert Preds(g, m) == {g.start} by {
      assert g.start in Preds(g, m);
      forall p | p in Preds(g, m) ensures p == g.start {
        assert (p, m) in g.edges;
      }
    }
    assert Succs(g, m) == {g.end} by {
      assert g.end in Succs(g, m);
      forall c | c in Succs(g, m) ensures c == g.end {
        assert (m, c) in g.edges;
      }
    }
    forall p, c | p in Preds(g, m) && c in Succs(g, m) ensures (p, c) in g.edges {
      assert p == g.start && c == g.end;
    }
  }

  // ==================================================================================
  // Round 7 (continued): the top-level method
  // ==================================================================================
  //
  // Repeatedly applies whichever of FindSimplePathPair/FindMergePair/FindOptionalNode
  // is currently findable, in that priority order; whenever none is found (and 2+
  // interior nodes remain), applies ExecCollapseAll to finish in one step. The
  // termination measure is lexicographic (|InteriorNodes(g)|, |g.edges|): simple-path,
  // merge and CollapseAll all strictly shrink the interior-node count (by exactly one
  // for the first two - InteriorNodesContractSimplePath/InteriorNodesMergeAny - and
  // straight down to exactly one - InteriorNodesCollapseAll - for the third), while
  // optional-contraction leaves the node count unchanged but strictly shrinks the edge
  // count instead (EdgeCountMakeOptional) - so the SECOND component of the measure is
  // what actually justifies termination for that one branch; a decreases clause of
  // |InteriorNodes(g)| alone would not have been enough.
  //
  // Once the loop reduces the graph to a single interior node m, two more, purely
  // structural, issues (neither related to soundness, both flagged in this round's
  // header comment) can still stand between that graph and SingleInteriorNodeAccepts's
  // hypotheses: m might carry a self-loop forward untouched (none of the three easy
  // contractions can ever pick a self-looped node - it's excluded from all three
  // preconditions - so a self-loop only ever gets cleared out by a set-contraction that
  // includes that node; if the very last size-reducing step happened to be a
  // simple-path/merge contraction rather than CollapseAll, m is guaranteed fresh and
  // hence already self-loop-free, but if the FIRST graph already had exactly one
  // interior node with a self-loop - e.g. S = {"aa"} - no contraction ever ran at all),
  // and a direct start->end bypass edge might coexist with m (arising whenever "" is a
  // sample alongside non-empty ones). Both are resolved with at most one extra
  // application each of the already-proven machinery: ExecCollapseAll (self-loop) and
  // ExecMakeOptional (bypass, licensed by FinalNodeCanMakeOptional above).

  // ---- One lemma per loop-body branch, so the loop's own verification condition
  // stays small (bundling all four branches' proofs directly into the loop body is what
  // caused InferViaBigramGraph to time out). Each bundles "preserve the four invariants
  // plus NoBackEdges/sentinels" and "the termination measure actually shrunk the right
  // way" into one call.

  lemma LoopStepSimplePath(oldG: Graph, x: int, y: int, S: set<string>, g: Graph)
    requires WF(oldG)
    requires AllLabelsSore(oldG)
    requires PairwiseDisjointLabels(oldG)
    requires NoBackEdges(oldG)
    requires oldG.labels[oldG.start] == Eps
    requires oldG.labels[oldG.end] == Eps
    requires forall w :: w in S ==> GraphAccepts(oldG, w)
    requires CanContractSimplePath(oldG, x, y)
    requires g == ContractSimplePathGraph(oldG, x, y)
    ensures WF(g)
    ensures AllLabelsSore(g)
    ensures PairwiseDisjointLabels(g)
    ensures NoBackEdges(g)
    ensures g.labels[g.start] == Eps
    ensures g.labels[g.end] == Eps
    ensures forall w :: w in S ==> GraphAccepts(g, w)
    ensures |InteriorNodes(g)| == |InteriorNodes(oldG)| - 1
  {
    ContractSimplePathAllLabelsSore(oldG, x, y);
    ContractSimplePathPairwiseDisjoint(oldG, x, y);
    ContractSimplePathNoBackEdges(oldG, x, y);
    ContractSimplePathSentinels(oldG, x, y);
    InteriorNodesContractSimplePath(oldG, x, y);
    forall w | w in S ensures GraphAccepts(g, w) {
      ContractSimplePathSound(oldG, x, y, w);
    }
  }

  lemma LoopStepMergeAny(oldG: Graph, a: int, b: int, S: set<string>, g: Graph)
    requires WF(oldG)
    requires AllLabelsSore(oldG)
    requires PairwiseDisjointLabels(oldG)
    requires NoBackEdges(oldG)
    requires oldG.labels[oldG.start] == Eps
    requires oldG.labels[oldG.end] == Eps
    requires forall w :: w in S ==> GraphAccepts(oldG, w)
    requires CanMergeAny(oldG, a, b)
    requires g == MergeAnyGraph(oldG, a, b)
    ensures WF(g)
    ensures AllLabelsSore(g)
    ensures PairwiseDisjointLabels(g)
    ensures NoBackEdges(g)
    ensures g.labels[g.start] == Eps
    ensures g.labels[g.end] == Eps
    ensures forall w :: w in S ==> GraphAccepts(g, w)
    ensures |InteriorNodes(g)| == |InteriorNodes(oldG)| - 1
  {
    MergeAnyAllLabelsSore(oldG, a, b);
    MergeAnyPairwiseDisjoint(oldG, a, b);
    MergeAnyNoBackEdges(oldG, a, b);
    MergeAnySentinels(oldG, a, b);
    InteriorNodesMergeAny(oldG, a, b);
    forall w | w in S ensures GraphAccepts(g, w) {
      MergeAnySound(oldG, a, b, w);
    }
  }

  lemma LoopStepMakeOptional(oldG: Graph, v: int, S: set<string>, g: Graph)
    requires WF(oldG)
    requires AllLabelsSore(oldG)
    requires PairwiseDisjointLabels(oldG)
    requires NoBackEdges(oldG)
    requires oldG.labels[oldG.start] == Eps
    requires oldG.labels[oldG.end] == Eps
    requires forall w :: w in S ==> GraphAccepts(oldG, w)
    requires CanMakeOptional(oldG, v)
    requires g == MakeOptionalGraph(oldG, v)
    ensures WF(g)
    ensures AllLabelsSore(g)
    ensures PairwiseDisjointLabels(g)
    ensures NoBackEdges(g)
    ensures g.labels[g.start] == Eps
    ensures g.labels[g.end] == Eps
    ensures forall w :: w in S ==> GraphAccepts(g, w)
    ensures InteriorNodes(g) == InteriorNodes(oldG)
    ensures |g.edges| < |oldG.edges|
  {
    MakeOptionalAllLabelsSore(oldG, v);
    MakeOptionalPairwiseDisjoint(oldG, v);
    MakeOptionalNoBackEdges(oldG, v);
    MakeOptionalSentinels(oldG, v);
    InteriorNodesMakeOptional(oldG, v);
    EdgeCountMakeOptional(oldG, v);
    forall w | w in S ensures GraphAccepts(g, w) {
      MakeOptionalSound(oldG, v, w);
    }
  }

  // ---- The finishing step, factored into its own method (again to keep
  // InferViaBigramGraph's own verification condition small) - see the big comment
  // above InferViaBigramGraph for what it does and why both canonicalization steps are
  // needed. ----

  method {:timeLimitMultiplier 4} FinishSingleInteriorNode(g0: Graph, S: set<string>, w0: string) returns (r: Regex)
    requires WF(g0)
    requires AllLabelsSore(g0)
    requires PairwiseDisjointLabels(g0)
    requires NoBackEdges(g0)
    requires g0.labels[g0.start] == Eps
    requires g0.labels[g0.end] == Eps
    requires forall w :: w in S ==> GraphAccepts(g0, w)
    requires |InteriorNodes(g0)| == 1
    requires w0 in S && w0 != ""
    ensures forall w :: w in S ==> Matches(r, w)
    ensures IsSore(r)
  {
    var g := g0;
    var interior := InteriorNodes(g);
    var m :| m in interior;
    SingletonSetChar(interior, m);
    assert InteriorNodes(g) == {m};

    if (m, m) in g.edges {
      var oldG := g;
      g := ExecCollapseAll(oldG);
      var interior2 := InteriorNodes(g);
      var m2 :| m2 in interior2;
      SingletonSetChar(interior2, m2);
      m := m2;
    }
    assert (m, m) !in g.edges;
    assert InteriorNodes(g) == {m};

    if (g.start, g.end) in g.edges {
      FinalNodeCanMakeOptional(g, m, w0);
      FinalNodeHasNeighbors(g, m, w0);
      FinalGraphEdgesEnumerated(g, m);
      assert g.edges == {(g.start, m), (m, g.end), (g.start, g.end)};
      var oldG := g;
      g := ExecMakeOptional(oldG, m);
      MakeOptionalSentinels(oldG, m);
      var bypass := set p, c | p in Preds(oldG, m) && c in Succs(oldG, m) :: (p, c);
      assert Preds(oldG, m) == {oldG.start} by {
        assert oldG.start in Preds(oldG, m);
        forall p | p in Preds(oldG, m) ensures p == oldG.start {
          assert (p, m) in oldG.edges;
        }
      }
      assert Succs(oldG, m) == {oldG.end} by {
        assert oldG.end in Succs(oldG, m);
        forall c | c in Succs(oldG, m) ensures c == oldG.end {
          assert (m, c) in oldG.edges;
        }
      }
      assert bypass == {(oldG.start, oldG.end)};
      assert g.edges == oldG.edges - bypass;
      assert g.edges == {(g.start, m), (m, g.end)};
      forall w | w in S ensures GraphAccepts(g, w) {
        MakeOptionalSound(oldG, m, w);
      }
    } else {
      FinalNodeHasNeighbors(g, m, w0);
      FinalGraphEdgesEnumerated(g, m);
      assert g.edges == {(g.start, m), (m, g.end)};
    }

    r := g.labels[m];
    forall w | w in S ensures Matches(r, w) {
      SingleInteriorNodeAccepts(g, m, w);
    }
    assert m in g.nodes;
  }

  // ==================================================================================
  // Round 8: real reachability-based SCC detection, tried before the CollapseAll
  // fallback (closes the gap Round 7 explicitly left open: "Real SCC-detection ... to
  // tighten results on cyclic inputs remains deferred future work")
  // ==================================================================================
  //
  // Round 7's driver never looked for a genuine cycle before giving up and collapsing
  // the ENTIRE remaining interior via CollapseAllGraph, so an input whose bigram graph
  // contains a real cycle among SOME (but not all) of its remaining interior nodes got
  // needlessly over-approximated: the whole interior was wildcarded into one
  // Star(a1|...|an) node, even when only a small subset of those nodes actually formed
  // a cycle and the rest of the graph was already a DAG. This round adds a genuine,
  // executable, reachability-based cycle finder (FindNontrivialSCC) and tries it right
  // before the CollapseAll fallback: whenever it finds a nonempty candidate C with
  // |C| >= 2 that is a genuine strongly-connected set (every member of C can both reach
  // and be reached from every other member), the driver now contracts just C via
  // ContractSCCGraph/ExecContractSCC instead of reaching for CollapseAllGraph over the
  // WHOLE remaining interior - letting the loop continue contracting whatever DAG-shaped
  // structure is left around the (now-collapsed) cycle via the ordinary simple-path/
  // merge/optional rules, instead of wildcarding all of it away in one shot.
  //
  // Placement in the driver's priority order: FindNontrivialSCC is tried AFTER
  // FindSimplePathPair/FindMergePair/FindOptionalNode and BEFORE CollapseAllGraph - i.e.
  // it slots in as a second-to-last resort, not a first one. Rationale: the other three
  // are cheap, purely local (single-node or single-pair) checks with no reachability
  // search at all, so they should stay tried first exactly as before; only once NONE of
  // them applies does it make sense to pay for a whole-graph reachability search looking
  // for a cycle - and doing so BEFORE falling back to CollapseAllGraph is strictly
  // better whenever a genuine proper-subset cycle exists (the whole point of this
  // round), while costing nothing extra when no such cycle exists (CollapseAllGraph
  // still fires exactly as before, unchanged). Note some inputs (e.g. S = {"abab"}) have
  // a bigram graph where the only remaining interior nodes ARE exactly the cycle - in
  // that specific case C ends up equal to InteriorNodes(g), so contracting just C
  // produces the IDENTICAL graph CollapseAllGraph would have (same set, same
  // construction, no tightening at all - verified empirically while building this
  // round, see GraphTests.dfy's TestNontrivialSCCTightening's comment for the concrete
  // example actually used to demonstrate a real difference: a cycle that is a PROPER
  // subset of the remaining interior nodes, with other, non-cyclic structure left over
  // to keep contracting afterwards).
  //
  // Self-loops (a single node x with (x,x) in g.edges) are deliberately NOT treated as
  // "nontrivial" by FindNontrivialSCC below, even though a self-loop is itself a
  // (degenerate, one-node) cycle: including it would leave the interior-node count
  // UNCHANGED (contracting a singleton C = {x} still produces one node), so the
  // driver's existing termination measure (|InteriorNodes(g)|, |g.edges|) would need a
  // NEW argument - specifically, a proof that a self-loop contraction strictly shrinks
  // |g.edges| instead (the same shape EdgeCountMakeOptional already proves for
  // optional-contraction) - to justify termination for that branch. Since every
  // self-loop scenario this project's tests actually exercise (S = {"aa"}) already
  // reduces to a SINGLE remaining interior node before the main loop even runs (the
  // loop's own guard is |InteriorNodes(g)| >= 2), that case is already handled
  // separately and unconditionally by FinishSingleInteriorNode's own self-loop
  // canonicalization step (see Round 7's header comment) - so there is no unaddressed
  // gap left for this round to close by also chasing self-loops inside the main loop,
  // and skipping them here avoids an extra termination lemma for no behavioral benefit.
  //
  // The reachability machinery itself: Reachable/ReachableBackward are plain (fully
  // executable) forward/backward reachability fixpoints - grow a `visited` set by
  // following one more step of (respectively) outgoing/incoming edges until nothing new
  // is added, terminating because `g.nodes - visited` strictly shrinks every time the
  // frontier is nonempty (the same "grow a set to a fixpoint over a finite universe"
  // shape used throughout this file, e.g. SetToSeq/SetToSeqExec's own `s - {x}`
  // decreases, just growing instead of shrinking here). A node x's classical SCC is the
  // intersection of everything x can reach and everything that can reach x
  // (SCCCandidate below) - proving this really is closed under mutual reachability (the
  // textbook SCC definition) is NOT attempted, and is not needed: exactly as Round 5/6
  // already established for CanContractSCC/ContractSCCGraph in general, soundness only
  // needs C to be a nonempty subset of interior nodes, nothing about genuine strong
  // connectivity - so SCCCandidateProps below only proves the (much easier) facts
  // CanContractSCC actually requires, following this file's established "propose a
  // candidate heuristically, prove whatever was proposed sound" separation of concerns.
  //
  // ExecContractSCC generalizes ExecCollapseAll (Round 7) from C := InteriorNodes(g) to
  // an arbitrary C satisfying CanContractSCC(g, C): every one of ExecCollapseAll's
  // supporting lemmas (ExecCollapseAllWF/SoreDisjoint/NoBackEdges/Sentinels/SoundOne)
  // turns out to ALREADY be fully generic in C (none of their proofs actually used
  // C == InteriorNodes(g), only CanContractSCC(g, C)) and are reused here verbatim - the
  // only new piece needed is ExecContractSCCInterior, replacing ExecCollapseAllInterior's
  // C-specific "InteriorNodes(g2) == {m}" conclusion with the general
  // "InteriorNodes(g2) == InteriorNodes(g) - C + {m}" (and the matching cardinality
  // fact), proved directly from the executable construction's own node-set formula, with
  // no need to relate it back to the ghost ContractSCCGraph at all.

  // ---- Cardinality of removing an arbitrary subset (generalizes CardRemoveTwo, whose
  // fixed-size-2 removal isn't enough once C can have any size >= 2). ----

  lemma CardRemoveSubset(s: set<int>, t: set<int>)
    requires t <= s
    ensures |s - t| == |s| - |t|
    decreases t
  {
    if t == {} {
    } else {
      var x :| x in t;
      CardRemoveSubset(s - {x}, t - {x});
      assert s - t == (s - {x}) - (t - {x});
      CardRemoveOne(s, x);
    }
  }

  // ---- Forward/backward reachability fixpoints ----

  function Reachable(g: Graph, from: int, visited: set<int>): set<int>
    requires WF(g)
    requires from in g.nodes
    requires visited <= g.nodes
    ensures visited <= Reachable(g, from, visited)
    ensures Reachable(g, from, visited) <= g.nodes
    decreases g.nodes - visited
  {
    var frontier := set n | n in g.nodes && n !in visited && (exists p :: p in visited && (p, n) in g.edges) :: n;
    if frontier == {} then visited
    else
      assert frontier <= g.nodes - visited && frontier != {};
      Reachable(g, from, visited + frontier)
  }

  function ReachableBackward(g: Graph, from: int, visited: set<int>): set<int>
    requires WF(g)
    requires from in g.nodes
    requires visited <= g.nodes
    ensures visited <= ReachableBackward(g, from, visited)
    ensures ReachableBackward(g, from, visited) <= g.nodes
    decreases g.nodes - visited
  {
    var frontier := set n | n in g.nodes && n !in visited && (exists p :: p in visited && (n, p) in g.edges) :: n;
    if frontier == {} then visited
    else
      assert frontier <= g.nodes - visited && frontier != {};
      ReachableBackward(g, from, visited + frontier)
  }

  // ---- A node's classical SCC, restricted to interior nodes (excludes the sentinels,
  // which every node can typically reach/be reached from, so they must be explicitly
  // filtered out before this is ever handed to CanContractSCC/ContractSCCGraph, whose
  // precondition forbids them). ----

  function SCCCandidate(g: Graph, x: int): set<int>
    requires WF(g)
    requires x in g.nodes
  {
    (Reachable(g, x, {x}) * ReachableBackward(g, x, {x})) * InteriorNodes(g)
  }

  lemma SCCCandidateProps(g: Graph, x: int)
    requires WF(g)
    requires x in InteriorNodes(g)
    ensures CanContractSCC(g, SCCCandidate(g, x))
    ensures x in SCCCandidate(g, x)
  {
    assert x in g.nodes;
    assert {x} <= Reachable(g, x, {x});
    assert {x} <= ReachableBackward(g, x, {x});
    assert x in Reachable(g, x, {x}) && x in ReachableBackward(g, x, {x});
    assert x in SCCCandidate(g, x);
    assert SCCCandidate(g, x) <= InteriorNodes(g);
    assert SCCCandidate(g, x) <= g.nodes;
    assert g.start !in InteriorNodes(g) && g.end !in InteriorNodes(g);
  }

  // ---- Executable "contract an arbitrary genuine SCC" builder, generalizing
  // ExecCollapseAll (Round 7) from C := InteriorNodes(g) to any C satisfying
  // CanContractSCC(g, C). ----

  lemma ExecContractSCCInterior(g: Graph, C: set<int>, m: int, cs: seq<int>, g2: Graph)
    requires WF(g)
    requires CanContractSCC(g, C)
    requires m !in g.nodes
    requires forall i :: 0 <= i < |cs| ==> cs[i] in g.nodes
    requires g2 == Graph(CollapseNodes(g, C, m), CollapseLabels(g, C, m, cs), CollapseEdges(g, C, m), g.start, g.end)
    ensures WF(g2)
    ensures InteriorNodes(g2) == InteriorNodes(g) - C + {m}
    ensures |InteriorNodes(g2)| == |InteriorNodes(g)| - |C| + 1
  {
    ExecCollapseAllWF(g, C, m, cs, g2);
    assert g2.nodes == g.nodes - C + {m};
    assert m != g.start && m != g.end;
    assert C <= InteriorNodes(g);
    assert InteriorNodes(g2) == InteriorNodes(g) - C + {m};
    CardRemoveSubset(InteriorNodes(g), C);
    assert m !in InteriorNodes(g) - C;
    CardAddOne(InteriorNodes(g) - C, m);
  }

  method ExecContractSCC(g: Graph, C: set<int>) returns (g2: Graph)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires NoBackEdges(g)
    requires CanContractSCC(g, C)
    ensures WF(g2)
    ensures AllLabelsSore(g2)
    ensures PairwiseDisjointLabels(g2)
    ensures NoBackEdges(g2)
    ensures InteriorNodes(g2) == InteriorNodes(g) - C + {ExecFreshNodeGhostValue(g.nodes)}
    ensures |InteriorNodes(g2)| == |InteriorNodes(g)| - |C| + 1
    ensures g.start in g2.nodes && g.end in g2.nodes
    ensures g2.start == g.start
    ensures g2.end == g.end
    ensures g2.labels[g.start] == g.labels[g.start]
    ensures g2.labels[g.end] == g.labels[g.end]
    ensures forall w :: GraphAccepts(g, w) ==> GraphAccepts(g2, w)
  {
    var cs := SetToSeqExec(C);
    var m := ExecFreshNode(g.nodes);
    ExecFreshNodeIsFreshNode(g.nodes, m);
    ExecFreshNodeGhostValueEq(g.nodes, m);

    g2 := Graph(CollapseNodes(g, C, m), CollapseLabels(g, C, m, cs), CollapseEdges(g, C, m), g.start, g.end);

    ExecCollapseAllSoreDisjoint(g, C, m, cs, g2);
    ExecCollapseAllNoBackEdges(g, C, m, cs, g2);
    ExecContractSCCInterior(g, C, m, cs, g2);
    ExecCollapseAllSentinels(g, C, m, cs, g2);
    forall w | GraphAccepts(g, w) ensures GraphAccepts(g2, w) {
      ExecCollapseAllSoundOne(g, C, m, cs, g2, w);
    }
  }

  // ---- Executable search: the first interior node whose SCCCandidate has size >= 2
  // (a genuine multi-node cycle) - see the big comment above for why single-node
  // self-loops are deliberately not treated as "nontrivial" here. ----

  method FindNontrivialSCC(g: Graph) returns (found: bool, C: set<int>)
    requires WF(g)
    ensures found ==> CanContractSCC(g, C) && |C| >= 2
  {
    found := false;
    C := {};
    var xs := SetToSeqExec(InteriorNodes(g));
    var i := 0;
    while i < |xs| && !found
      invariant 0 <= i <= |xs|
      invariant found ==> CanContractSCC(g, C) && |C| >= 2
    {
      var x := xs[i];
      assert x in InteriorNodes(g);
      var Cx := SCCCandidate(g, x);
      SCCCandidateProps(g, x);
      if |Cx| >= 2 {
        found := true;
        C := Cx;
      }
      i := i + 1;
    }
  }

  // ==================================================================================
  // Round 9: self-loop-to-Plus contraction (fixes the precision bug the driver's own
  // header comment above now documents in full - see that comment for the motivating
  // example, root cause, and the resulting before/after regex).
  // ==================================================================================

  // The !Matches(g.labels[v], "") conjunct is what makes LoopToPlusSound provable in
  // general (see the module header comment): every repetition piece collapsed into the
  // new Plus(labels[v]) step must be non-empty, and this is what guarantees that. It costs
  // nothing on any input this pipeline actually produces - a self-looped node's label is
  // always still its original, never-nullable Sym(c) (every other contraction rule
  // excludes self-looped candidates from its own precondition, so nothing ever gets the
  // chance to relabel one into something nullable before this rule fires).
  predicate CanLoopToPlus(g: Graph, v: int)
    requires WF(g)
  {
    v in g.nodes && v != g.start && v != g.end && (v, v) in g.edges &&
    !Matches(g.labels[v], "")
  }

  ghost function LoopToPlusGraph(g: Graph, v: int): Graph
    requires WF(g)
    requires CanLoopToPlus(g, v)
  {
    Graph(g.nodes, g.labels[v := Plus(g.labels[v])], g.edges - {(v, v)}, g.start, g.end)
  }

  lemma LoopToPlusWF(g: Graph, v: int)
    requires WF(g)
    requires CanLoopToPlus(g, v)
    ensures WF(LoopToPlusGraph(g, v))
  {
    var g' := LoopToPlusGraph(g, v);
    assert g'.start in g'.nodes && g'.end in g'.nodes;
    forall e | e in g'.edges ensures e.0 in g'.nodes && e.1 in g'.nodes {
      assert e in g.edges;
    }
  }

  lemma LoopToPlusAllLabelsSore(g: Graph, v: int)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanLoopToPlus(g, v)
    ensures WF(LoopToPlusGraph(g, v))
    ensures AllLabelsSore(LoopToPlusGraph(g, v))
  {
    LoopToPlusWF(g, v);
    var g' := LoopToPlusGraph(g, v);
    forall n | n in g'.nodes ensures IsSore(g'.labels[n]) {
      if n == v {
        PlusIsSore(g.labels[v]);
      }
    }
  }

  lemma LoopToPlusPairwiseDisjoint(g: Graph, v: int)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanLoopToPlus(g, v)
    ensures WF(LoopToPlusGraph(g, v))
    ensures PairwiseDisjointLabels(LoopToPlusGraph(g, v))
  {
    LoopToPlusWF(g, v);
    var g' := LoopToPlusGraph(g, v);
    forall n1, n2 | n1 in g'.nodes && n2 in g'.nodes && n1 != n2
      ensures forall c :: Symbols(g'.labels[n1])[c] == 0 || Symbols(g'.labels[n2])[c] == 0
    {
      if n1 == v {
        assert Symbols(g'.labels[n1]) == Symbols(g.labels[v]);
      } else if n2 == v {
        assert Symbols(g'.labels[n2]) == Symbols(g.labels[v]);
      }
    }
  }

  lemma LoopToPlusNoBackEdges(g: Graph, v: int)
    requires WF(g)
    requires CanLoopToPlus(g, v)
    requires NoBackEdges(g)
    ensures NoBackEdges(LoopToPlusGraph(g, v))
  {
  }

  lemma LoopToPlusSentinels(g: Graph, v: int)
    requires WF(g)
    requires CanLoopToPlus(g, v)
    ensures WF(LoopToPlusGraph(g, v))
    ensures LoopToPlusGraph(g, v).start == g.start
    ensures LoopToPlusGraph(g, v).end == g.end
    ensures LoopToPlusGraph(g, v).labels[g.start] == g.labels[g.start]
    ensures LoopToPlusGraph(g, v).labels[g.end] == g.labels[g.end]
  {
    LoopToPlusWF(g, v);
  }

  lemma InteriorNodesLoopToPlus(g: Graph, v: int)
    requires WF(g)
    requires CanLoopToPlus(g, v)
    ensures InteriorNodes(LoopToPlusGraph(g, v)) == InteriorNodes(g)
  {
  }

  lemma EdgeCountLoopToPlus(g: Graph, v: int)
    requires WF(g)
    requires CanLoopToPlus(g, v)
    ensures |LoopToPlusGraph(g, v).edges| < |g.edges|
  {
    var g' := LoopToPlusGraph(g, v);
    assert g'.edges == g.edges - {(v, v)};
    CardEdgesRemoveNonempty(g.edges, {(v, v)});
  }

  // ---- Soundness preservation ----
  //
  // The walk-transform reuses the SCC section's SkipCRun/CollapseRuns/CollapseSplits/
  // SkipCSplits/RunIsAllC/SkipCSplitsIsSuffix/CollapseRunsFirstUnchanged/
  // CollapseRunsLastUnchanged/SkipCRunHeadNotInC verbatim, instantiated with C := {v} and
  // m := v (v keeps its own identity - there is no fresh node here, unlike SCC
  // contraction, so no into_m/outof_m redirection is needed either: every edge other than
  // the removed self-loop (v,v) survives unchanged, whichever node it touches).

  // Peels one repetition off (Plus's own existential witness) and hands the rest to the
  // already-proven, already-robust StarOfUnionAccepts, instantiated at the singleton
  // C := {v}, cs := [v] - UnionAllLabels(g, [v]) reduces, by its own one-element-sequence
  // case, to exactly g.labels[v], so Star(UnionAllLabels(g, [v])) IS Star(g.labels[v]),
  // no separate equivalence lemma needed. This reuses StarOfUnionAccepts's own SCC-section
  // proof verbatim instead of re-deriving an analogous induction from scratch - and,
  // crucially for verification robustness (see the module header's note on dafny-verify-
  // clean-but-dafny-test-flaky failures), keeps every per-index fact indexed through
  // `run[i]`/`runSplits[i]` (plain sequence lookups, exactly StarOfUnionAccepts's own
  // trigger shape) rather than hoisting "which node"/"which offset" into a fixed constant
  // or arithmetic offset - an earlier version of this proof hoisted g.labels[v] out of the
  // per-index quantifier (and, separately, tried an arithmetic start-offset instead of
  // re-slicing run/runSplits at each step) and verified cleanly under `dafny verify`, but
  // intermittently failed to re-derive the very same `forall` precondition specifically
  // under `dafny test`/`dafny build` - Dafny reported "could not find a trigger" for
  // exactly those hoisted/arithmetic-indexed quantifiers, unlike the plain `run[i]`/
  // `runSplits[i]` shape used here and throughout the pre-existing SCC section.
  lemma PlusOfRunAccepts(g: Graph, v: int, run: seq<int>, runSplits: seq<nat>, w: string)
    requires WF(g)
    requires v in g.nodes
    requires |run| >= 1
    requires |runSplits| == |run| + 1
    requires runSplits[0] <= |w|
    requires !Matches(g.labels[v], "")
    requires forall i :: 0 <= i < |run| ==> run[i] == v
    requires forall i :: 0 <= i < |run| ==>
               var lo := runSplits[i]; var hi := runSplits[i + 1];
               lo <= hi <= |w| && Matches(g.labels[run[i]], w[lo..hi])
    ensures runSplits[0] <= runSplits[|run|] <= |w|
    ensures Matches(Plus(g.labels[v]), w[runSplits[0]..runSplits[|run|]])
  {
    var k := |run|;
    var restRun := run[1..];
    var restSplits := runSplits[1..];
    forall i | 0 <= i < |restRun| ensures restRun[i] == v {
      assert restRun[i] == run[i + 1];
    }
    forall i | 0 <= i < |restRun|
      ensures var lo := restSplits[i]; var hi := restSplits[i + 1];
              lo <= hi <= |w| && Matches(g.labels[restRun[i]], w[lo..hi])
    {
      assert restRun[i] == run[i + 1];
      assert restSplits[i] == runSplits[i + 1];
      assert restSplits[i + 1] == runSplits[i + 2];
    }
    assert restSplits[0] <= |w| by {
      assert restSplits[0] == runSplits[1];
      assert var lo := runSplits[0]; var hi := runSplits[1]; lo <= hi <= |w|;
    }
    StarOfUnionAccepts(g, {v}, [v], restRun, restSplits, w);
    assert UnionAllLabels(g, [v]) == g.labels[v];
    assert Matches(g.labels[v], w[runSplits[0]..runSplits[1]]) by {
      assert run[0] == v;
      assert var lo := runSplits[0]; var hi := runSplits[1]; lo <= hi <= |w| && Matches(g.labels[run[0]], w[lo..hi]);
    }
    assert restSplits[0] == runSplits[1];
    assert restSplits[k - 1] == runSplits[k];
    assert Matches(Star(g.labels[v]), w[runSplits[1]..runSplits[k]]);
    assert runSplits[0] <= runSplits[1];
    assert runSplits[1] <= runSplits[k];
    assert runSplits[1] - runSplits[0] > 0 by {
      if runSplits[1] - runSplits[0] == 0 {
        assert w[runSplits[0]..runSplits[1]] == "";
      }
    }
    assert Matches(Plus(g.labels[v]), w[runSplits[0]..runSplits[k]]) by {
      assert 0 < runSplits[1] - runSplits[0] <= runSplits[k] - runSplits[0];
      assert w[runSplits[0]..runSplits[k]][..runSplits[1] - runSplits[0]] == w[runSplits[0]..runSplits[1]];
      assert w[runSplits[0]..runSplits[k]][runSplits[1] - runSplits[0]..] == w[runSplits[1]..runSplits[k]];
    }
  }

  lemma LoopStepsPreserves(g: Graph, v: int, g': Graph, walk: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
    requires CanLoopToPlus(g, v)
    requires g' == LoopToPlusGraph(g, v)
    requires ValidSteps(g, walk)
    requires StepsOk(g, walk, splits, w)
    ensures WF(g')
    ensures ValidSteps(g', CollapseRuns(walk, {v}, v))
    ensures StepsOk(g', CollapseRuns(walk, {v}, v), CollapseSplits(walk, splits, {v}, v), w)
    ensures CollapseSplits(walk, splits, {v}, v)[0] == splits[0]
    ensures CollapseSplits(walk, splits, {v}, v)[|CollapseRuns(walk, {v}, v)|] == splits[|walk|]
    decreases |walk|, 1
  {
    if |walk| == 0 {
      // ValidSteps requires |walk| >= 1, so this case is vacuous.
    } else if walk[0] != v {
      LoopStepsPreservesUntouched(g, v, g', walk, splits, w);
    } else {
      LoopStepsPreservesRun(g, v, g', walk, splits, w);
    }
  }

  lemma LoopStepsPreservesUntouched(g: Graph, v: int, g': Graph, walk: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
    requires CanLoopToPlus(g, v)
    requires g' == LoopToPlusGraph(g, v)
    requires ValidSteps(g, walk)
    requires StepsOk(g, walk, splits, w)
    requires |walk| >= 1 && walk[0] != v
    ensures WF(g')
    ensures ValidSteps(g', CollapseRuns(walk, {v}, v))
    ensures StepsOk(g', CollapseRuns(walk, {v}, v), CollapseSplits(walk, splits, {v}, v), w)
    ensures CollapseSplits(walk, splits, {v}, v)[0] == splits[0]
    ensures CollapseSplits(walk, splits, {v}, v)[|CollapseRuns(walk, {v}, v)|] == splits[|walk|]
    decreases |walk|, 0
  {
    LoopToPlusWF(g, v);
    var C := {v};
    var walk' := CollapseRuns(walk, C, v);
    var splits' := CollapseSplits(walk, splits, C, v);
    var restWalk := walk[1..];
    var restSplits := splits[1..];
    if |restWalk| == 0 {
      assert walk' == [walk[0]] + CollapseRuns(restWalk, C, v);
      assert CollapseRuns(restWalk, C, v) == [];
      assert walk' == [walk[0]];
      assert splits' == [splits[0]] + CollapseSplits(restWalk, restSplits, C, v);
      assert CollapseSplits(restWalk, restSplits, C, v) == restSplits;
      assert splits' == [splits[0]] + restSplits;
      assert splits == [splits[0]] + restSplits;
      assert splits' == splits;
      assert ValidSteps(g', walk') by {
        assert walk[0] in g.nodes;
      }
      assert StepsOk(g', walk', splits', w) by {
        assert |walk'| >= 1;
        assert |splits'| == |walk'| + 1;
        forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
        }
        forall i | 0 <= i < |walk'|
          ensures var lo := splits'[i]; var hi := splits'[i + 1];
                  lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
        {
          assert g'.labels[walk[0]] == g.labels[walk[0]];
        }
      }
    } else {
      StepsOkDropFirst(g, walk, splits, w);
      assert ValidSteps(g, restWalk) by {
        forall i | 0 <= i < |restWalk| ensures restWalk[i] in g.nodes {
          assert restWalk[i] == walk[i + 1];
        }
        forall i | 0 <= i < |restWalk| - 1 ensures (restWalk[i], restWalk[i + 1]) in g.edges {
          assert restWalk[i] == walk[i + 1] && restWalk[i + 1] == walk[i + 2];
        }
      }
      LoopStepsPreserves(g, v, g', restWalk, restSplits, w);
      var restWalk' := CollapseRuns(restWalk, C, v);
      var restSplits' := CollapseSplits(restWalk, restSplits, C, v);
      assert walk' == [walk[0]] + restWalk';
      assert splits' == [splits[0]] + restSplits';
      assert ValidSteps(g', walk') by {
        assert walk[0] in g.nodes;
        assert (walk[0], restWalk[0]) in g.edges;
        assert (walk[0], restWalk'[0]) in g'.edges by {
          if restWalk[0] == v {
            assert restWalk'[0] == v;
            assert (walk[0], v) != (v, v);
          } else {
            CollapseRunsFirstUnchanged(restWalk, C, v);
            assert restWalk'[0] == restWalk[0];
            assert (walk[0], restWalk[0]) != (v, v);
          }
        }
      }
      assert StepsOk(g', walk', splits', w) by {
        assert |walk'| >= 1;
        assert |splits'| == |walk'| + 1;
        forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
          if i == 0 {
          } else {
            assert walk'[i] == restWalk'[i - 1];
          }
        }
        forall i | 0 <= i < |walk'|
          ensures var lo := splits'[i]; var hi := splits'[i + 1];
                  lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
        {
          if i == 0 {
            assert g'.labels[walk[0]] == g.labels[walk[0]];
          } else {
            assert walk'[i] == restWalk'[i - 1];
            assert splits'[i] == restSplits'[i - 1];
            assert splits'[i + 1] == restSplits'[i];
          }
        }
      }
    }
  }

  lemma {:timeLimitMultiplier 24} LoopStepsPreservesRun(g: Graph, v: int, g': Graph, walk: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
    requires CanLoopToPlus(g, v)
    requires g' == LoopToPlusGraph(g, v)
    requires ValidSteps(g, walk)
    requires StepsOk(g, walk, splits, w)
    requires |walk| >= 1 && walk[0] == v
    ensures WF(g')
    ensures ValidSteps(g', CollapseRuns(walk, {v}, v))
    ensures StepsOk(g', CollapseRuns(walk, {v}, v), CollapseSplits(walk, splits, {v}, v), w)
    ensures CollapseSplits(walk, splits, {v}, v)[0] == splits[0]
    ensures CollapseSplits(walk, splits, {v}, v)[|CollapseRuns(walk, {v}, v)|] == splits[|walk|]
    decreases |walk|, 0
  {
    LoopToPlusWF(g, v);
    var C := {v};
    var walk' := CollapseRuns(walk, C, v);
    var splits' := CollapseSplits(walk, splits, C, v);
    var afterRun := SkipCRun(walk, C);
    var afterSplits := SkipCSplits(walk, splits, C);
    var k := |walk| - |afterRun|;
    assert k >= 1;
    RunIsAllC(walk, C, k);
    assert afterRun == walk[k..];
    SkipCSplitsIsSuffix(walk, splits, C);
    assert afterSplits == splits[k..];
    var run := walk[..k];
    var runSplits := splits[..k + 1];
    forall i | 0 <= i < k ensures run[i] == v {
      assert run[i] == walk[i];
      assert run[i] in C;
    }
    forall i | 0 <= i < k
      ensures var lo := runSplits[i]; var hi := runSplits[i + 1];
              lo <= hi <= |w| && Matches(g.labels[run[i]], w[lo..hi])
    {
      StepsOkAt(g, walk, splits, w, i);
      assert run[i] == walk[i];
      assert runSplits[i] == splits[i];
      assert runSplits[i + 1] == splits[i + 1];
    }
    assert runSplits[0] == splits[0];
    assert runSplits[k] == splits[k];
    assert runSplits[0] <= |w| by {
      assert 0 <= 0 < k;
      assert var lo := runSplits[0]; var hi := runSplits[1]; lo <= hi <= |w|;
    }
    PlusOfRunAccepts(g, v, run, runSplits, w);
    assert splits[0] <= splits[k] <= |w| by {
      assert runSplits[0] <= runSplits[k] <= |w|;
    }
    assert Matches(Plus(g.labels[v]), w[splits[0]..splits[k]]) by {
      assert w[splits[0]..splits[k]] == w[runSplits[0]..runSplits[k]];
    }
    assert g'.labels[v] == Plus(g.labels[v]);

    if |afterRun| == 0 {
      assert walk' == [v] + CollapseRuns(afterRun, C, v);
      assert CollapseRuns(afterRun, C, v) == [];
      assert walk' == [v];
      assert splits' == [splits[0], splits[k]];
      assert k == |walk|;
      assert ValidSteps(g', walk') by {
        assert v in g'.nodes;
      }
      assert StepsOk(g', walk', splits', w) by {
        forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
        }
        forall i | 0 <= i < |walk'|
          ensures var lo := splits'[i]; var hi := splits'[i + 1];
                  lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
        {
        }
      }
    } else {
      assert ValidSteps(g, afterRun) by {
        forall i | 0 <= i < |afterRun| ensures afterRun[i] in g.nodes {
          assert afterRun[i] == walk[k + i];
        }
        forall i | 0 <= i < |afterRun| - 1 ensures (afterRun[i], afterRun[i + 1]) in g.edges {
          assert afterRun[i] == walk[k + i] && afterRun[i + 1] == walk[k + i + 1];
        }
      }
      assert StepsOk(g, afterRun, afterSplits, w) by {
        forall i | 0 <= i < |afterRun| ensures afterRun[i] in g.nodes {
          assert afterRun[i] == walk[k + i];
        }
        forall i | 0 <= i < |afterRun|
          ensures var lo := afterSplits[i]; var hi := afterSplits[i + 1];
                  lo <= hi <= |w| && Matches(g.labels[afterRun[i]], w[lo..hi])
        {
          StepsOkAt(g, walk, splits, w, k + i);
          assert afterRun[i] == walk[k + i];
          assert afterSplits[i] == splits[k + i];
          assert afterSplits[i + 1] == splits[k + i + 1];
        }
      }
      LoopStepsPreserves(g, v, g', afterRun, afterSplits, w);
      var afterWalk' := CollapseRuns(afterRun, C, v);
      var afterSplits' := CollapseSplits(afterRun, afterSplits, C, v);
      assert walk' == [v] + afterWalk';
      assert splits' == [splits[0], splits[k]] + afterSplits'[1..];
      assert afterSplits'[0] == afterSplits[0] == splits[k];
      assert ValidSteps(g', walk') by {
        assert v in g'.nodes;
        assert (v, afterWalk'[0]) in g'.edges by {
          SkipCRunHeadNotInC(walk, C);
          assert afterRun[0] !in C;
          assert afterRun[0] != v;
          assert run[k - 1] == v;
          assert (v, afterRun[0]) in g.edges by {
            assert (walk[k - 1], walk[k]) in g.edges;
            assert walk[k - 1] == run[k - 1];
            assert walk[k] == afterRun[0];
          }
          assert (v, afterRun[0]) != (v, v);
          CollapseRunsFirstUnchanged(afterRun, C, v);
          assert afterWalk'[0] == afterRun[0];
        }
      }
      assert StepsOk(g', walk', splits', w) by {
        forall i | 0 <= i < |walk'| ensures walk'[i] in g'.nodes {
          if i == 0 {
          } else {
            assert walk'[i] == afterWalk'[i - 1];
          }
        }
        forall i | 0 <= i < |walk'|
          ensures var lo := splits'[i]; var hi := splits'[i + 1];
                  lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
        {
          if i == 0 {
            var lo := splits'[0]; var hi := splits'[1];
            assert lo == splits[0];
            assert hi == splits[k];
            assert lo <= hi <= |w|;
            assert Matches(g'.labels[walk'[0]], w[lo..hi]) by {
              assert walk'[0] == v;
              assert g'.labels[v] == Plus(g.labels[v]);
              assert Matches(Plus(g.labels[v]), w[splits[0]..splits[k]]);
            }
          } else {
            assert walk'[i] == afterWalk'[i - 1];
            assert splits'[i] == afterSplits'[i - 1];
            assert splits'[i + 1] == afterSplits'[i];
            StepsOkAt(g', afterWalk', afterSplits', w, i - 1);
            var lo := splits'[i]; var hi := splits'[i + 1];
            assert lo == afterSplits'[i - 1];
            assert hi == afterSplits'[i];
            assert Matches(g'.labels[walk'[i]], w[lo..hi]) by {
              assert walk'[i] == afterWalk'[i - 1];
              assert Matches(g'.labels[afterWalk'[i - 1]], w[afterSplits'[i - 1]..afterSplits'[i]]);
            }
          }
        }
      }
    }
  }

  lemma LoopToPlusSound(g: Graph, v: int, w: string)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires CanLoopToPlus(g, v)
    requires GraphAccepts(g, w)
    ensures WF(LoopToPlusGraph(g, v))
    ensures GraphAccepts(LoopToPlusGraph(g, v), w)
  {
    var g' := LoopToPlusGraph(g, v);
    LoopToPlusWF(g, v);
    var walk :| IsWalk(g, walk) && WalkMatches(g, walk, w);
    var splits: seq<nat> :| |splits| == |walk| + 1 &&
      splits[0] == 0 && splits[|walk|] == |w| &&
      (forall i :: 0 <= i < |walk| ==>
        var lo := splits[i]; var hi := splits[i + 1];
        lo <= hi <= |w| && Matches(g.labels[walk[i]], w[lo..hi]));
    assert StepsOk(g, walk, splits, w) by {
      forall i | 0 <= i < |walk| ensures walk[i] in g.nodes {
      }
    }
    LoopStepsPreserves(g, v, g', walk, splits, w);
    var walk' := CollapseRuns(walk, {v}, v);
    var splits' := CollapseSplits(walk, splits, {v}, v);
    assert walk[0] == g.start && walk[0] != v;
    assert walk[|walk| - 1] == g.end && walk[|walk| - 1] != v;
    assert walk'[0] == g.start by {
      CollapseRunsFirstUnchanged(walk, {v}, v);
    }
    assert walk'[|walk'| - 1] == g.end by {
      CollapseRunsLastUnchanged(walk, {v}, v);
    }
    assert IsWalk(g', walk');
    assert splits'[0] == 0;
    assert splits'[|walk'|] == |w|;
    assert WalkMatches(g', walk', w) by {
      forall i | 0 <= i < |walk'|
        ensures var lo := splits'[i]; var hi := splits'[i + 1];
                lo <= hi <= |w| && Matches(g'.labels[walk'[i]], w[lo..hi])
      {
      }
    }
  }

  // ---- Executable builder (no fresh node needed, exactly like ExecMakeOptional) ----

  method ExecLoopToPlus(g: Graph, v: int) returns (g2: Graph)
    requires WF(g)
    requires CanLoopToPlus(g, v)
    ensures g2 == LoopToPlusGraph(g, v)
  {
    var labels' := g.labels[v := Plus(g.labels[v])];
    g2 := Graph(g.nodes, labels', g.edges - {(v, v)}, g.start, g.end);
  }

  // ---- Executable search: the first node with a (non-nullable-labeled) self-loop ----

  method FindSelfLoopNode(g: Graph) returns (found: bool, v: int)
    requires WF(g)
    ensures found ==> CanLoopToPlus(g, v)
  {
    found := false;
    v := 0;
    var xs := SetToSeqExec(g.nodes);
    var i := 0;
    while i < |xs| && !found
      invariant 0 <= i <= |xs|
      invariant found ==> CanLoopToPlus(g, v)
    {
      if xs[i] != g.start && xs[i] != g.end && (xs[i], xs[i]) in g.edges && !Matches(g.labels[xs[i]], "") {
        found := true;
        v := xs[i];
      }
      i := i + 1;
    }
  }

  // ---- Loop-body lemma, matching LoopStepSimplePath/…MergeAny/…MakeOptional's shape ----

  lemma LoopStepLoopToPlus(oldG: Graph, v: int, S: set<string>, g: Graph)
    requires WF(oldG)
    requires AllLabelsSore(oldG)
    requires PairwiseDisjointLabels(oldG)
    requires NoBackEdges(oldG)
    requires oldG.labels[oldG.start] == Eps
    requires oldG.labels[oldG.end] == Eps
    requires forall w :: w in S ==> GraphAccepts(oldG, w)
    requires CanLoopToPlus(oldG, v)
    requires g == LoopToPlusGraph(oldG, v)
    ensures WF(g)
    ensures AllLabelsSore(g)
    ensures PairwiseDisjointLabels(g)
    ensures NoBackEdges(g)
    ensures g.labels[g.start] == Eps
    ensures g.labels[g.end] == Eps
    ensures forall w :: w in S ==> GraphAccepts(g, w)
    ensures InteriorNodes(g) == InteriorNodes(oldG)
    ensures |g.edges| < |oldG.edges|
  {
    LoopToPlusAllLabelsSore(oldG, v);
    LoopToPlusPairwiseDisjoint(oldG, v);
    LoopToPlusNoBackEdges(oldG, v);
    LoopToPlusSentinels(oldG, v);
    InteriorNodesLoopToPlus(oldG, v);
    EdgeCountLoopToPlus(oldG, v);
    forall w | w in S ensures GraphAccepts(g, w) {
      LoopToPlusSound(oldG, v, w);
    }
  }

  // ==================================================================================
  // Round 11: topological chain-wrap (algorithm step 6), replacing CollapseAllGraph as
  // the near-final step - see this file's header comment for the full motivating gap
  // and fix (S = {"B", "C", "BC"} wrongly produced [BC]* before this round).
  // ==================================================================================

  // ---- A ghost seq-view of InteriorNodes(g), used only to state TopoSort's
  // multiset-permutation postcondition (order-independent, so the ghost SetToSeq's
  // unpredictable `:|`-chosen enumeration order is fine here). ----
  ghost function InteriorNodesSeq(g: Graph): seq<int>
    requires WF(g)
  {
    SetToSeq(InteriorNodes(g))
  }

  // ---- Small reusable fact: two duplicate-free sequences with the same set of
  // elements have the same multiset (every element occurs with multiplicity exactly 0
  // or 1 in each, and membership determines which). ----

  lemma DistinctSeqMultisetCount(s: seq<int>, x: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    ensures multiset(s)[x] == (if x in s then 1 else 0)
    decreases s
  {
    if s == [] {
    } else {
      DistinctSeqMultisetCount(s[1..], x);
      assert s == [s[0]] + s[1..];
      assert multiset(s) == multiset{s[0]} + multiset(s[1..]);
      if x == s[0] {
        assert x !in s[1..] by {
          if x in s[1..] {
            var k :| 0 <= k < |s[1..]| && s[1..][k] == x;
            assert s[k + 1] == x;
          }
        }
      }
    }
  }

  lemma DistinctSameSetSameMultiset(s1: seq<int>, s2: seq<int>)
    requires forall i, j :: 0 <= i < j < |s1| ==> s1[i] != s1[j]
    requires forall i, j :: 0 <= i < j < |s2| ==> s2[i] != s2[j]
    requires forall x :: x in s1 <==> x in s2
    ensures multiset(s1) == multiset(s2)
  {
    forall x ensures multiset(s1)[x] == multiset(s2)[x] {
      DistinctSeqMultisetCount(s1, x);
      DistinctSeqMultisetCount(s2, x);
    }
  }

  // ---- Executable, certifying topological sort (Kahn's algorithm) over
  // InteriorNodes(g): repeatedly pick an as-yet-unplaced interior node with no
  // remaining in-edges from other unplaced interior nodes; if at some point no such
  // node exists while some remain, the interior graph has a genuine cycle and
  // `found` comes back false. The key loop invariant (NoEdgeFromRemainingIntoPlaced,
  // inlined below rather than named) is: no node still in `remaining` has an edge into
  // any node already placed in `order` - true initially (order is empty) and preserved
  // at each step precisely because a candidate is only ever placed once EVERY node
  // still in `remaining` (at that moment, including the candidate itself) has no edge
  // into it. That same "zero in-degree relative to remaining" check, applied to the
  // candidate itself, also directly rules out a self-loop on it - so self-loop-freedom
  // of `order` falls out for free, with no separate case needed. ----
  method TopoSort(g: Graph) returns (found: bool, order: seq<int>)
    requires WF(g)
    ensures found ==> multiset(order) == multiset(InteriorNodesSeq(g))
    ensures found ==> forall i :: 0 <= i < |order| ==> order[i] in InteriorNodes(g)
    ensures found ==> forall i, j :: 0 <= i < j < |order| ==> order[i] != order[j]
    ensures found ==> forall i, j :: 0 <= i < j < |order| ==> (order[j], order[i]) !in g.edges
    ensures found ==> forall i :: 0 <= i < |order| ==> (order[i], order[i]) !in g.edges
  {
    order := [];
    var remaining := InteriorNodes(g);
    found := true;

    while remaining != {}
      invariant remaining <= InteriorNodes(g)
      invariant forall i :: 0 <= i < |order| ==> order[i] in InteriorNodes(g) && order[i] !in remaining
      invariant forall x :: x in InteriorNodes(g) && x !in remaining ==> x in order
      invariant forall i, j :: 0 <= i < j < |order| ==> order[i] != order[j]
      invariant forall p, x :: p in remaining && x in order ==> (p, x) !in g.edges
      invariant forall i, j :: 0 <= i < j < |order| ==> (order[j], order[i]) !in g.edges
      invariant forall i :: 0 <= i < |order| ==> (order[i], order[i]) !in g.edges
      decreases remaining
    {
      var remSeq := SetToSeqExec(remaining);

      var k := 0;
      var picked := false;
      var x0 := 0;
      while k < |remSeq| && !picked
        invariant 0 <= k <= |remSeq|
        invariant picked ==> x0 in remaining && (forall q :: q in remaining ==> (q, x0) !in g.edges)
      {
        var c := remSeq[k];
        var l := 0;
        var ok := true;
        while l < |remSeq| && ok
          invariant 0 <= l <= |remSeq|
          invariant ok ==> forall t :: 0 <= t < l ==> (remSeq[t], c) !in g.edges
        {
          if (remSeq[l], c) in g.edges {
            ok := false;
          }
          l := l + 1;
        }
        if ok {
          assert forall q :: q in remaining ==> (q, c) !in g.edges by {
            forall q | q in remaining ensures (q, c) !in g.edges {
              var t :| 0 <= t < |remSeq| && remSeq[t] == q;
            }
          }
          picked := true;
          x0 := c;
        }
        k := k + 1;
      }

      if !picked {
        found := false;
        return;
      }

      var oldOrder := order;
      var oldRemaining := remaining;
      order := order + [x0];
      remaining := remaining - {x0};

      forall i | 0 <= i < |order| ensures order[i] in InteriorNodes(g) && order[i] !in remaining {
        if i < |oldOrder| {
        } else {
        }
      }
      forall x | x in InteriorNodes(g) && x !in remaining ensures x in order {
        if x == x0 || x !in oldRemaining {
        } else {
        }
      }
      forall i, j | 0 <= i < j < |order| ensures order[i] != order[j] {
        if j < |oldOrder| {
        } else {
          // j == |oldOrder|, order[j] == x0; order[i] == oldOrder[i] != x0 since x0 was
          // in oldRemaining and oldOrder's elements are all !in oldRemaining.
        }
      }
      forall p, x | p in remaining && x in order ensures (p, x) !in g.edges {
        if x in oldOrder {
        } else {
          // x == x0; p in remaining <= oldRemaining, and the pick-loop established
          // (q, x0) !in g.edges for every q in oldRemaining.
        }
      }
      forall i, j | 0 <= i < j < |order| ensures (order[j], order[i]) !in g.edges {
        if j < |oldOrder| {
        } else {
          // j == |oldOrder|, order[j] == x0, order[i] == oldOrder[i] in oldOrder; the
          // "NoEdgeFromRemainingIntoPlaced" invariant (with p := x0 in oldRemaining,
          // x := oldOrder[i] in oldOrder) gives (x0, oldOrder[i]) !in g.edges directly.
        }
      }
      forall i | 0 <= i < |order| ensures (order[i], order[i]) !in g.edges {
        if i < |oldOrder| {
        } else {
          // i == |oldOrder|, order[i] == x0; the pick-loop's own criterion, instantiated
          // at q := x0 (x0 in oldRemaining), gives (x0, x0) !in g.edges.
        }
      }
    }

    assert forall x :: x in InteriorNodesSeq(g) <==> x in InteriorNodes(g);
    DistinctSameSetSameMultiset(order, InteriorNodesSeq(g));
  }

  // ---- Chain-wrap construction: Concat(Opt(labels[order[0]]), Concat(Opt(labels[order[1]]), ... Eps)) ----

  function ChainWrapRegex(g: Graph, order: seq<int>): Regex
    requires WF(g)
    requires forall i :: 0 <= i < |order| ==> order[i] in g.nodes
    decreases order
  {
    if order == [] then Eps
    else Concat(Opt(g.labels[order[0]]), ChainWrapRegex(g, order[1..]))
  }

  // ---- Soreness: mirrors UnionAllLabelsSymbolsMem/UnionAllLabelsIsSore's shape exactly,
  // just folding via Concat/Opt down a chain instead of Union down a set. ----

  lemma ChainWrapSymbolsMem(g: Graph, order: seq<int>, ch: char)
    requires WF(g)
    requires forall i :: 0 <= i < |order| ==> order[i] in g.nodes
    ensures ch in Symbols(ChainWrapRegex(g, order)) <==>
              (exists i :: 0 <= i < |order| && ch in Symbols(g.labels[order[i]]))
    decreases order
  {
    if order == [] {
    } else {
      ChainWrapSymbolsMem(g, order[1..], ch);
      forall i | 0 <= i < |order[1..]| && ch in Symbols(g.labels[order[1..][i]])
        ensures exists j :: 0 <= j < |order| && ch in Symbols(g.labels[order[j]])
      {
        assert order[1..][i] == order[i + 1];
      }
    }
  }

  lemma ChainWrapAllLabelsSore(g: Graph, order: seq<int>)
    requires WF(g)
    requires AllLabelsSore(g)
    requires PairwiseDisjointLabels(g)
    requires forall i :: 0 <= i < |order| ==> order[i] in g.nodes
    requires forall i, j :: 0 <= i < j < |order| ==> order[i] != order[j]
    ensures IsSore(ChainWrapRegex(g, order))
    decreases order
  {
    if order == [] {
      EpsIsSore();
    } else {
      var rest := order[1..];
      forall i, j | 0 <= i < j < |rest| ensures rest[i] != rest[j] {
        assert order[i + 1] == rest[i] && order[j + 1] == rest[j];
      }
      ChainWrapAllLabelsSore(g, rest);
      OptIsSore(g.labels[order[0]]);
      forall c ensures Symbols(Opt(g.labels[order[0]]))[c] == 0 || Symbols(ChainWrapRegex(g, rest))[c] == 0 {
        if Symbols(g.labels[order[0]])[c] > 0 && Symbols(ChainWrapRegex(g, rest))[c] > 0 {
          ChainWrapSymbolsMem(g, rest, c);
          var idx :| 0 <= idx < |rest| && c in Symbols(g.labels[rest[idx]]);
          assert rest[idx] != order[0] by {
            assert order[idx + 1] == rest[idx];
          }
          assert Symbols(g.labels[order[0]])[c] == 0 || Symbols(g.labels[rest[idx]])[c] == 0;
          assert false;
        }
      }
      SymbolsDisjointIsSore(Opt(g.labels[order[0]]), ChainWrapRegex(g, rest));
    }
  }

  // ---- Soundness: every interior node has a slot somewhere in `order` (order is a
  // full permutation of InteriorNodes(g), by TopoSort's multiset postcondition). ----

  lemma OrderContainsAllInterior(g: Graph, order: seq<int>)
    requires WF(g)
    requires multiset(order) == multiset(InteriorNodesSeq(g))
    ensures forall x :: x in InteriorNodes(g) ==> x in order
  {
    forall x | x in InteriorNodes(g) ensures x in order {
      assert x in InteriorNodesSeq(g);
      assert x in multiset(InteriorNodesSeq(g));
      assert x in multiset(order);
    }
  }

  // ---- The key graph fact licensing the whole chain-wrap induction: order[0] (the
  // topologically-first remaining node) can only ever occur at position 0 of a
  // node-sequence drawn from `order`'s membership and following real edges - never
  // later. (Any later occurrence would need a real edge into it from the previous,
  // also-order-drawn, position; the no-back-edge/no-self-loop properties rule out
  // every possible source of that edge.) ----

  lemma ChainWrapOrderHeadOnlyAtFront(g: Graph, order: seq<int>, walkNodes: seq<int>)
    requires WF(g)
    requires order != []
    requires forall i, j :: 0 <= i < j < |order| ==> order[i] != order[j]
    requires forall i, j :: 0 <= i < j < |order| ==> (order[j], order[i]) !in g.edges
    requires forall i :: 0 <= i < |order| ==> (order[i], order[i]) !in g.edges
    requires forall i :: 0 <= i < |walkNodes| ==> walkNodes[i] in order
    requires forall i :: 0 <= i < |walkNodes| - 1 ==> (walkNodes[i], walkNodes[i + 1]) in g.edges
    ensures forall k :: 1 <= k < |walkNodes| ==> walkNodes[k] != order[0]
  {
    forall k | 1 <= k < |walkNodes| ensures walkNodes[k] != order[0] {
      if walkNodes[k] == order[0] {
        assert (walkNodes[k - 1], walkNodes[k]) in g.edges;
        assert walkNodes[k - 1] in order;
        var j :| 0 <= j < |order| && order[j] == walkNodes[k - 1];
        if j == 0 {
          assert walkNodes[k - 1] == order[0] == walkNodes[k];
          assert (order[0], order[0]) in g.edges;
          assert false;
        } else {
          assert (order[j], order[0]) !in g.edges;
          assert false;
        }
      }
    }
  }

  // ---- Small helper: adjacent-pairwise-monotone implies fully monotone (needed since
  // ChainWrapAux's splits are only known adjacent-monotone from the per-index Matches
  // requires, but a recursive call needs the ENDPOINTS of a shifted sub-range compared
  // directly). ----

  lemma SplitsChainMonotone(splits: seq<nat>, i: nat, j: nat)
    requires forall k :: 0 <= k < |splits| - 1 ==> splits[k] <= splits[k + 1]
    requires 0 <= i <= j < |splits|
    ensures splits[i] <= splits[j]
    decreases j - i
  {
    if i < j {
      SplitsChainMonotone(splits, i + 1, j);
    }
  }

  // ---- The main induction: walkNodes (a node-sequence drawn from `order`'s
  // membership, following real edges) matches w[splits[0]..splits[|walkNodes|]] against
  // ChainWrapRegex(g, order) - by peeling order's head at each step and deciding,
  // for the CURRENT walkNodes, whether it starts with that head (consume: match it
  // against the corresponding piece of w) or not (skip: it can only appear later, by
  // ChainWrapOrderHeadOnlyAtFront, so contribute "" via Opt and recurse unchanged). ----

  lemma {:timeLimitMultiplier 4} ChainWrapAux(g: Graph, order: seq<int>, walkNodes: seq<int>, splits: seq<nat>, w: string)
    requires WF(g)
    requires forall i :: 0 <= i < |order| ==> order[i] in InteriorNodes(g)
    requires forall i :: 0 <= i < |order| ==> order[i] in g.nodes
    requires forall i, j :: 0 <= i < j < |order| ==> order[i] != order[j]
    requires forall i, j :: 0 <= i < j < |order| ==> (order[j], order[i]) !in g.edges
    requires forall i :: 0 <= i < |order| ==> (order[i], order[i]) !in g.edges
    requires forall i :: 0 <= i < |walkNodes| ==> walkNodes[i] in order
    requires forall i :: 0 <= i < |walkNodes| ==> walkNodes[i] in g.nodes
    requires forall i :: 0 <= i < |walkNodes| - 1 ==> (walkNodes[i], walkNodes[i + 1]) in g.edges
    requires |splits| == |walkNodes| + 1
    requires splits[0] <= splits[|walkNodes|] <= |w|
    requires forall i :: 0 <= i < |walkNodes| ==>
               var lo := splits[i]; var hi := splits[i + 1];
               lo <= hi <= |w| && Matches(g.labels[walkNodes[i]], w[lo..hi])
    ensures Matches(ChainWrapRegex(g, order), w[splits[0]..splits[|walkNodes|]])
    decreases order
  {
    if order == [] {
      assert walkNodes == [] by {
        if walkNodes != [] {
          assert walkNodes[0] in order;
        }
      }
      assert w[splits[0]..splits[|walkNodes|]] == "";
    } else if walkNodes == [] || walkNodes[0] != order[0] {
      // skip order[0]: it contributes "" to its own Opt slot.
      if walkNodes != [] {
        ChainWrapOrderHeadOnlyAtFront(g, order, walkNodes);
      }
      var order' := order[1..];
      forall i | 0 <= i < |walkNodes| ensures walkNodes[i] in order' {
        assert walkNodes[i] in order;
        assert walkNodes[i] != order[0];
        var idx :| 0 <= idx < |order| && order[idx] == walkNodes[i];
        assert idx != 0;
        assert order'[idx - 1] == walkNodes[i];
      }
      forall i, j | 0 <= i < j < |order'| ensures order'[i] != order'[j] {
        assert order[i + 1] == order'[i] && order[j + 1] == order'[j];
      }
      forall i, j | 0 <= i < j < |order'| ensures (order'[j], order'[i]) !in g.edges {
        assert order[i + 1] == order'[i] && order[j + 1] == order'[j];
      }
      forall i | 0 <= i < |order'| ensures (order'[i], order'[i]) !in g.edges {
        assert order[i + 1] == order'[i];
      }
      forall i | 0 <= i < |order'| ensures order'[i] in InteriorNodes(g) {
        assert order[i + 1] == order'[i];
      }
      forall i | 0 <= i < |order'| ensures order'[i] in g.nodes {
        assert order[i + 1] == order'[i];
      }
      ChainWrapAux(g, order', walkNodes, splits, w);
      OptSoundEps(g.labels[order[0]]);
      var lo := splits[0]; var hi := splits[|walkNodes|];
      assert w[lo..hi][..0] == "";
      assert w[lo..hi][0..] == w[lo..hi];
      assert Matches(ChainWrapRegex(g, order), w[lo..hi]) by {
        assert ChainWrapRegex(g, order) == Concat(Opt(g.labels[order[0]]), ChainWrapRegex(g, order'));
      }
    } else {
      // consume: walkNodes != [] && walkNodes[0] == order[0].
      var lo0 := splits[0]; var hi1 := splits[1];
      assert lo0 <= hi1 <= |w|;
      assert Matches(g.labels[order[0]], w[lo0..hi1]);
      OptSound(g.labels[order[0]], w[lo0..hi1]);

      ChainWrapOrderHeadOnlyAtFront(g, order, walkNodes);
      var walkNodes' := walkNodes[1..];
      var order' := order[1..];
      var splits' := splits[1..];

      forall i | 0 <= i < |walkNodes'| ensures walkNodes'[i] in order' {
        assert walkNodes'[i] == walkNodes[i + 1];
        assert walkNodes[i + 1] in order;
        assert walkNodes[i + 1] != order[0];
        var idx :| 0 <= idx < |order| && order[idx] == walkNodes[i + 1];
        assert idx != 0;
        assert order'[idx - 1] == walkNodes[i + 1];
      }
      forall i | 0 <= i < |walkNodes'| - 1 ensures (walkNodes'[i], walkNodes'[i + 1]) in g.edges {
        assert walkNodes'[i] == walkNodes[i + 1] && walkNodes'[i + 1] == walkNodes[i + 2];
      }
      forall i, j | 0 <= i < j < |order'| ensures order'[i] != order'[j] {
        assert order[i + 1] == order'[i] && order[j + 1] == order'[j];
      }
      forall i, j | 0 <= i < j < |order'| ensures (order'[j], order'[i]) !in g.edges {
        assert order[i + 1] == order'[i] && order[j + 1] == order'[j];
      }
      forall i | 0 <= i < |order'| ensures (order'[i], order'[i]) !in g.edges {
        assert order[i + 1] == order'[i];
      }
      forall i | 0 <= i < |order'| ensures order'[i] in InteriorNodes(g) {
        assert order[i + 1] == order'[i];
      }
      forall i | 0 <= i < |order'| ensures order'[i] in g.nodes {
        assert order[i + 1] == order'[i];
      }
      forall i | 0 <= i < |walkNodes'| ensures walkNodes'[i] in g.nodes {
        assert walkNodes'[i] == walkNodes[i + 1];
      }
      assert |walkNodes'| == |walkNodes| - 1;
      assert |splits'| == |walkNodes'| + 1;
      assert splits'[0] == splits[1];
      assert splits'[|walkNodes'|] == splits[|walkNodes|];
      assert forall k :: 0 <= k < |splits| - 1 ==> splits[k] <= splits[k + 1] by {
        forall k | 0 <= k < |splits| - 1 ensures splits[k] <= splits[k + 1] {
          assert k < |walkNodes|;
          var lo := splits[k]; var hi := splits[k + 1];
          assert lo <= hi <= |w|;
        }
      }
      SplitsChainMonotone(splits, 1, |walkNodes|);
      assert splits'[0] <= splits'[|walkNodes'|] <= |w|;
      forall i | 0 <= i < |walkNodes'|
        ensures var lo := splits'[i]; var hi := splits'[i + 1]; lo <= hi <= |w| && Matches(g.labels[walkNodes'[i]], w[lo..hi])
      {
        assert splits'[i] == splits[i + 1] && splits'[i + 1] == splits[i + 2];
        assert walkNodes'[i] == walkNodes[i + 1];
      }

      ChainWrapAux(g, order', walkNodes', splits', w);

      var lo := splits[0]; var hi := splits[|walkNodes|]; var mid := hi1;
      assert splits'[0] == mid && splits'[|walkNodes'|] == hi;
      assert lo <= mid <= hi <= |w|;
      assert w[lo..hi][..mid - lo] == w[lo..mid];
      assert w[lo..hi][mid - lo..] == w[mid..hi];
      assert Matches(Opt(g.labels[order[0]]), w[lo..mid]);
      assert Matches(ChainWrapRegex(g, order'), w[mid..hi]);
      assert Matches(ChainWrapRegex(g, order), w[lo..hi]) by {
        assert ChainWrapRegex(g, order) == Concat(Opt(g.labels[order[0]]), ChainWrapRegex(g, order'));
      }
    }
  }

  // Factored into its own small lemma rather than an inline `:|` (matching this file's
  // documented verification-robustness note above ContractStepsPreserves: isolating a
  // `:|` extraction into its own dedicated, small proof obligation has proven more
  // robust across `dafny verify` vs. `dafny build`/`dafny test` invocation modes than
  // relying on an ambient WalkMatches-shaped hypothesis to auto-unfold at a call site
  // buried inside a much larger surrounding proof).
  lemma ExtractWalkSplits(g: Graph, walk: seq<int>, w: string) returns (splits: seq<nat>)
    requires WF(g)
    requires IsWalk(g, walk)
    requires WalkMatches(g, walk, w)
    ensures |splits| == |walk| + 1
    ensures splits[0] == 0
    ensures splits[|walk|] == |w|
    ensures forall i :: 0 <= i < |walk| ==>
              var lo := splits[i]; var hi := splits[i + 1];
              lo <= hi <= |w| && Matches(g.labels[walk[i]], w[lo..hi])
  {
    assert exists sp: seq<nat> ::
      |sp| == |walk| + 1 &&
      sp[0] == 0 && sp[|walk|] == |w| &&
      (forall i :: 0 <= i < |walk| ==>
        var lo := sp[i]; var hi := sp[i + 1];
        lo <= hi <= |w| && Matches(g.labels[walk[i]], w[lo..hi]));
    splits :| |splits| == |walk| + 1 &&
      splits[0] == 0 && splits[|walk|] == |w| &&
      (forall i :: 0 <= i < |walk| ==>
        var lo := splits[i]; var hi := splits[i + 1];
        lo <= hi <= |w| && Matches(g.labels[walk[i]], w[lo..hi]));
  }

  // ---- The top-level soundness theorem: any accepted string is matched by the
  // chain-wrap of a valid topological order. Extracts the witness walk, strips its
  // start/end sentinels (forced by NoBackEdges to sit only at the very front/back -
  // StartOnlyAtFront/EndOnlyAtBack, already proven for Round 7), and hands the
  // resulting interior-node subsequence to ChainWrapAux. ----

  lemma ChainWrapSound(g: Graph, order: seq<int>, w: string)
    requires WF(g)
    requires NoBackEdges(g)
    requires g.labels[g.start] == Eps
    requires g.labels[g.end] == Eps
    requires forall i :: 0 <= i < |order| ==> order[i] in InteriorNodes(g)
    requires forall i, j :: 0 <= i < j < |order| ==> order[i] != order[j]
    requires multiset(order) == multiset(InteriorNodesSeq(g))
    requires forall i, j :: 0 <= i < j < |order| ==> (order[j], order[i]) !in g.edges
    requires forall i :: 0 <= i < |order| ==> (order[i], order[i]) !in g.edges
    requires GraphAccepts(g, w)
    ensures Matches(ChainWrapRegex(g, order), w)
  {
    OrderContainsAllInterior(g, order);
    assert forall i :: 0 <= i < |order| ==> order[i] in g.nodes;

    var walk :| IsWalk(g, walk) && WalkMatches(g, walk, w);
    var splits := ExtractWalkSplits(g, walk, w);

    StartOnlyAtFront(g, walk);
    EndOnlyAtBack(g, walk);
    assert |walk| >= 2;

    var walkNodes := walk[1..|walk| - 1];
    var wsplits := splits[1..|walk|];

    forall i | 0 <= i < |walkNodes| ensures walkNodes[i] in InteriorNodes(g) {
      assert walkNodes[i] == walk[i + 1];
      assert walk[i + 1] in g.nodes;
      assert walk[i + 1] != g.start;
      assert walk[i + 1] != g.end;
    }
    forall i | 0 <= i < |walkNodes| ensures walkNodes[i] in order {
      assert walkNodes[i] in InteriorNodes(g);
    }
    forall i | 0 <= i < |walkNodes| ensures walkNodes[i] in g.nodes {
      assert walkNodes[i] in InteriorNodes(g);
    }
    forall i | 0 <= i < |walkNodes| - 1 ensures (walkNodes[i], walkNodes[i + 1]) in g.edges {
      assert walkNodes[i] == walk[i + 1] && walkNodes[i + 1] == walk[i + 2];
      assert (walk[i + 1], walk[i + 2]) in g.edges;
    }

    assert |wsplits| == |walkNodes| + 1;
    forall i | 0 <= i < |walkNodes|
      ensures var lo := wsplits[i]; var hi := wsplits[i + 1]; lo <= hi <= |w| && Matches(g.labels[walkNodes[i]], w[lo..hi])
    {
      assert wsplits[i] == splits[i + 1] && wsplits[i + 1] == splits[i + 2];
      assert walkNodes[i] == walk[i + 1];
    }

    // wsplits[0] (== splits[1]) is forced to 0: labels[walk[0]] == labels[g.start] == Eps
    // only matches "", pinning splits[1] == splits[0] == 0.
    assert wsplits[0] == 0 by {
      assert walk[0] == g.start;
      var lo := splits[0]; var hi := splits[1];
      assert Matches(g.labels[walk[0]], w[lo..hi]);
      assert g.labels[walk[0]] == Eps;
      assert w[lo..hi] == "";
      assert lo == 0;
      assert hi == 0;
    }
    // wsplits[|walkNodes|] (== splits[|walk|-1]) is forced to |w|: symmetric, via
    // labels[walk[|walk|-1]] == labels[g.end] == Eps.
    assert wsplits[|walkNodes|] == |w| by {
      assert walk[|walk| - 1] == g.end;
      var lo := splits[|walk| - 1]; var hi := splits[|walk|];
      assert Matches(g.labels[walk[|walk| - 1]], w[lo..hi]);
      assert g.labels[walk[|walk| - 1]] == Eps;
      assert w[lo..hi] == "";
      assert hi == |w|;
      assert lo == |w|;
    }

    ChainWrapAux(g, order, walkNodes, wsplits, w);
    assert w[wsplits[0]..wsplits[|walkNodes|]] == w;
  }

  method InferViaBigramGraph(S: set<string>) returns (r: Regex)
    ensures forall w :: w in S ==> Matches(r, w)
    ensures IsSore(r)
  {
    var g := BuildBigramGraph(S);

    if InteriorNodes(g) == {} {
      r := Eps;
      EpsIsSore();
      forall w | w in S ensures Matches(r, w) {
      }
      return;
    }

    var w0 :| w0 in S && w0 != "";

    while |InteriorNodes(g)| >= 2
      invariant WF(g)
      invariant AllLabelsSore(g)
      invariant PairwiseDisjointLabels(g)
      invariant NoBackEdges(g)
      invariant g.labels[g.start] == Eps
      invariant g.labels[g.end] == Eps
      invariant forall w :: w in S ==> GraphAccepts(g, w)
      invariant |InteriorNodes(g)| >= 1
      decreases |InteriorNodes(g)|, |g.edges|
    {
      var foundSP, x, y := FindSimplePathPair(g);
      if foundSP {
        var oldG := g;
        g := ExecContractSimplePath(oldG, x, y);
        LoopStepSimplePath(oldG, x, y, S, g);
      } else {
        var foundLoop, vLoop := FindSelfLoopNode(g);
        if foundLoop {
          var oldG := g;
          g := ExecLoopToPlus(oldG, vLoop);
          LoopStepLoopToPlus(oldG, vLoop, S, g);
        } else {
          var foundExact, aExact, bExact := FindExactMergePair(g);
          if foundExact {
            var oldG := g;
            g := ExecMergeAny(oldG, aExact, bExact);
            LoopStepMergeAny(oldG, aExact, bExact, S, g);
          } else {
            var foundOpt, v := FindOptionalNode(g);
            if foundOpt {
              var oldG := g;
              g := ExecMakeOptional(oldG, v);
              LoopStepMakeOptional(oldG, v, S, g);
            } else {
              var foundSCC, C := FindNontrivialSCC(g);
              if foundSCC {
                var oldG := g;
                assert CanContractSCC(oldG, C) && |C| >= 2;
                assert C <= InteriorNodes(oldG);
                g := ExecContractSCC(oldG, C);
                assert |InteriorNodes(g)| == |InteriorNodes(oldG)| - |C| + 1;
                assert |InteriorNodes(g)| < |InteriorNodes(oldG)|;
              } else {
                var foundTopo, order := TopoSort(g);
                if foundTopo {
                  // The remaining graph is acyclic (every rule that could find a cycle -
                  // self-loop-to-Plus, nontrivial-SCC - has already failed this pass), so
                  // wrapping every remaining node in Opt and concatenating in topological
                  // order is always sound (Round 11) - this terminates the loop directly,
                  // no further contraction needed.
                  r := ChainWrapRegex(g, order);
                  ChainWrapAllLabelsSore(g, order);
                  forall w | w in S ensures Matches(r, w) {
                    ChainWrapSound(g, order, w);
                  }
                  return;
                } else {
                  // Defensive fallback only: shouldn't happen given the priority chain
                  // above, but if TopoSort ever can't complete, fall back to the
                  // always-sound (if lossy) wildcard collapse.
                  var oldG := g;
                  g := ExecCollapseAll(oldG);
                }
              }
            }
          }
        }
      }
    }

    r := FinishSingleInteriorNode(g, S, w0);
  }
}
