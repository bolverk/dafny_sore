// CLI entry point for the bigram-graph based alternative SORE inference
// (BigramGraph.InferViaBigramGraph, in Graph.dfy) - mirrors Main.dfy exactly, just
// calling the bigram-graph algorithm instead of the tiered heuristic in Infer.dfy.
// Both produce the same shared RegexCore.Regex type, so the same PrettyPrint/Simplify
// printer in Print.dfy is reused unchanged - no separate printer needed.
include "Regex.dfy"
include "Graph.dfy"
include "Print.dfy"

module MainBigram {
  import opened RegexCore
  import opened BigramGraph
  import opened Print

  method Run(strs: seq<string>) returns (text: string) {
    var S := set t | t in strs :: t;
    var r := InferViaBigramGraph(S);
    text := PrettyPrint(Simplify(r));
  }

  method Main(args: seq<string>) {
    var text := Run(args);
    print text, "\n";
  }
}
