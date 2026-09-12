include "Regex.dfy"
include "Chain.dfy"
include "Infer.dfy"
include "Print.dfy"

module Main {
  import opened RegexCore
  import opened SoreInfer
  import opened Print

  method Run(strs: seq<string>) returns (text: string) {
    var S := set t | t in strs :: t;
    var r := Infer(S);
    text := PrettyPrint(Simplify(r));
  }

  method Main(args: seq<string>) {
    var text := Run(args);
    print text, "\n";
  }
}
