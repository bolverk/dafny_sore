#!/usr/bin/env python3
"""CLI wrapper around the bigram-graph based alternative SORE inference engine.

Usage:
    python3 ./sore_bigram.py STRING [STRING ...]

Prints one line: a Python `re`-compatible regex that is sound for every given
input string (accepts each one) and single-occurrence (every alphabet symbol
appears at most once in it), per the proved theorems on InferViaBigramGraph in
src/Graph.dfy. This is a separate, standalone implementation from the tiered
heuristic used by sore.py/Infer - see src/Graph.dfy's header comment for the
7-step bigram-graph algorithm this implements.

The regex text itself is produced by src/Print.dfy's PrettyPrint, a plain
display utility with no Dafny-level correctness proof of its own (unlike
InferViaBigramGraph, which is formally verified). As defense in depth, this
script re-parses the printed text with Python's own `re` module and confirms
it actually accepts every input string before printing anything - see
README.md.
"""
import os
import re
import sys

_BUILD_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "build", "sore_bigram-py")
if not os.path.isdir(_BUILD_DIR):
    sys.exit(
        "error: {} not found.\n"
        "Build it first with:\n"
        "  dafny build --target:py src/Regex.dfy src/Graph.dfy "
        "src/Print.dfy src/MainBigram.dfy --output build/sore_bigram".format(_BUILD_DIR)
    )
sys.path.insert(0, _BUILD_DIR)

import _dafny  # noqa: E402
import MainBigram  # noqa: E402


def _dafny_str(s: str):
    return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, s))


def infer_regex(strings):
    """Run the verified Dafny InferViaBigramGraph (+ Simplify/PrettyPrint) on a list of strings."""
    dafny_args = _dafny.Seq([_dafny_str(s) for s in strings])
    text_seq = MainBigram.default__.Run(dafny_args)
    return text_seq.VerbatimString(False)


def main(argv):
    strings = argv[1:]

    pattern_text = infer_regex(strings)

    try:
        compiled = re.compile(pattern_text)
    except re.error as exc:
        sys.exit(
            "internal error: PrettyPrint produced an invalid regex {!r} ({})".format(
                pattern_text, exc
            )
        )

    for s in strings:
        if compiled.fullmatch(s) is None:
            sys.exit(
                "internal error: printed regex {!r} does not accept input {!r} "
                "(this would mean PrettyPrint disagrees with the proved "
                "GraphAccepts/Matches semantics - please report this as a bug)".format(
                    pattern_text, s
                )
            )

    print(pattern_text)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
