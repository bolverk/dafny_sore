#!/usr/bin/env python3
"""Differential-testing harness: compare our Dafny-verified `sore.py` output
against `grex` (https://github.com/pemistahl/grex), an independent, mature
regex-inference CLI, for the same input strings.

grex is not restricted to single-occurrence output. But when it happens to
produce an already-single-occurrence regex (a "SORE") for a given input set,
that is good outside evidence that a SORE exists for that input - and this
script checks that our own tool's output defines the SAME LANGUAGE as grex's
in that case.

Usage:
    python3 compare_grex.py STRING [STRING ...]      # compare one input set
    python3 compare_grex.py --fuzz [N]               # batch-compare N random
                                                      # sets plus curated examples

What this DOES verify, for every case where grex's output is single-occurrence:
  - both regexes accept every original input string
  - both regexes agree on EVERY string up to a length bound over their combined
    alphabet (brute-force enumeration - see `_enumeration_bound` below)

What this does NOT do: this is a strong empirical check up to that length
bound, not a formal proof of language equivalence. Unlike `Infer`'s own
soundness (a proved Dafny theorem, see src/Infer.dfy), nothing here is
machine-checked for all strings of all lengths.

Prerequisite: `grex` on PATH (`cargo install grex`; on this machine the global
cargo linker config points at a nonexistent `zigcc`, so install with
`CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER=cc cargo install grex`).

Known grex quirk observed during development: grex silently drops the empty
string "" when it appears alongside other, non-empty test cases (e.g.
`grex -- "" "a"` prints `^a$`, not `^a?$`, and so does not actually accept "").
This script therefore excludes "" from generated fuzz cases and does not
attempt to compare sets containing "" together with other strings.
"""
import itertools
import os
import random
import subprocess
import sys
from collections import Counter

_HERE = os.path.dirname(os.path.abspath(__file__))
_SORE_PY = os.path.join(_HERE, "sore.py")

# --------------------------------------------------------------------------
# A small regex-text parser, just expressive enough for grex's (and our own)
# un-flagged output vocabulary: literals (incl. \-escaped metacharacters),
# [...]/[^...] character classes with ranges, (...)/(?:...) groups, |
# alternation, concatenation by juxtaposition, and *, +, ?, {m}, {m,}, {m,n}
# quantifiers on the immediately preceding atom. Constructs outside this
# vocabulary (., \d/\w/\s/\D/\W/\S, negated classes, unbalanced/unrecognized
# syntax) are represented as an explicit 'unsupported' node rather than
# silently mis-handled.
# --------------------------------------------------------------------------

UNSUPPORTED = ("unsupported",)

_ESCAPABLE_LITERALS = set(".^$*+?()[]{}|\\-")
_SHORTHAND_CLASSES = set("dDwWsSbB")


class _Parser:
    def __init__(self, s):
        self.s = s
        self.i = 0
        self.n = len(s)

    def peek(self):
        return self.s[self.i] if self.i < self.n else ""

    def eof(self):
        return self.i >= self.n

    def parse_alternation(self):
        branches = [self.parse_concat()]
        while self.peek() == "|":
            self.i += 1
            branches.append(self.parse_concat())
        if len(branches) == 1:
            return branches[0]
        return ("alt", branches)

    def parse_concat(self):
        parts = []
        while not self.eof() and self.peek() not in "|)":
            parts.append(self.parse_quantified())
        if len(parts) == 1:
            return parts[0]
        return ("concat", parts)

    def parse_quantified(self):
        atom = self.parse_atom()
        if self.eof():
            return atom
        c = self.peek()
        if c == "*":
            self.i += 1
            return ("star", atom)
        if c == "+":
            self.i += 1
            return ("plus", atom)
        if c == "?":
            self.i += 1
            return ("opt", atom)
        if c == "{":
            j = self.s.find("}", self.i)
            if j != -1:
                body = self.s[self.i + 1 : j]
                if all(ch.isdigit() or ch == "," for ch in body) and body:
                    self.i = j + 1
                    return ("repeat", atom, body)
        return atom

    def parse_atom(self):
        c = self.peek()
        if c == "(":
            self.i += 1
            if self.s[self.i : self.i + 2] == "?:":
                self.i += 2
            elif self.peek() == "?":
                # (?=...), (?!...), named groups, etc. - outside our vocabulary
                depth = 1
                start = self.i - 1
                while not self.eof() and depth:
                    if self.peek() == "(":
                        depth += 1
                    elif self.peek() == ")":
                        depth -= 1
                    self.i += 1
                return UNSUPPORTED
            inner = self.parse_alternation()
            if self.peek() != ")":
                return UNSUPPORTED
            self.i += 1
            return inner
        if c == "[":
            return self._parse_class()
        if c == ".":
            self.i += 1
            return UNSUPPORTED
        if c == "\\":
            self.i += 1
            e = self.peek()
            self.i += 1
            if e in _SHORTHAND_CLASSES:
                return UNSUPPORTED
            if e == "":
                return UNSUPPORTED
            return ("lit", e)
        if c == "" or c in ")|":
            return UNSUPPORTED
        self.i += 1
        return ("lit", c)

    def _parse_class(self):
        assert self.peek() == "["
        self.i += 1
        negated = False
        if self.peek() == "^":
            negated = True
            self.i += 1
        chars = set()
        first = True
        while not self.eof() and (self.peek() != "]" or first):
            first = False
            ch = self._read_class_char()
            if ch is None:
                return UNSUPPORTED
            if self.peek() == "-" and self.i + 1 < self.n and self.s[self.i + 1] != "]":
                self.i += 1  # consume '-'
                ch2 = self._read_class_char()
                if ch2 is None:
                    return UNSUPPORTED
                lo, hi = ord(ch), ord(ch2)
                if lo > hi:
                    return UNSUPPORTED
                for code in range(lo, hi + 1):
                    chars.add(chr(code))
            else:
                chars.add(ch)
        if self.eof():
            return UNSUPPORTED
        self.i += 1  # consume ']'
        if negated:
            return UNSUPPORTED
        return ("class", frozenset(chars))

    def _read_class_char(self):
        if self.eof():
            return None
        c = self.peek()
        if c == "\\":
            self.i += 1
            e = self.peek()
            self.i += 1
            if e in _SHORTHAND_CLASSES or e == "":
                return None
            return e
        self.i += 1
        return c


def parse_regex(text):
    """Parse a regex string (grex-style, optionally ^...$-anchored) into an AST.
    Returns UNSUPPORTED if any construct outside our vocabulary is encountered."""
    if text.startswith("^") and text.endswith("$") and len(text) >= 2:
        text = text[1:-1]
    elif text.startswith("^"):
        text = text[1:]
    elif text.endswith("$"):
        text = text[:-1]
    p = _Parser(text)
    node = p.parse_alternation()
    if not p.eof():
        return UNSUPPORTED
    return node


def symbol_counts(node):
    """Multiset of alphabet-symbol occurrences as tree LEAVES (a quantifier
    wrapping a subtree does not multiply its counts - same principle as this
    project's own Regex.dfy Opt/Plus being primitive constructors). Returns
    None if the tree contains any unsupported construct."""
    if node is UNSUPPORTED or node == UNSUPPORTED:
        return None
    tag = node[0]
    if tag == "lit":
        return Counter({node[1]: 1})
    if tag == "class":
        return Counter({c: 1 for c in node[1]})
    if tag in ("star", "plus", "opt"):
        return symbol_counts(node[1])
    if tag == "repeat":
        return symbol_counts(node[1])
    if tag in ("concat", "alt"):
        total = Counter()
        for child in node[1]:
            sub = symbol_counts(child)
            if sub is None:
                return None
            total += sub
        return total
    return None


def is_sore(text):
    """Returns (verdict, reason) where verdict is True/False/None (None =
    unsupported construct, could not determine)."""
    node = parse_regex(text)
    counts = symbol_counts(node)
    if counts is None:
        return None, "contains a construct outside our parser's vocabulary"
    bad = [c for c, n in counts.items() if n > 1]
    if bad:
        return False, "symbol(s) {} appear more than once".format(sorted(bad))
    return True, "every symbol appears at most once"


def alphabet_of(text):
    node = parse_regex(text)
    counts = symbol_counts(node)
    if counts is None:
        return None
    return set(counts.keys())


# --------------------------------------------------------------------------
# Running the two tools
# --------------------------------------------------------------------------


def run_grex(strings):
    result = subprocess.run(
        ["grex", "--", *strings], capture_output=True, text=True, timeout=30
    )
    if result.returncode != 0:
        raise RuntimeError("grex failed: {}".format(result.stderr.strip()))
    return result.stdout.strip()


def run_sore(strings):
    result = subprocess.run(
        [sys.executable, _SORE_PY, *strings], capture_output=True, text=True, timeout=60
    )
    if result.returncode != 0:
        raise RuntimeError("sore.py failed: {}".format(result.stderr.strip()))
    return result.stdout.strip()


# --------------------------------------------------------------------------
# Empirical equivalence check
# --------------------------------------------------------------------------


def _enumeration_bound(alphabet_size, target_total=300_000, hard_cap_len=12):
    if alphabet_size == 0:
        return 0
    for length in range(hard_cap_len, 0, -1):
        total = sum(alphabet_size**i for i in range(length + 1))
        if total <= target_total:
            return length
    return 1


def check_equivalence(grex_text, our_text, max_examples=5):
    """Returns (equivalent: bool, detail: str, counterexamples: list[str])."""
    grex_body = grex_text[1:] if grex_text.startswith("^") else grex_text
    grex_body = grex_body[:-1] if grex_body.endswith("$") else grex_body

    alpha_grex = alphabet_of(grex_text)
    alpha_ours = alphabet_of(our_text)
    if alpha_grex is None or alpha_ours is None:
        return None, "cannot enumerate: unsupported construct in one of the regexes", []

    alphabet = sorted(alpha_grex | alpha_ours) or ["a"]  # non-empty fallback
    length = _enumeration_bound(len(alphabet))

    try:
        grex_re = __import__("re").compile(grex_body)
        our_re = __import__("re").compile(our_text)
    except Exception as exc:  # noqa: BLE001
        return None, "regex failed to compile: {}".format(exc), []

    counterexamples = []
    total_checked = 0
    for L in range(0, length + 1):
        for tup in itertools.product(alphabet, repeat=L):
            s = "".join(tup)
            total_checked += 1
            a = grex_re.fullmatch(s) is not None
            b = our_re.fullmatch(s) is not None
            if a != b:
                counterexamples.append((s, a, b))
                if len(counterexamples) >= max_examples:
                    return (
                        False,
                        "disagree on at least {} (checked {} strings up to length {} "
                        "over alphabet {})".format(len(counterexamples), total_checked, length, alphabet),
                        counterexamples,
                    )
    return (
        True,
        "agree on all {} strings up to length {} over alphabet {}".format(
            total_checked, length, alphabet
        ),
        [],
    )


# --------------------------------------------------------------------------
# One comparison
# --------------------------------------------------------------------------


class ComparisonResult:
    def __init__(self, strings):
        self.strings = strings
        self.grex_text = None
        self.our_text = None
        self.grex_sore = None
        self.grex_sore_reason = None
        self.our_sore_selfcheck = None  # bonus: re-verify our OWN output independently
        self.our_sore_selfcheck_reason = None
        self.grex_accepts_inputs = None
        self.our_accepts_inputs = None
        self.equivalent = None
        self.equivalence_detail = None
        self.counterexamples = []
        self.error = None

    @property
    def is_finding(self):
        """A real mismatch: grex's output IS single-occurrence but does not
        match ours."""
        return self.grex_sore is True and self.equivalent is False

    def report(self):
        lines = []
        lines.append("input strings: {}".format(self.strings))
        if self.error:
            lines.append("ERROR: {}".format(self.error))
            return "\n".join(lines)
        lines.append("grex:  {}".format(self.grex_text))
        lines.append("ours:  {}".format(self.our_text))
        lines.append(
            "grex is single-occurrence: {} ({})".format(self.grex_sore, self.grex_sore_reason)
        )
        if self.our_sore_selfcheck is False:
            lines.append(
                "!! ours FAILED an independent single-occurrence re-check: {}".format(
                    self.our_sore_selfcheck_reason
                )
            )
        if self.grex_accepts_inputs is False:
            lines.append("note: grex's own output does not accept all inputs (unexpected)")
        if self.our_accepts_inputs is False:
            lines.append("!! ours does not accept all inputs (should never happen)")
        if self.grex_sore:
            lines.append("equivalence: {} ({})".format(self.equivalent, self.equivalence_detail))
            for s, a, b in self.counterexamples:
                lines.append(
                    "  counterexample {!r}: grex={} ours={}".format(s, a, b)
                )
        else:
            lines.append("(grex output is not single-occurrence - nothing to compare)")
        return "\n".join(lines)


def compare_one(strings):
    r = ComparisonResult(strings)
    try:
        r.grex_text = run_grex(strings)
    except Exception as exc:  # noqa: BLE001
        r.error = "running grex: {}".format(exc)
        return r
    try:
        r.our_text = run_sore(strings)
    except Exception as exc:  # noqa: BLE001
        r.error = "running sore.py: {}".format(exc)
        return r

    r.grex_sore, r.grex_sore_reason = is_sore(r.grex_text)
    r.our_sore_selfcheck, r.our_sore_selfcheck_reason = is_sore(r.our_text)

    import re as _re

    grex_body = r.grex_text[1:-1] if r.grex_text.startswith("^") and r.grex_text.endswith("$") else r.grex_text
    try:
        grex_re = _re.compile(grex_body)
        our_re = _re.compile(r.our_text)
        r.grex_accepts_inputs = all(grex_re.fullmatch(s) for s in strings)
        r.our_accepts_inputs = all(our_re.fullmatch(s) for s in strings)
    except Exception:  # noqa: BLE001
        pass

    if r.grex_sore:
        r.equivalent, r.equivalence_detail, r.counterexamples = check_equivalence(
            r.grex_text, r.our_text
        )
    return r


# --------------------------------------------------------------------------
# Fuzz / batch mode
# --------------------------------------------------------------------------

CURATED = [
    ["abc", "adc"],
    ["cat", "car", "cab"],
    ["SABE", "SXYE"],
    ["SABE", "SXYE", "SPQE"],
    ["abab"],
    ["ab", "ba"],
    ["ab", "ba", "cd"],
    ["prefix_a", "prefix_b", "prefix_c"],           # common-prefix-only
    ["a_suffix", "b_suffix", "c_suffix"],           # common-suffix-only
    ["wa", "wb", "wc", "wd"],                       # 4-way single-char alternation
    ["Xreq", "Xopt1", "Xopt2"],                     # asymmetric: one mandatory-ish, others vary
    ["ab", "abab", "ababab"],                       # periodic block
    ["xy", "xzy"],                                  # mandatory + optional middle char
    ["m1n", "m2n", "m3n"],                          # common prefix+suffix, single-digit middles
    ["cat", "dog"],                                 # fully disjoint groups
]


def random_string(rng, alphabet, max_len):
    length = rng.randint(1, max_len)
    return "".join(rng.choice(alphabet) for _ in range(length))


def random_case(rng):
    alphabet = rng.sample("abcde", rng.randint(2, 4))
    count = rng.randint(1, 4)
    strings = {random_string(rng, alphabet, 4) for _ in range(count)}
    return sorted(strings)


def fuzz(n):
    cases = list(CURATED)
    rng = random.Random(1234567)
    while len(cases) < n:
        c = random_case(rng)
        if c and c not in cases:
            cases.append(c)

    total = 0
    grex_sore_count = 0
    matched_count = 0
    findings = []
    errors = []

    for strings in cases:
        total += 1
        r = compare_one(strings)
        if r.error:
            errors.append(r)
            continue
        if r.grex_sore:
            grex_sore_count += 1
            if r.equivalent:
                matched_count += 1
            elif r.equivalent is False:
                findings.append(r)
            # r.equivalent is None -> unsupported construct, not counted either way

    print("=" * 72)
    print(
        "Batch summary: {} cases, {} had a single-occurrence grex output, "
        "{} of those matched ours".format(total, grex_sore_count, matched_count)
    )
    if errors:
        print("{} case(s) errored while running the tools:".format(len(errors)))
        for r in errors:
            print(r.report())
            print("-" * 72)

    if findings:
        print()
        print("!!! {} MISMATCH(ES) FOUND !!!".format(len(findings)))
        for r in findings:
            print("-" * 72)
            print(r.report())
    else:
        print("No mismatches found.")
    print("=" * 72)
    return 1 if findings else 0


def main(argv):
    if len(argv) >= 2 and argv[1] == "--fuzz":
        n = int(argv[2]) if len(argv) > 2 else 300
        return fuzz(n)

    strings = argv[1:]
    if not strings:
        print("usage: compare_grex.py STRING [STRING ...]  |  compare_grex.py --fuzz [N]")
        return 2

    r = compare_one(strings)
    print(r.report())
    return 1 if r.is_finding else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
