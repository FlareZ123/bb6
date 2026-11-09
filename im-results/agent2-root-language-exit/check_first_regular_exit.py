"""Independent arithmetic/word-level cross-check of the D regular L first-exit certificates.

Run from any directory with Python 3.10+; imports Agent37's existing
source-derived macro interpreter without modifying its implementation.
The result is a macro-model statement, not a raw-Turing-machine theorem.
"""
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
import sys

PILOT = Path(__file__).resolve().parents[1] / "agent37-root-language-pilot"
sys.path.insert(0, str(PILOT))
from macro_engine import Config, step as word_step  # noqa: E402


@dataclass(frozen=True)
class L:
    a: int
    q: int
    b: int

    @property
    def suffix(self) -> str:
        return "01" * self.q + "1" * self.b if self.q else ""


def next_l(s: L) -> L | None:
    a, q, b = s.a, s.q, s.b
    if a % 3 == 2:
        k = (a - 2) // 3
        if q == 0:
            return L(8 * k + 9, 0, 0)
        if q == 1:
            return L(8 * k + 10 + b, 0, 0)
        return L(8 * k + 10, q - 1, b)
    if a % 3 == 0:
        k = (a - 3) // 3
        if q == 0:
            return L(8 * k + 11, 0, 0)
        r = (b + 1) // 3
        d = q - 1 + 4 * r
        if (b + 1) % 3 == 0:
            return L(8 * k + 11 + 2 * d, 0, 0)
        if (b + 1) % 3 == 1:
            return L(8 * k + 13 + 2 * d, 0, 0)
        return L(8 * k + 7 + 2 * d, 1, 5)
    k = (a - 4) // 3
    if q == 0:
        return L(8 * k + 5, 1, 5)
    if b == 0:
        return L(8 * k + 5, 1, 2 * q + 5)
    if b == 2:
        return L(8 * k + 9, q + 1, 0)
    if b >= 3:
        return L(8 * k + 9, q + 2, b - 3)
    return None


EXPECTED = {
    5: (1711, 211, 5),
    9: (8394, 157, 6),
    15: (9458, 121, 9),
    39: (7611, 46, 7),
}


def check(seed: int, expected: tuple[int, int, int]) -> None:
    index, residue, q = expected
    state = L(seed, 0, 0)
    trace = sha256()
    for i in range(index + 1):
        assert state.q >= 0 and state.b >= 0 and (state.q or state.b == 0)
        word = Config(state.a, state.suffix)
        trace.update(f"{state.a}:{state.q}:{state.b}\n".encode())
        label, cost, nxt_word = word_step(word)
        nxt = next_l(state)
        if i == index:
            assert (state.a % 243, state.q, state.b) == (residue, q, 1)
            assert nxt is None and nxt_word is not None
            assert label == "E_pairs_1100"
            expected_tail = "0" + "1" * (2 * q) + "0" + "1" * 6
            assert nxt_word.suffix == expected_tail
            k = (state.a - 4) // 3
            assert nxt_word.n == 8 * k + 5
            print(
                f"seed={seed} first_exit={index} a_bits={state.a.bit_length()} "
                f"a_mod243={residue} q={q} b=1 next_packet_p={2*q} "
                f"next_a_mod81={nxt_word.n % 81} trace_sha256={trace.hexdigest()}"
            )
            break
        assert nxt is not None, (seed, i, "premature exception")
        assert nxt_word == Config(nxt.a, nxt.suffix), (
            seed, i, label, nxt, nxt_word
        )
        assert cost is not None and cost > 0
        state = nxt


if __name__ == "__main__":
    for seed, evidence in EXPECTED.items():
        check(seed, evidence)
