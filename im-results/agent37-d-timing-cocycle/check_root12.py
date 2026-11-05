"""Reproducible exact-integer arithmetic prediction of the twelfth authentic D
exception after the earlier independently source-proved eleven checkpoints.

Numerical arithmetic is not itself a Lean source proof or a BB(6) decision.
Imports the already maintained DRegular arithmetic model from Agent2.
"""
from pathlib import Path
import sys

sys.path.insert(
    0, str(Path(__file__).resolve().parents[1] / "agent2-cryptid-continuity")
)
from check_eighth_root import L, advance, find_exception, second_of_exception, fingerprint


def main() -> None:
    s, index = L(9), 0
    for episode, expected in enumerate(
        (8394, 9422, 12089, 23037, 27291, 31787), 1
    ):
        index, s = find_exception(s, index)
        assert index == expected, (episode, index)
        if episode < 6:
            s = second_of_exception(s)
            assert s is not None
            index += 2
    assert (s.q, s.b, s.a % 243) == (4, 1, 214)
    t6 = (s.a - 7) // 9
    assert t6 % 27 == 23
    s = L(32768 * (t6 // 27) + 28577, 3, 2)
    index += 5

    s = advance(s, 34)
    index += 34
    assert (index, s.a % 9, s.q, s.b) == (31826, 4, 3, 1)
    s = L(64 * ((s.a - 4) // 9) + 23, 1, 5)
    index += 2

    s = advance(s, 6046)
    index += 6046
    assert (index, s.a.bit_length(), s.a % 9, s.q, s.b) == (
        37874, 53597, 1, 3, 1
    )
    assert fingerprint(s.a) == (
        "dca8fef2d5858a9a53065a3dd9d73a068bceb4d4df0a0ede58eeceed341ef952"
    )
    s = L(64 * ((s.a - 10) // 9) + 81)
    index += 2

    s = advance(s, 6090)
    index += 6090
    assert (index, s.a.bit_length(), s.a % 9, s.q, s.b) == (
        43966, 62217, 4, 9, 1
    )
    s = L(64 * ((s.a - 4) // 9) + 35, 1, 5)
    index += 2

    s = advance(s, 41)
    index += 41
    assert (index, s.a % 9, s.q, s.b) == (44009, 4, 6, 1)
    s = L(64 * ((s.a - 4) // 9) + 29, 1, 5)
    index += 2

    s = advance(s, 1708)
    index += 1708
    assert (index, s.a.bit_length(), s.a % 9, s.q, s.b) == (
        45719, 64698, 7, 6, 1
    )
    t11 = (s.a - 7) // 9
    assert t11 % 27 == 4
    s = L(32768 * (t11 // 27) + 5493)
    index += 5
    assert index == 45724

    s = advance(s, 1759)
    index += 1759
    assert (index, s.a.bit_length(), s.a % 9, s.a % 81, s.q, s.b) == (
        47483, 67194, 1, 37, 7, 1
    )
    print("Twelfth exception:", index, "bits", s.a.bit_length(),
          "SHA256", fingerprint(s.a), "q,b", s.q, s.b)

    t12 = (s.a - 10) // 9
    s = L(64 * t12 + 91, 3, 2)
    index += 2
    assert index == 47485

    s = advance(s, 3679)
    index += 3679
    assert (index, s.a.bit_length(), s.a % 9, s.q, s.b) == (
        51164, 72403, 4, 6, 1
    )
    print("Thirteenth candidate:", index, "bits", s.a.bit_length(),
          "q,b", s.q, s.b)
    print("PASS: exact integer root arithmetic through twelfth episode")


if __name__ == "__main__":
    main()
