#!/usr/bin/env python3
"""Reproduce DRegular arithmetic candidates 14 through 17.

This imports the checked-in transition formulas used by check_root12.py.
It is an arithmetic replay of the DRegular abstraction, not an independent
raw-tape simulation and not a substitute for the original-source Lean proof.
"""

from __future__ import annotations

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "agent2-cryptid-continuity"))

from check_eighth_root import (  # noqa: E402
    L,
    advance,
    find_exception,
    second_of_exception,
    fingerprint,
)


def main() -> None:
    state, index = L(9), 0
    expected_first_six = (8394, 9422, 12089, 23037, 27291, 31787)

    for episode, expected in enumerate(expected_first_six, 1):
        index, state = find_exception(state, index)
        assert index == expected, (episode, index, expected)
        if episode < 6:
            state = second_of_exception(state)
            assert state is not None
            index += 2

    t6 = (state.a - 7) // 9
    assert t6 % 27 == 23
    state = L(32768 * (t6 // 27) + 28577, 3, 2)
    index += 5
    state = advance(state, 34)
    index += 34
    assert (index, state.a % 9, state.q, state.b) == (31826, 4, 3, 1)

    t7 = (state.a - 4) // 9
    state = L(64 * t7 + 23, 1, 5)
    index += 2
    state = advance(state, 6046)
    index += 6046
    assert (index, state.a.bit_length(), state.a % 9, state.q, state.b) == (
        37874, 53597, 1, 3, 1
    )
    assert fingerprint(state.a) == (
        "dca8fef2d5858a9a53065a3dd9d73a068bceb4d4df0a0ede58eeceed341ef952"
    )

    t8 = (state.a - 10) // 9
    state = L(64 * t8 + 81)
    index += 2
    state = advance(state, 6090)
    index += 6090
    assert (index, state.a.bit_length(), state.a % 9, state.q, state.b) == (
        43966, 62217, 4, 9, 1
    )

    t9 = (state.a - 4) // 9
    state = L(64 * t9 + 35, 1, 5)
    index += 2
    state = advance(state, 41)
    index += 41
    assert (index, state.a % 9, state.q, state.b) == (44009, 4, 6, 1)

    t10 = (state.a - 4) // 9
    state = L(64 * t10 + 29, 1, 5)
    index += 2
    state = advance(state, 1708)
    index += 1708
    assert (index, state.a.bit_length(), state.a % 9, state.q, state.b) == (
        45719, 64698, 7, 6, 1
    )

    t11 = (state.a - 7) // 9
    assert t11 % 27 == 4
    state = L(32768 * (t11 // 27) + 5493)
    index += 5
    state = advance(state, 1759)
    index += 1759
    assert (index, state.a.bit_length(), state.a % 9, state.a % 81,
            state.q, state.b) == (47483, 67194, 1, 37, 7, 1)

    t12 = (state.a - 10) // 9
    state = L(64 * t12 + 91, 3, 2)
    index += 2
    state = advance(state, 3679)
    index += 3679
    assert (index, state.a.bit_length(), state.a % 9, state.q, state.b) == (
        51164, 72403, 4, 6, 1
    )

    t13 = (state.a - 4) // 9
    state = L(64 * t13 + 29, 1, 5)
    index += 2
    assert index == 51166

    expected = (
        (5169, 4, 5, 3, 79720, 31,
         "ba4659f0c9e798bb7ebd0b41801f61be5e3263b2d87278cd5652f8b4e0c70d1a"),
        (6821, 4, 8, 14, 89375, 49,
         "16096123fac4a5f3e8ba277524b9437a0fcdaf4b6c47a87b98f222a3f7e6a9fe"),
        (2077, 4, 5, 26, 92317, 76,
         "4a5b86899e571cf3f3bfa654d6d8c24b558d15b4b72cfbc702cf70f13eadc0a1"),
        (2656, 7, 7, 6, 96078, 61,
         "5c039ec769ccca913198f39e56298967381910731491d6ceed124768ce4beaf6"),
    )

    print("episode,index,regular_steps,a_mod9,q,t_mod27,bits,a_mod81,sha256_le")
    for episode, (steps, residue, q, t_mod27, bits, mod81, digest) in enumerate(
        expected, 14
    ):
        state = advance(state, steps)
        index += steps
        t = (state.a - (7 if residue == 7 else 4)) // 9
        actual = (
            state.a % 9,
            state.q,
            t % 27,
            state.a.bit_length(),
            state.a % 81,
            fingerprint(state.a),
        )
        target = (residue, q, t_mod27, bits, mod81, digest)
        assert actual == target, (episode, index, actual, target)
        assert next_regular_is_exception(state)
        print(
            f"{episode},{index},{steps},{residue},{q},{t_mod27},"
            f"{bits},{mod81},{digest}"
        )
        if episode < 17:
            state = second_of_exception(state)
            assert state is not None
            index += 2

    assert index == 67895
    print("PASS: DRegular arithmetic replay through the seventeenth exception.")
    print("The seventeenth case has t mod 3 = 0, q = 7, and EAllDouble parameter 6.")

    # Provisional lookahead: assume the proposed seventeenth E/E/A source
    # theorem returns to L(8*(64*u17+10)+39,3,2). The following root transports
    # are arithmetic predictions until their source-level Lean chain is added.
    t17 = (state.a - 7) // 9
    assert t17 % 27 == 6
    u17 = t17 // 3
    state = L(8 * (64 * u17 + 10) + 39, 3, 2)
    index += 3

    lookahead = (
        (2902, 4, 3, 22, 100189, 40,
         "9e243d9b93114e44802052832ec31474654f0b102cc3bb6f560aa3a53b81e5e0"),
        (9780, 1, 9, 12, 114030, 37,
         "a1a269cbba34f375f7dd0b253daa0aec8cfd3c68de2e6a6cd453e18364ff3eb5"),
        (2040, 7, 5, 4, 116920, 43,
         "a6f7923f597dff19cebe20c4ee6552be60eed28736dbec6ae944072cb10bbdef"),
    )
    print("LOOKAHEAD (assumes the proposed seventeenth source reentry):")
    print("episode,index,regular_steps,a_mod9,q,t_mod27,bits,a_mod81,sha256_le")
    for episode, (steps, residue, q, t_mod27, bits, mod81, digest) in enumerate(
        lookahead, 18
    ):
        state = advance(state, steps)
        index += steps
        offset = 7 if residue == 7 else 4 if residue == 4 else 10
        t = (state.a - offset) // 9
        actual = (
            state.a % 9,
            state.q,
            t % 27,
            state.a.bit_length(),
            state.a % 81,
            fingerprint(state.a),
        )
        target = (residue, q, t_mod27, bits, mod81, digest)
        assert actual == target, (episode, index, actual, target)
        assert next_regular_is_exception(state)
        print(
            f"{episode},{index},{steps},{residue},{q},{t_mod27},"
            f"{bits},{mod81},{digest}"
        )
        if episode == 18:
            state = L(64 * t + 23, 1, 5)  # Agent25 BGeneral, p=1
            index += 2
        elif episode == 19:
            state = L(64 * t + 113, 0, 0)  # Agent25 EAGeneral, p=2
            index += 2

    assert index == 82624
    print("PASS: arithmetic lookahead through the twentieth exception.")
    print("The twentieth candidate is in the k=3t+1, t=1 mod 3, q=5 off-L family.")


def next_regular_is_exception(state: L) -> bool:
    from check_eighth_root import next_regular

    return next_regular(state) is None


if __name__ == "__main__":
    main()
