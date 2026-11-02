#!/usr/bin/env python3
"""Reproducible depth-4 and depth-5 extension of the Agent 17 Sheep sieve.

The imported sieve is the exact all-exponent modular inverse-tree checker,
not a finite orbit test. It verifies every candidate valuation's period.
"""
from hashlib import sha256
from pathlib import Path
import sys

SOURCE = Path(__file__).resolve().parents[1] / "agent17-sheep-third-generation"
sys.path.insert(0, str(SOURCE))
from symbolic_sieve import (  # noqa: E402
    Family, MODULUS, check_small_exponents, inverse_tree_closes
)

EXPECTED = {
    3: (3544, "3501152b8f0e5feb4d45fce3505e4457264d2f6001b2ea675508abde300ccb37"),
    4: (3590, "a428450076921a5ca8adef12ade61fcb63b421e6a9c48ae49eb12d41e8469fca"),
    5: (3596, "dc77776f9a51938d6c6e1fdb57be681477dae9b93d54fa351d4d4f9ae4b6555b"),
}
ADDED = {
    4: (46, "89426f4836e98f855a347bf14307300bdd405a543999560562c168c5e65ce10e"),
    5: (6, "be4adfc9a970efb01ee97326b3d1e37231bc8fe859e47d0f6e690e4f4c3c0b22"),
}


def digest(values: list[int]) -> str:
    return sha256(",".join(map(str, values)).encode("ascii")).hexdigest()


def main() -> None:
    assert MODULUS == 5400
    assert check_small_exponents() == 252
    root = Family(0, 0, 1)
    previous: set[int] = set()
    original: set[int] = set()
    for depth in (3, 4, 5):
        values = [
            r for r in range(MODULUS)
            if inverse_tree_closes(root, r, MODULUS, depth)
        ]
        count, expected_hash = EXPECTED[depth]
        assert len(values) == count
        assert digest(values) == expected_hash
        current = set(values)
        assert previous <= current
        print(f"Depth {depth}: {len(values)}/{MODULUS}; SHA256 {digest(values)}", flush=True)
        if depth == 3:
            original = current
        else:
            new = sorted(current - previous)
            new_count, new_hash = ADDED[depth]
            assert len(new) == new_count and digest(new) == new_hash
            print(f"Depth {depth} newly closed: {new}", flush=True)
        previous = current

    new_all = sorted(previous - original)
    assert len(new_all) == 52
    # Newly certified residue set is invariant under +2700 modulo 5400.
    assert all(((r + 2700) % 5400 in new_all) for r in new_all)
    print("PASS: 52 previously unexcluded classes, periodic mod 2700.", flush=True)
    print("All exponents <100 are separately excluded by the certified monotone prefix.")


if __name__ == "__main__":
    main()
