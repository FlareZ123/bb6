"""Exact comparison of the four Sheep E cones against the published F depth-5 sieve.

Runs the unchanged Agent17 symbolic code (and its SymPy dependency) and
rechecks Agent16's exact 3,596/5,400 digest before assessing overlap.
"""
import hashlib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] /
                       "agent17-sheep-third-generation"))
import symbolic_sieve as earlier


def main():
    base = earlier.Family(0, 0, 1)
    old = {
        r for r in range(5400)
        if earlier.inverse_tree_closes(base, r, 5400, 5)
    }
    digest = hashlib.sha256(
        ",".join(map(str, sorted(old))).encode("ascii")
    ).hexdigest()
    assert len(old) == 3596
    assert digest == "dc77776f9a51938d6c6e1fdb57be681477dae9b93d54fa351d4d4f9ae4b6555b"

    for r in (138, 402, 1218, 1738):
        # Period of a +4860 progression modulo 5400 is ten.
        residue_set = {(r + 4860 * k) % 5400 for k in range(10)}
        assert len(residue_set) == 10
        intersection = old & residue_set
        assert not intersection, (r, sorted(intersection))
        print(f"r={r}: all 10 projected mod5400 classes absent from depth-5 F exclusion")

    # LCM(4860,5400)=48600; each of the four r classes covers 10
    # disjoint residue classes in the combined period.
    new = {(r + 4860 * k) % 48600
           for r in (138, 402, 1218, 1738) for k in range(10)}
    prev = {j for j in range(48600) if j % 5400 in old}
    assert len(new) == 40 and new.isdisjoint(prev)
    assert len(prev | new) == 32404
    print("PASS: 3,596/5,400 F-depth-five classes plus 40 disjoint E-certified classes")
    print("Combined period 48,600: exact excluded density 8,101/12,150")


if __name__ == "__main__":
    main()
