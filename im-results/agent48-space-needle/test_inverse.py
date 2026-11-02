"""Single-file reproducibility test for Space Needle exact inverse search."""
import hashlib
from inverse import high_level_next, predecessors, reverse_cone


def main() -> None:
    for d in range(10000):
        successor = high_level_next(d)
        if successor is not None:
            assert d in predecessors(successor), (d, successor)
    print("Round trip: 10000 input counters, all nonterminal steps inverted")

    lines = []
    largest = (0, 0)
    no_incoming = 0
    for power in range(2, 3001):
        cone = reverse_cone((1 << power) - 2)
        assert 1 not in cone, (power, "blank-entry counter found")
        if len(cone) == 1:
            no_incoming += 1
        if len(cone) > largest[1]:
            largest = (power, len(cone))
        lines.append(f"{power},{len(cone)},0")
    digest = hashlib.sha256(("\n".join(lines) + "\n").encode()).hexdigest()
    assert digest == "ac278b8dea30013c5dd918cd29742a75a5485df79e21ff9508b8760c5012ea6c"
    assert largest == (1099, 19)
    assert no_incoming == 1803
    print("Complete predecessor cones: terminal exponents 2 through 3000 (2999 targets)")
    print(f"No initial counter found; immediate in-degree zero at {no_incoming} targets")
    print(f"Largest predecessor cone: exponent {largest[0]}, {largest[1]} nodes")
    print(f"SHA-256 of CSV (exponent,cone_size,initial_hit): {digest}")


if __name__ == "__main__":
    main()
