"""Reproduce the exact Agent43 B8/M32 Machine C quotient overlap audit.

The original quotient is an overapproximation of genuine blank-root reachability.
A seen quotient cell is UNKNOWN, not proof of a genuine visit. This script
distinguishes older quotient-forbidden sliver inputs from newly source-proved
unreachable states that the quotient still permits.

Use the source-verified Lean theorem odd_seven_slope_blank_unreachable in
im-results/agent3-c-bounce-inverse/OddSevenSliver.lean for the mathematical
proof. Its validity does not depend on this script.
"""

from agent43_c32_certificate import enc, graph, q


def main() -> None:
    seen = graph()  # Verifies 31,570 cells, 189,834 edges and full closure.

    def admitted(a: int, k: int) -> bool:
        return bool(seen[enc(q(a), q(k), q(0))])

    # Former candidate: these two exact source-inaccessible wedges were
    # already absent from the stronger Agent43 quotient, so no new decision.
    for p in range(16):
        for n in range(16):
            if p + n >= 1:
                assert not admitted(16 * p + 1, 16 * n + 7)
            assert not admitted(16 * p + 9, 16 * n + 15)

    # Exact new family T_(p,n), all absent from the genuine blank orbit by
    # original-source Lean, nonetheless allowed by Agent43's quotient.
    # The quotient's high coordinate period is 32, so p=0..7 already
    # spans its distinct x projections; n has no effect on high residues.
    assert all(admitted(8 * p, 8 * p + 64 * n + 23)
               for p in range(8) for n in range(4))
    assert admitted(0, 23)
    print("Agent43 B8/M32 graph: 31570 source-closed cells, 189834 edges")
    print("Previous odd sliver wedges: absent in quotient (redundant exclusions)")
    print("New source-verified line (8p, 8p+64q+23): all quotient cells seen")
    print("Its genuine blank nonreachability is in OddSevenSliver.lean")


if __name__ == "__main__":
    main()
