"""Finite synthetic #623 two-step terminal-parent diagnostics.

Run beside coverage.py. This is a finite source-mirrored simulation and
does not infer blank-root reachability, machine halting or nonhalting.
"""

from coverage import transition


def main():
    witnesses = []
    for a in range(2, 502, 2):
        for d in range(501):
            daughter = transition(a, d)
            if daughter is not None and transition(*daughter) is None:
                witnesses.append((a, d, *daughter))
    assert len(witnesses) == 383
    assert (2, 9, 10, 10) in witnesses
    assert (20, 0, 16, 14) in witnesses
    assert (38, 1, 30, 25) in witnesses
    print("Positive even-first-coordinate synthetic parents in grid:", len(witnesses))
    print("Exact witness examples:", [(2, 9, 10, 10), (20, 0, 16, 14),
                                      (38, 1, 30, 25)])
    print("The blank-origin orbit may avoid all these parents.")


if __name__ == "__main__":
    main()
