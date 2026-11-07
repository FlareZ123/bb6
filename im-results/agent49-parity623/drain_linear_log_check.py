"""Finite checks for the sharp linear-logarithmic B-drain bounds.

This is an independent Python mirror of the source equations in
Agent8LogRightSource.lean. It is supporting computational evidence only;
the universal statements are intended to be proved in DrainLinearLogSource.lean.
"""


def eval_a(a: int, k: int, m: int):
    """Exact evaluator recursion, with the source's digit-2/zero/one cases."""
    while True:
        q, r = divmod(k, 3)
        if r == 2:
            return a + 1, q, m
        if a == 0:
            if r == 0:
                return None
            return 0, q, m
        if r == 0:
            return a - 1, q, m + 2
        a, k, m = a - 1, q, m + 2 * q + 3


def drain_b(a: int, b: int, d: int):
    """Exact B-drain recursion, returning None on an unsuccessful call."""
    while b:
        out = eval_a(a, b - 1, d + 2 * b + 3)
        if out is None:
            return None
        a, b_next, d = out
        if b_next >= b:
            return None
        b = b_next
    return a, d


def check(max_n: int = 9) -> None:
    for n in range(1, max_n + 1):
        limit = 3**n
        max_excess = -1
        max_loss = -1
        checked = 0

        # The d-coordinate is translation-equivariant, so d=0 suffices.
        for b in range(limit):
            for a in range(n + 25):
                out = drain_b(a, b, 0)
                if out is None:
                    continue
                aa, dd = out
                excess = dd - 3 * b
                loss = a - aa
                assert excess <= 4 * n + 2, (n, a, b, aa, dd, excess)
                assert loss <= n + 1, (n, a, b, aa, dd, loss)
                max_excess = max(max_excess, excess)
                max_loss = max(max_loss, loss)
                checked += 1

        # One family simultaneously attains both bounds.
        sharp_b = (5 * 3 ** (n - 1) - 1) // 2
        sharp_out = drain_b(n + 1, sharp_b, 0)
        assert sharp_out == (0, 3 * sharp_b + 4 * n + 2), (
            n, sharp_b, sharp_out
        )

        # The first-counter bound also has a second simple sharp family.
        loss_b = (3**n + 1) // 2
        loss_out = drain_b(n + 1, loss_b, 0)
        assert loss_out is not None and loss_out[0] == 0, (
            n, loss_b, loss_out
        )

        assert max_excess == 4 * n + 2, (n, max_excess)
        assert max_loss == n + 1, (n, max_loss)
        print(
            f"n={n}: checked={checked}, max_excess={max_excess}, "
            f"max_loss={max_loss}, sharp_b={sharp_b}, "
            f"loss_b={loss_b}"
        )


if __name__ == "__main__":
    check()
