"""Pure, reproducible generator for exact P1 affine inverse-shadow certificates.

The generated Lean Boolean checks, combined with source-verified theorems
AdaptiveParam.check_sound and AffineParamRoot, provide the proof; this generator
does not assert any mathematical conclusion on its own.
"""
from collections import deque


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def base_graph(q: int, side: int, limit: int = 50_000) -> set[tuple[int, int]]:
    assert q >= 29 and side in (8, 9)
    c = 12 if side == 8 else 10
    root = (0, c * q + 4)
    seen = {root}
    queue = deque([root])
    while queue:
        m, z = queue.popleft()
        for t in range(v2(z) + 1):
            n = 16 * q + side + m + t + z // (1 << t)
            if n % 2:
                child = (m + t + 1, n // 2)
                if child not in seen:
                    seen.add(child)
                    queue.append(child)
                    if len(seen) > limit:
                        raise OverflowError("Base graph exceeds limit; no certificate")
    return seen


def minimal_period_exponent(q: int) -> int:
    """Least power-of-two exponent preserving every base-graph path's valuation."""
    best = 0
    for side in (8, 9):
        c = 12 if side == 8 else 10
        nodes = base_graph(q, side)
        best = max(best, *(m + v2(z) + 1 - v2(c) for m, z in nodes))
    return best


def affine_graph(q: int, side: int, exponent: int,
                 limit: int = 50_000) -> set[tuple[int, int, int, int]]:
    assert q >= 29 and side in (8, 9) and exponent >= 0
    p = 1 << exponent
    c = 12 if side == 8 else 10
    root = (0, c * q + 4, c * p)
    queue = deque([root])
    seen = {root}
    while queue:
        m, a, b = queue.popleft()
        k = v2(a) + 1
        if b % (1 << k):
            raise ValueError(f"Affine valuation failure at {(m, a, b, k)}")
        for t in range(k):
            if a % (1 << t):
                continue
            n = 16 * q + side + m + t + a // (1 << t)
            if n % 2:
                child = (m + t + 1, n // 2, 8 * p + b // (1 << (t + 1)))
                if child not in seen:
                    seen.add(child)
                    queue.append(child)
                    if len(seen) > limit:
                        raise OverflowError("Affine graph exceeds limit; no certificate")
    return {(m, a, b, v2(a) + 1) for m, a, b in seen}


def verified_graphs(q: int) -> tuple[int, list[list[tuple[int, int, int, int]]]]:
    exponent = minimal_period_exponent(q)
    graphs = []
    for side in (8, 9):
        base = base_graph(q, side)
        affine = affine_graph(q, side, exponent)
        assert {(m, a) for m, a, b, k in affine} == base
        graphs.append(sorted(affine))
    for r in (0, 1, 2, 7):
        for index, side in enumerate((8, 9)):
            lifted = {(m, a + b * r) for m, a, b, k in graphs[index]}
            assert lifted == base_graph(q + (1 << exponent) * r, side)
    return exponent, graphs


def render_lean(q: int, period_name: str = "P") -> str:
    """Return a source-checkable Lean finite certificate without writing files."""
    exponent, graphs = verified_graphs(q)
    budget = max(m for nodes in graphs for m, a, b, k in nodes)
    cutoff = max(k for nodes in graphs for m, a, b, k in nodes)
    lines = [
        "import AdaptiveParam",
        "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 0",
        "namespace BB6.Agent13Narrow",
        "open BB6.Agent13AdaptiveParam",
        f"def {period_name} : Nat := {1 << exponent}",
    ]
    for feeder, nodes in enumerate(graphs):
        payload = ",\n".join(f"  ({m},{a},{b},{k})" for m, a, b, k in nodes)
        lines.extend([
            f"def q{q}nodes{feeder} : List (Nat×Nat×Nat×Nat) := [\n{payload}\n]",
            f"theorem q{q}check{feeder} : check {cutoff} {budget} "
            f"{16*q+8+feeder} {period_name} q{q}nodes{feeder} = true := by decide",
            f"#print axioms q{q}check{feeder}",
        ])
    lines.append("end BB6.Agent13Narrow")
    return "\n\n".join(lines) + "\n"
