"""Finite modular overapproximation of Cryptids holdout #429's macro map.

Exploratory instrumentation. The Lean theorems in BB429Mod32Six.lean
independently certify the modulo-32 restriction for the actual blank-root
orbit. This quotient intentionally contains infeasible branch paths.
"""
from collections import deque


def successors(modulus: int, u: int, w: int):
    """Conservative successors of (u mod P, w mod 2P)."""
    width = modulus * 2
    m = w // 2
    d = u - m
    out = set()

    def add(a: int, b: int) -> None:
        out.add((a % modulus, b % width))

    # The first-branch size guard is deliberately omitted.
    add(2 * u + 3, w - 2 * u - 3)
    if (w - (2 * u + 2)) % width == 0:
        add(0, 4 * u + 18)
    if (w - (2 * u + 1)) % width == 0:
        add(11, 4 * u + 2)
    if (w - 2 * u) % width == 0:
        add(0, 4 * u + 12)
    if w % 2 == 0:
        if (d - 1) % modulus == 0:
            add(0, 2 * w + 12)
        if d % 2 == 0:
            add(11, 2 * u + w - 2)
        else:
            add(0, 2 * u + w + 10)
    else:
        if (d - 2) % modulus == 0:
            add(0, 2 * w + 8)
        if d % 2 == 0:
            # The exceptional w=1 branch can only originate here.
            if w == 1:
                add(11, 2 * u + 10)
            # The w>=3 guard is intentionally omitted.
            add(d + 7, 2 * w - 4)
        else:
            add(d + 3, 2 * w)
    return out


def abstract_reachability(modulus: int):
    if modulus < 2 or modulus & (modulus - 1):
        raise ValueError('modulus must be a power of two at least 2')
    seen = {(0, 0)}
    pending = deque([(0, 0)])
    while pending:
        u, w = pending.popleft()
        for state in successors(modulus, u, w):
            if state not in seen:
                seen.add(state)
                pending.append(state)
    gate_residues = tuple(
        u for u in range(modulus)
        if (u, (2 * u - 1) % (2 * modulus)) in seen
    )
    return seen, gate_residues


if __name__ == '__main__':
    for power in range(1, 8):
        p = 1 << power
        seen, gates = abstract_reachability(p)
        print(f'P={p:<3} states={len(seen):<5}/{2*p*p:<6} gate_u_residues={gates}')
