"""Reproduce the #746 t=3 high-q residue and inverse-cone census.

The inverse-parent implementation is the exact two-arm ResetParent grammar
from im-results/agent10-cascade/FirstInverseComplete.lean. This script is a
finite computational audit, not a proof of global nonreachability.
"""
from __future__ import annotations

from collections import Counter
from functools import lru_cache
import json
import statistics

MODULUS = 3**8
PERIOD = 2 * 3**7
SECTORS = (4, 5)


def deficit(n: int, j: int) -> int:
    """Closed form D_j(n) = 2^j(2n+3) - (n-1)."""
    return (1 << j) * (2 * n + 3) - (n - 1)


def margin_holds(n: int, j: int) -> bool:
    return 2048 * deficit(n, j) + 16384 * n + 16384 <= (1 << n)


def max_margin_depth(n: int) -> int:
    """Largest j satisfying the monotone source margin, by binary search."""
    lo, hi = 0, n + 1
    while lo < hi:
        mid = (lo + hi) // 2
        if margin_holds(n, mid):
            lo = mid + 1
        else:
            hi = mid
    return lo - 1


def signed_z_mod(n: int, j: int) -> int:
    """2*ray(n,j)+5, reduced modulo 3^8 using its closed form."""
    return (
        8 * pow(2, n, MODULUS)
        - pow(2, j + 1, MODULUS) * (2 * n + 3)
        + 2 * n + 3
    ) % MODULUS


def high_gate_quotient_residue(n: int) -> int:
    """c_n with 32*c_n = 2^(n+1)+2n-1 (mod 81); 32^-1=38."""
    return (38 * (pow(2, n + 1, 81) + 2 * n - 1)) % 81


def primitive_power_index() -> dict[int, int]:
    """Map each unit modulo 3^8 to its unique exponent j in 2^(j+1)."""
    result: dict[int, int] = {}
    power = 2
    for j in range(PERIOD):
        if power in result:
            raise AssertionError("2 did not have the claimed order")
        result[power] = j
        power = (power * 2) % MODULUS
    if len(result) != PERIOD or power != 2:
        raise AssertionError("unexpected order of 2 modulo 3^8")
    if any(value % 3 == 0 for value in result):
        raise AssertionError("a power of 2 was not a unit")
    return result


def unique_high_gate_residue(n: int, power_index: dict[int, int]) -> tuple[int, int]:
    """Return (j0,c_n) for the unique j0 mod 4374 with Z(n,j0)=81*c_n."""
    c_n = high_gate_quotient_residue(n)
    numerator = (8 * pow(2, n, MODULUS) + 2 * n + 3 - 81 * c_n) % MODULUS
    coefficient = (2 * n + 3) % MODULUS
    if numerator % 3 == 0 or coefficient % 3 == 0:
        raise AssertionError("the target equation must be a unit equation")
    rhs = numerator * pow(coefficient, -1, MODULUS) % MODULUS
    j0 = power_index[rhs]
    if signed_z_mod(n, j0) != 81 * c_n % MODULUS:
        raise AssertionError("discrete-log residue failed its defining congruence")
    return j0, c_n


def odd_valuation(x: int) -> int:
    """v_3(x), for positive x."""
    value = 0
    while x % 3 == 0:
        x //= 3
        value += 1
    return value


def reset_parents(u: int) -> list[int]:
    """All exact ResetParent predecessors of u from the two source arms."""
    parents: list[int] = []

    # Even arm: 6*2^k-1 <= u <= 8*2^k-3 and 2u=8*2^k+h+k.
    k = u.bit_length() - 3
    if k >= 0:
        scale = 1 << k
        if 6 * scale - 1 <= u <= 8 * scale - 3:
            h = 2 * u - 8 * scale - k
            if h >= 0:
                if h >= u:
                    raise AssertionError("even parent did not strictly decrease")
                parents.append(h)

    # Odd arm: 2u+5=3^(t+1)d, d odd, and 2^t*d in an odd inverse band.
    z = 2 * u + 5
    valuation = odd_valuation(z)
    for t in range(valuation):
        d = z // (3 ** (t + 1))
        if d % 2 != 1:
            raise AssertionError("odd numerator quotient should remain odd")
        x = (1 << t) * d
        k = x.bit_length() - 3
        if k < 0:
            continue
        scale = 1 << k
        if 6 * scale + 1 <= x <= 8 * scale - 1:
            h = 2 * x - 8 * scale - k - 5
            if h >= 0:
                if h >= u:
                    raise AssertionError("odd parent did not strictly decrease")
                parents.append(h)
    return parents


def inverse_cone(target: int) -> tuple[set[int], int, int]:
    """Return (all ancestors, maximum path depth, edge count)."""
    @lru_cache(maxsize=None)
    def depth(u: int) -> int:
        ps = reset_parents(u)
        return 0 if not ps else 1 + max(depth(h) for h in ps)

    seen: set[int] = set()
    stack = [target]
    edges = 0
    while stack:
        u = stack.pop()
        if u in seen:
            continue
        seen.add(u)
        ps = reset_parents(u)
        edges += len(ps)
        stack.extend(h for h in ps if h not in seen)
    return seen, depth(target), edges


def audit(limit: int = 10_000) -> dict[str, object]:
    power_index = primitive_power_index()
    candidates: list[tuple[int, int, int, int, int, int, int, int, int]] = []
    n_counts: Counter[int] = Counter()
    for n in range(20, limit + 1):
        if n % 6 not in SECTORS:
            continue
        j0, c_n = unique_high_gate_residue(n, power_index)
        j_max = max_margin_depth(n)
        for j in range(j0, j_max + 1, PERIOD):
            if not margin_holds(n, j):
                raise AssertionError("binary-search margin endpoint was invalid")
            z = 2 * (4 * (1 << n) - deficit(n, j)) + 5
            if z % 81 != 0 or z % MODULUS != 81 * c_n % MODULUS:
                raise AssertionError("high-gate congruence failed")
            d_ray = z // 81
            k_ray = n - 3
            if not (6 * (1 << k_ray) + 1 <= 8 * d_ray <= 8 * (1 << k_ray) - 1):
                raise AssertionError("t=3 ray-parent band failed")
            q = 16 * d_ray - (1 << n) - n - 2
            if q % 3 != 2 or (2 * q + 5) % 81 != 0:
                raise AssertionError("second high-gate condition failed")
            d_q = (2 * q + 5) // 81
            r = 16 * d_q - (1 << (n - 3)) - n + 1
            r1 = 2 * r - (1 << (n - 3)) - n + 6
            candidates.append((n, j, j0, d_ray, q, d_q, r, r1, c_n))
            n_counts[n] += 1

    r_mod3: Counter[int] = Counter()
    q_valuation: Counter[int] = Counter()
    cone_sizes: list[int] = []
    max_cone: tuple[int, int, int, int, int] | None = None
    max_depth: tuple[int, int, int] | None = None
    for n, j, _j0, _d_ray, q, _d_q, r, _r1, _c_n in candidates:
        r_mod3[r % 3] += 1
        q_valuation[odd_valuation(2 * q + 5)] += 1
        cone, depth, edges = inverse_cone(q)
        if 2 in cone:
            raise AssertionError(f"root 2 reached from candidate (n,j)=({n},{j})")
        cone_sizes.append(len(cone))
        if max_cone is None or len(cone) > max_cone[0]:
            max_cone = (len(cone), n, j, depth, edges)
        if max_depth is None or depth > max_depth[0]:
            max_depth = (depth, n, j)

    return {
        "limit": limit,
        "modulus": MODULUS,
        "period": PERIOD,
        "candidate_count": len(candidates),
        "distinct_n": len(n_counts),
        "candidate_multiplicity_per_n": dict(sorted(Counter(n_counts.values()).items())),
        "r_mod_3": dict(sorted(r_mod3.items())),
        "v3_2q_plus_5": dict(sorted(q_valuation.items())),
        "inverse_cone_size": {
            "min": min(cone_sizes),
            "median": statistics.median(cone_sizes),
            "mean": statistics.mean(cone_sizes),
            "max": max_cone,
        },
        "inverse_cone_max_depth": max_depth,
        "all_cones_exclude_root_2": True,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
