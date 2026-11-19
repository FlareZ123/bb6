#!/usr/bin/env python3
"""Exact-integer diagnostics for the Sheep odd-cofactor 3-adic recurrence.

This is an experiment/checker, not a proof of nonhalting. It checks the
weighted valuation identity on the authentic first-even orbit from x=10.
Only Python's standard library is used.
"""
from __future__ import annotations

import argparse
import math


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def v3(n: int) -> int | float:
    if n == 0:
        return math.inf
    n = abs(n)
    k = 0
    while n % 3 == 0:
        n //= 3
        k += 1
    return k


def one_edge(x: int):
    """Return the exact first-even edge and its source data."""
    a = v2(x)
    u = x >> a
    if u == 1:
        return None
    special = u == 3
    if special:
        f = x + a + 3
    else:
        f = x + a + (u - 1) // 2
    z = f - 1
    h = v2(z)
    v = z >> h
    y = 1 + pow(3, h) * v
    b = v2(y)
    u_next = y >> b
    return {
        "a": a, "u": u, "h": h, "v": v, "b": b,
        "y": y, "u_next": u_next, "special": special,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=1000,
                        help="maximum number of even-return edges")
    parser.add_argument("--show", type=int, default=12,
                        help="print this many initial edge records")
    args = parser.parse_args()

    x = 10
    cumulative_weight = 0
    segment = 0
    resonant = 0
    positive_or_zero_S = 0
    max_R = 0
    shown = []
    zero_residual_shapes = {}
    resonant_unit_excess_hist = {}
    resonant_unit_mod3_cancels = 0
    terminal_resonant = 0

    for n in range(args.steps):
        edge = one_edge(x)
        if edge is None:
            print(f"HALTED at edge index {n}: x={x}")
            break

        a = edge["a"]
        u = edge["u"]
        h = edge["h"]
        b = edge["b"]
        y = edge["y"]
        u_next = edge["u_next"]

        if edge["special"]:
            # The u=3 source has its own machine clause. It is a reset:
            # the next odd cofactor is fixed by this source, not affine in u.
            segment += 1
            cumulative_weight = 0
            record = {
                "n": n, "x": x, "a": a, "u": u, "h": h, "b": b,
                "y": y, "u_next": u_next, "special": True,
                "kappa": None, "S": None, "R": None, "sigma": None,
                "R_next": None, "weight": cumulative_weight,
            }
        else:
            kappa = h + int(v3((1 << (a + 1)) + 1))
            S = pow(3, h) * ((1 << a) + a - 1) - pow(2, h) * ((1 << b) - 1)
            R = int(v3(u - 1))
            sigma = v3(S)
            lhs = kappa + R
            R_next = v3(u_next - 1)

            # Exact ultrametric recurrence for u_next - 1.
            if lhs != sigma:
                assert R_next == min(lhs, sigma), (
                    n, a, u, h, b, kappa, R, S, sigma, R_next
                )
            else:
                assert R_next >= sigma, (
                    n, a, u, h, b, kappa, R, S, sigma, R_next
                )

            # Since A>0 and u>1, S>=0 cannot produce u_next=1.
            if S >= 0:
                positive_or_zero_S += 1
                assert u_next > 1, (n, x, edge, S)

            # The all-parameter proof in README classifies S=0 exactly.
            if S == 0:
                shape = (a, h, b)
                zero_residual_shapes[shape] = zero_residual_shapes.get(shape, 0) + 1
                assert shape in {(1, 1, 2), (3, 1, 4)}, (n, shape, x)
                assert kappa == 1, (n, shape, kappa)
                assert R_next == R + 1, (n, shape, R, R_next)
                if shape == (1, 1, 2):
                    assert u % 32 == 1
                    assert u_next == (15 * u + 1) // 16
                else:
                    assert u % 128 == 1
                    assert u_next == (51 * u + 13) // 64

            if lhs == sigma:
                resonant += 1
                if S != 0:
                    t = int(v3((1 << (a + 1)) + 1))
                    P = ((1 << (a + 1)) + 1) // (3 ** t)
                    W = (u - 1) // (2 * (3 ** R))
                    S0 = S // (3 ** sigma)
                    unit_sum = P * W + S0
                    if unit_sum == 0:
                        terminal_resonant += 1
                        assert u_next == 1, (n, a, h, b, P, W, S0)
                    else:
                        excess = int(v3(unit_sum))
                        assert R_next == sigma + excess, (
                            n, a, h, b, R, sigma, R_next, unit_sum
                        )
                        resonant_unit_excess_hist[excess] = (
                            resonant_unit_excess_hist.get(excess, 0) + 1
                        )
                    if unit_sum % 3 == 0:
                        resonant_unit_mod3_cancels += 1
            max_R = max(max_R, R)
            cumulative_weight += kappa

            record = {
                "n": n, "x": x, "a": a, "u": u, "h": h, "b": b,
                "y": y, "u_next": u_next, "special": False,
                "kappa": kappa, "S": S, "R": R, "sigma": sigma,
                "R_next": R_next, "weight": cumulative_weight,
            }

        if len(shown) < args.show:
            shown.append(record)
        x = y

        if u_next == 1:
            print(f"HALTED after edge {n}: y={y}=2^{b}")
            break
    else:
        print(f"Completed {args.steps} edges without a power-of-two hit.")

    print(f"last_state_bits={x.bit_length()}")
    print(f"special_reset_segments={segment}")
    print(f"cumulative_generic_weight_since_last_reset={cumulative_weight}")
    print(f"resonant_generic_edges={resonant}")
    print(f"generic_edges_with_S_nonnegative={positive_or_zero_S}")
    print(f"maximum_source_v3(u-1)_observed={max_R}")
    print(f"zero_residual_shapes={zero_residual_shapes}")
    print(f"resonant_unit_mod3_cancels={resonant_unit_mod3_cancels}")
    print(f"resonant_unit_excess_hist={resonant_unit_excess_hist}")
    print(f"terminal_resonant={terminal_resonant}")
    for row in shown:
        print(row)


if __name__ == "__main__":
    main()
