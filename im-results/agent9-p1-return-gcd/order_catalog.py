#!/usr/bin/env python3
"""Enumerate exact signed orders that feed the P1 K+B forbidden-factor lemma.

The theorem requires h odd, 2^K == +/-1 mod h, B s.t.
h*(7*2^n+K+1) < 2^B, and forbids equal/complement factors
of length L=n+3+K+B at shift 2^r*h for an original Trace.
No numerical row by itself proves reachability is impossible.

Usage: python order_catalog.py --n 14 --max-h 10000 --top 30
"""
from __future__ import annotations

import argparse
import csv
import math
import sys


def orders(h: int):
    """First positive K for 2^K == +/-1 mod odd h; elementary exact loop."""
    if h < 3 or h % 2 == 0:
        raise ValueError("odd h>=3 required")
    r = 1
    kminus = None
    for k in range(1, h + 1):
        r = (r * 2) % h
        if r == h - 1 and kminus is None:
            kminus = k
        if r == 1:
            return k, kminus
    raise ArithmeticError(f"No multiplicative order below h for {h}")


def window(n: int, h: int, k: int):
    total = 7 << n
    b = (h * (total + k + 1)).bit_length()
    assert h * (total + k + 1) < 1 << b
    return b, n + 3 + k + b


def rows(n: int, max_h: int):
    for h in range(3, max_h + 1, 2):
        plus, minus = orders(h)
        for sign, k in (("cyclic", plus), ("negacyclic", minus)):
            if k is None:
                continue
            b, length = window(n, h, k)
            old_length = 2 * n + 2 * k + 7
            yield {
                "h": h, "sign": sign, "K": k, "gcd_hK": math.gcd(h, k),
                "B": b, "length": length,
                "previous_2K_length": old_length,
                "saved_bits": old_length - length,
                "divisor_check": int((pow(2, k, h) - (1 if sign == "cyclic" else h - 1)) % h == 0),
            }


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, default=14)
    p.add_argument("--max-h", type=int, default=10000)
    p.add_argument("--top", type=int, default=30)
    p.add_argument("--min-gain", type=int, default=0)
    p.add_argument("--only-noncoprime", action="store_true")
    p.add_argument("--csv", action="store_true")
    args = p.parse_args()
    if args.n < 14 or args.n % 2 != 0 or args.max_h < 3:
        p.error("source theorem requires even n>=14, max-h>=3")
    data = [r for r in rows(args.n, args.max_h)
            if r["saved_bits"] >= args.min_gain and
               (not args.only_noncoprime or r["gcd_hK"] > 1)]
    data.sort(key=lambda r: (-r["saved_bits"], r["length"], r["h"]))
    fields = ["h", "sign", "K", "gcd_hK", "B", "length",
              "previous_2K_length", "saved_bits", "divisor_check"]
    if args.csv:
        out = csv.DictWriter(sys.stdout, fieldnames=fields)
        out.writeheader()
        out.writerows(data[:args.top])
    else:
        print(f"n={args.n}, h<= {args.max_h}, rows={len(data)}; "
              "all bounds conditional on a genuine original Trace")
        print(" ".join(f"{f:>18}" for f in fields))
        for row in data[:args.top]:
            print(" ".join(f"{str(row[f]):>18}" for f in fields))


if __name__ == "__main__":
    main()
