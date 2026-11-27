#!/usr/bin/env python3
"""A reproducible residue-tree pilot for the original Cryptid D marker packets.

Analyzes prepared F0 packets P(8*k+5,0,2*Q+6;01010111). The literal
original 6-state E and B source-return laws (PacketSource.lean) imply
these affine transformations *while the corresponding guard holds*:
  E: a -> (8*a-5)//3, q -> q+2, p -> p-3 (a%3=1,p>=3);
  B: a -> (8*a+14)//3, q -> q-1, p unchanged (a%3=2,q>0).
An A packet (a%3=0) or a B packet with q=0 has an independently
kernel-verified arbitrary-marker regular-section return (MarkerOneSource).

This tool only detects *symbolic all-Q algebraic routes*. It is NOT a
formal certificate, and it does not classify terminals of type
'E with low guaranteed p' or prefixes whose residue depends on the
free high-precision index. Use Lean to certify any chosen cylinder.

Usage:
  python3 marker_residue_route.py --power 7 --show-open
"""
import argparse
from collections import Counter

def route(power: int, residue: int):
    mod = 3**power
    a_coeff, a_const = 8*mod, 8*residue+5
    q, p_const = 0, 6  # a=coeff*v+const, p=2*Q+p_const
    transitions = []
    while True:
        if a_coeff % 3:
            return "needs_deeper_residue", "".join(transitions), q, p_const
        rem = a_const % 3
        if rem == 0:
            return "A-terminal", "".join(transitions), q, p_const
        if rem == 2:
            if q == 0:
                return "B0-terminal", "".join(transitions), q, p_const
            a_coeff = 8*a_coeff // 3
            a_const = (8*a_const+14)//3
            q -= 1
            transitions.append("B")
        else:
            if p_const < 3:
                return "E-low-p", "".join(transitions), q, p_const
            a_coeff = 8*a_coeff // 3
            a_const = (8*a_const-5)//3
            q += 2
            p_const -= 3
            transitions.append("E")

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--power", type=int, default=5)
    ap.add_argument("--show-open", action="store_true")
    ap.add_argument("--show-all", action="store_true")
    args = ap.parse_args()
    if not 0 <= args.power <= 10:
        ap.error("--power must lie between 0 and 10")
    m = 3**args.power
    tally = Counter()
    open_cases = []
    closed = []
    for r in range(m):
        outcome, path, q, pconst = route(args.power,r)
        tally[outcome] += 1
        row = (r,outcome,path,q,pconst)
        if outcome in ("A-terminal","B0-terminal"):
            closed.append(row)
        else:
            open_cases.append(row)
    print(f"modulus={m} all_Q_source_terminal={len(closed)}/{m} "
          f"fraction={len(closed)/m:.8f} tally={dict(tally)}")
    if args.show_open or args.show_all:
        print("residue,status,E_B_path,last_q,min_p_intercept")
        for row in (open_cases if args.show_open else sorted(open_cases+closed)):
            print(",".join(map(str,row)))

if __name__=="__main__":
    main()
