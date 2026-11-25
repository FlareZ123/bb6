"""Regenerate the two long 1LF sweep certificates from explicit families.

The chosen families are fixed mathematical witnesses; the symbolic simulator
only decomposes their epochs. Lean checks every local equation and induction.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "agent31-three-hole-tnf"))
import generate_sweeps as one

CASES = [
    (1327, "1RB1LF_1RC0RB_0RD0LA_1LD1RE_---1RA_1RC1LA",
     1, "R", 1, "0", "00001100000011000000110000001100", "1", 15, 1955, 2992),
    (1605, "1RB1LF_1RC0LB_0RD0RF_1LD1RE_---1RA_0RC1LB",
     873, "L", 1, "0011000001100011001100001111000", "00001111",
     "11110001111", -8, 442, 0),
]

def main():
    parts = ["import SweepPumping", "set_option maxRecDepth 100000",
             "set_option maxHeartbeats 0", "set_option linter.unusedVariables false",
             "namespace BB6.Agent1Raw60LFLong", "open BB6Coverage BB6Coverage.Agent31Pump"]
    original = one.local
    one.local = lambda p, q, l, r, side, block: original(p, q, l, r, side, block, limit=500)
    try:
        for i, code, t, side, q, pre, block, suf, delta, a, b in CASES:
            p = one.parse(code)
            w, v = one.W(pre, block, suf), one.W(pre + block, block, suf)
            st = one.C(q, 0, 0, w if side == "R" else one.W(), w if side == "L" else one.W())
            tg = one.C(q, delta, 0, v if side == "R" else one.W(), v if side == "L" else one.W())
            res = one.pump(p, st, tg, 3000)
            assert res is not None, i
            proof, info = one.generate(i, p, (t, None, st, tg, res))
            assert info == (t, a, b), (i, info)
            parts.append(proof)
            print(i, info)
    finally:
        one.local = original
    parts.append("end BB6.Agent1Raw60LFLong")
    (ROOT / "Raw60LFLong.lean").write_text("\n\n".join(parts) + "\n", encoding="utf-8")

if __name__ == "__main__":
    main()
