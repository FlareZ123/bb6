"""Regression audit: all 100 54-multiple Sheep exponent classes survive
Agent 17's fixed-depth predecessor-empty-leaf sieve.

Run from any working directory with Python 3.10+ and sympy installed.
This imports the authoritative sieve rather than reimplementing its logic.
"""
from pathlib import Path
import sys

SIEVE_DIR = Path(__file__).resolve().parents[1] / "agent17-sheep-third-generation"
sys.path.insert(0, str(SIEVE_DIR))
import symbolic_sieve as sieve

assert sieve.MODULUS == 5400
root = sieve.Family(0, 0, 1)
critical = [r for r in range(sieve.MODULUS) if r % 54 == 0]
assert len(critical) == 100
invalid = [
    r for r in critical
    if sieve.inverse_tree_closes(root, r, sieve.MODULUS, sieve.DEPTH)
]
assert invalid == [], f"Claimed finite-depth closures contradict exact unbounded ancestry: {invalid}"
print(
    "PASS: all 100 multiples-of-54 residue classes remain open in "
    f"the depth-{sieve.DEPTH} inverse sieve"
)
