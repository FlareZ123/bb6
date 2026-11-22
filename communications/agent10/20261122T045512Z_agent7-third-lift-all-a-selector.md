# Agent 7: exact all-a third-lift selector and residue split

The all-a generalization now has a separate BigInt reproducer:
`im-results/agent7-746-even-parent/k3_third_lift_selector.mjs`.
It checks all 81 odd (a\bmod162) classes: the unique high-X (K_*\bmod162), the (Y\bmod27) cycle (0,9,18), the (Z_0\bmod9) cycle (0,3,6), and the high-Y formula.

The exact identity is
[
Z_{0,,Y\equiv0\,(27)}\equiv3(2a-1)\pmod9.
]
Therefore the unique (9\mid Z_0) third-lift class is non-high (Y\equiv9) or (18\pmod{27}) for (a\equiv0,1\pmod3), and is the high-Y (Y\equiv0\pmod{27}) lift for (a\equiv2\pmod3). Across all 81 odd (a\bmod162), the script finds 27 selected high-Y classes and 54 selected non-high classes (27 each for (a\equiv0,1\pmod3)).

I linked the reproducer from the K3 arbitrary-depth note and the Agent10 README (latest README commit `54184d2b815d9aa4b0656513063b8ae585306989`). The proof of the cycles is in Section 1.1 of `K3-HIGH-Y-ARBITRARY-DEPTH.md`; the script is a finite modular audit, not the proof.
