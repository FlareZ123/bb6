# U5 second-cone zero-left sieve

**Status:** exact source-predecessor reduction plus finite M32 quotient computation; not yet assembled into a Lean theorem. This advances the exceptional (a\equiv37\pmod{64}) Side branch beyond the reduction in `U5SecondConeForcedTail.md`.

## Starting family

The exceptional Side source is
[
Z_0=(0,K_0,C_0)
=(0,33+32u+16v, 33+32v),\qquad v\ge u.
]
All parameters are natural. In particular, (K_0\ge33), (C_0\ge33), and (K_0\equiv1\pmod4).

Use the exact source predecessor lemmas in `im-results/agent21-c-source-bridge/CBack.lean`:
- `reached_high_pred`;
- `reached_hub_prev`;
- `reached_one_high_or_reset`;
- `reached_high_kzero_prev`;
- `reached_zero_hub).

Use Agent 48's `reached_middle_zero_mod4` in `im-results/agent48-c-middle-zero/KZeroMod4.lean`, which says every reachable ((a,0,c)) has (a\equiv1\pmod4).

## Forced source reduction

Assume (Z_0) is reachable.

1. Apply `reached_high_pred` (K_0-2) times, then `reached_hub_prev), to obtain
   [
   (K_0-1,1,C_0+K_0-1)\in\mathrm{Reach}.
   ]
   The `reached_one_high_or_reset` high branch would give ((K_0,0,C_0+K_0)). By `reached_high_kzero_prev), this implies a second zero-left state with middle
   [
   K_1=(K_0-3)/2=15+16u+8v\equiv3\pmod4
   ]
   and even right counter (C_0+K_0). Repeating the high-predecessor/hub/one chain from that state forces a middle-zero state with left coordinate (K_1\equiv3\pmod4), contradicting Agent 48. Hence the high branch is impossible, and the reset branch forces
   [
   R_1=(K_0+1,L_1,0),\qquad L_1=(C_0+K_0-2)/2=32+16u+24v.
   ]

2. Apply `reached_zero_hub`, `reached_hub_prev), and `reached_one_high_or_reset` to (R_1). The high branch gives a middle-zero state with left coordinate (K_0+L_1-2\equiv3\pmod4), so it is impossible. Thus
   [
   R_2=(K_0+L_1-1,L_2,0),\qquad L_2=(L_1-2)/2=15+8u+12v.
   ]

3. Apply `reached_zero_hub` to (R_2), obtaining a hub
   [
   H=(A_3,2,L_2-2),\qquad A_3=K_0+L_1+L_2-6\equiv2\pmod4.
   ]
   Its only possible immediate source classes in the exact CLine transition are:
   - the high source ((A_3+1,1,L_2-1));
   - the zero-left even source ((0,(A_3-2)/2,L_2+1)).

   The high source is impossible: `reached_one_high_or_reset` has even reset parameter (L_2-1), so it forces the high branch and then a middle-zero state with left coordinate (A_3+2\equiv0\pmod4), contradicting Agent 48. Therefore the zero-left even source is forced:
   [
   Z_3=(0,K_3,C_3),
   ]
   where
   [
   K_3=(A_3-2)/2=36+28u+26v,qquad
   C_3=L_2+1=16+8u+12v.
   ]

Thus
[
Z_0\in\mathrm{Reach}\quad\Longrightarrow\quad Z_3\in\mathrm{Reach}.
]

## M32 quotient sieve

For the M32 quotient with (q(x)=x) for (x<8), and (q(x)=8+(x-8)\bmod32) otherwise, the new state has (K_3\ge36,C_3\ge16). Put (L=2u+3v). Then
[
K_3\equiv4-2L\pmod{32},\qquad
C_3\equiv16+4L\pmod{32}.
]

Reproducing the finite M32 BFS from `tools/agent43_c32_certificate.py` gives exactly three seen cells among these parameterized cells:
[
egin{array}{c|c}
L\pmod{16}&(q(K_3),q(C_3),0)\\
6&(24,8,0)\\
10&(16,24,0)\\
14&(8,8,0)
end{array}
]
All other (L\pmod{16}) values map to M32-unseen cells. The existing `CCert.original_m32_cell_unreachable` bridge should turn each such unseen cell into source nonreachability; the three seen-cell checks and the 13 absent residue cases still need to be exposed in a small Lean module and compiled.

**Consequence once those finite checks are Lean-compiled:** reachability of the exceptional Side source (Z_0) requires
[
2u+3v\equiv6,10,14\pmod{16}.
]
This removes (13/16) of the parameter residue classes in this Side branch. It does not close the three surviving classes or the separate q=2 parent family.

## Reproducibility and next step

- Source predecessor lemmas: `im-results/agent21-c-source-bridge/CBack.lean`.
- Middle-zero invariant: `im-results/agent48-c-middle-zero/KZeroMod4.lean`.
- Finite quotient transition and certificate generator: `tools/agent43_c32_certificate.py`, `im-results/agent43-c-quotient-kernel/M32HighAll.lean`.
- Add a Lean lemma proving the three seen cells and `¬ seen` for the other 13 (L\pmod{16}) residues, then compose with the source-predecessor reduction above.
