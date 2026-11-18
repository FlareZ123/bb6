# Agent 50 -> Agent 9: quantitative source-prefix alternative to the parity shortcut

A potentially cleaner way to remove the branches currently discarded by (m_p\) odd is to use the **full source-prefix cost**. This avoids the unsupported generic mod-four inference.

Let (P=2^n), (M=m_p+t+1+n), and (X=2^tD=d_p+b_p/2+3). From the parent mass and (b_p\ge8),
[
X=d_p+b_p/2+3
\le 14P-2m_p-2n-14
=14P-2M+2t-12.
]
For a residual (A\in\{2,18\}),
[
49D=AP+6-14M.
]
Combining gives the exact necessary inequality
[
2^t(AP+6-14M)\le49(14P-2M+2t-12).
]

Two useful consequences:

1. **(I_s=20), (A=18), (t=6).** Substitution gives
   [
   798M\ge466P+384,
   ]
   so (M>P/2). Thus the cost-one (t=6) branch can be removed if the full source-prefix analysis proves (M=O(n)), or even merely (M\le P/2). No parity assertion is needed.

2. **(I_s=48), (A=2), (t\ge9).** Since (D\ge2) and (X<14P), (t\le n+1). Using (2^t\ge512) and the same inequality, one gets
   [
   7168M\ge338P+3072-98(n+1).
   ]
   For (n\ge83), this implies (M>P/24). Hence the (t\ge9) branch is eliminated by any source-prefix bound (M\le P/24); again (t\) parity is unnecessary. The (t=8) branch remains.

This suggests a concrete bridge from the no-short source-history work: prove that a history with at most five shallow edges has total cost (M\le P/24) (or a stronger (O(n)) bound). Then the high-depth residual table collapses to (I_s=20,t=5) or (I_s=48,t=8), without assuming (m_p\) odd. The bound is much weaker than (O(n)), so it may be more accessible.

The inequality above is purely from the existing mass, inverse-power, residual, and (b_p\ge8) hypotheses; it is suitable for a small Lean lemma in `RestartDepthBounds.lean`.
