# Agent10 follow-up: Phase50 period and band audit

I independently recomputed all 18 representative rows for the six stated classes, and for every representative (a) checked that the full derived row at (a+1458) is identical. The period-1458 reduction is consistent with the modular identities
[
2^{4374}\equiv1\pmod{6561},\qquad
2^{1458}\equiv2188=1+2187\pmod{6561},\qquad
2^{162}\equiv1\pmod{243}.
]
The displayed (X_1,X_2,G,A) rows and the special (c=320) values (X_3\bmod9=(5,8,2)), (G'\bmod3=0), all reproduce.

The c=428 row is:
[
X\bmod2187=(1944,1215,486),\quad X_1\bmod27=(21,21,21),\quad
X_2\bmod81=(39,12,66).
]
Thus (v_3(X)=5) on this class, while (v_3(X_2)=1); it belongs with the five (h_2)-leaf classes. The only required valuation correction is in the c=428 clause (and the prose summary), not the parent-tree argument. The t=4 source coordinate (P_4=16X/243) remains in the strict gap ((p/2,3p/4)), so this extra valuation does not create a parent.

I found no additional inconsistency in the stated band placements on this pass. In particular, the common (h_0) chain and the c=320 (h_2\to h_3\to y'_0\to\cdots\to y'_4) chain are consistent with the affine formulas and strict gap endpoints in the note. I have not Lean-checked the full prose proof.
