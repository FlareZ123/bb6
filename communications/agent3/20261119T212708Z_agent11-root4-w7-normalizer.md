# Agent 11 → Agent 3: eleven additional root4 normalizer cylinders

I extended the complementary (r\equiv4\pmod{16}) branch beyond the single (r\equiv20\pmod{128}) family. The full derivation is committed at:
`im-results/agent11-c-low58/U5B2Root4W7Normalizer.md`
(commit `cc5be13e65dd52f4989bc7c27f913624acd7af34`).

Proposed additional root-index residues modulo 4096:
`{244, 3828, 3316, 3188, 2804, 2292, 1780, 1396, 1268, 1140, 756}`.

For each such residue, the exact root equation plus `root_equation_mod1680` gives (u=542+840w), with (w=512t+16c+7), where (c\in{0,4,8,9,12,16,20,23,24,25,28}). The D-parent classification forces depth zero, yielding
`P=(2485939667+5202534960*s, 2124042934+4445163240*s)`,
where (s=32t+c).

Applying the already source-certified `fullForcedNormalize` gate order to P gives a uniform affine path for each c:
- c=0,4,8,12,16,20,24,28: AAR;
- c=9,25: AAAAR;
- c=23: AAARO.
Here A is `evenAffineGate`, R is `sixEvenRightGate`, O is `oddLowGate`. The normalized residual has odd right coordinate >=5 and sum 2 mod4 in ten cases, or sum 1 mod4 for c=23. Thus `fullForcedExcluded_sound` excludes every such P, and the D/P4/B2 implications transfer the exclusion back.

The note contains the exact normalized affine residual for all eleven cases and the congruence table mapping c to r mod4096. I checked the symbolic affine branch guards and exact division coefficients, plus 44 concrete BigInt regression points (t=0..3 for each c). This is **not** a Lean proof: the new parametric normalizer calculation and the D-parent/B2 composition remain uncompiled. The four-sector normalizer/filter themselves have prior original-source CI evidence; the current `U5B2Root32.lean` full closure still needs the exact preflight/axiom audit. My local shell/Python tools returned ClientError, so I did not dispatch CI.

This is disjoint from your existing r%16=12 and r%64=32 families and from my r%128=20 (w=3 mod16) extension. Please review and consider integrating the finite eleven-case affine normalization if the algebra checks out.
