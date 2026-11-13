# Q/U depth selector and the n=887 U-parent cone

**Status: source integration pending.** The new Lean modules were locally checked with Lean 4.36.0-rc2 against interface stubs matching the existing source theorem signatures. This is not yet an original-source CI result. The manual workflow `.github/workflows/agent7-u-parent-band.yml` has been extended to compile the actual ray, `ResetParent`, `ParentsFast`, and `ClosedCertFast` dependency chains before compiling these modules. Do not describe the result as source-certified until that run passes.

## 1. The Q/U coordinate

For
[
Q_j(n)=8,mathrm{signedZ}(n,j)-9(2^{n+2}+2n+1),
]
the direct affine form is
[
Q_j(n)=28cdot2^n-2n+15-2^{j+4}(2n+3).
]
The n=887 U coordinate in `UParentBandEnvelope` is exactly this Q numerator:
[
U=Q_j(887)=9(2z+5).
]
The affine identity and the exact child coordinate are formalized in `UParentBandBase.lean`.

## 2. All-precision Hensel selector

The modules `QDepthDefs.lean`, `QDepthLift.lean`, `QDepthSelectorBase.lean`, and `QDepthSelector.lean` construct the Q depth residue recursively. For every (n\equiv4,5\pmod6) and every (k,j\in\mathbb N), the selector theorem is
[
3^{k+1}\mid Q_j(n)
\quad\Longleftrightarrow\quad
j\equiv qDepthResidue(n,k)\pmod{2\cdot3^k}.
]
The proof transfers the signed-ray digit lift: the Q lift coefficient is eight times the signed-ray coefficient, hence remains a unit modulo three. The induction proves existence and uniqueness of one depth residue at every precision, not merely a finite search bound.

For n=887, `QDepth887.lean` kernel-checks the exact residues:
| k | Divisibility | Period | Residue |
|---:|---:|---:|---:|
| 0–5 | (3^{k+1}\mid Q) | (2\cdot3^k) | 0 |
| 6 | (3^7\mid Q) | 1458 | 486 |
| 7 | (3^8\mid Q) | 4374 | 3402 |

## 3. Exact first-tier odd U-parent alternatives

The existing source band filter excludes exponents (t=0,1,3,5,6,8,10), and fixes the parent scales for (t=2,4,7,9). If (t\ge5), then
[
U=3^{t+3}d\quad\Longrightarrow\quad3^8\mid Q_j(887).
]
The k=7 selector would force (j\equiv3402\pmod{4374}), impossible for first-tier (6\le j\le870). Thus only (t=2,4) remain:
- (t=2): (k=883), (j\equiv0\pmod{162}), hence (j\in\{162,324,486,648,810\}).
- (t=4): (k=882), (j\equiv486\pmod{1458}), hence (j=486).

This is formalized by `u_odd_parent_exact_n887` in `UParentOddSelector.lean`. The source-shaped even/odd wrapper is retained in `UParentResetFilter.lean`.

## 4. A 31-state closed inverse cone

The five possible first-tier U children are
[
z_0(j)=\frac{56\cdot2^{885}-902-2^{j+3}\cdot1777}{9},
\qquad j\in\{162,324,486,648,810\}.
]
`UParentCone887.lean` takes these five values as roots and computes their depth-10 reverse closure using the exact `parentsFast` implementation. Its kernel-checked finite claims are:
- the closure has exactly 31 states;
- it is closed under all `parentsFast` predecessors;
- the root state 2 is absent.

The source theorem `closedCertFast_excludes` then excludes every state in this cone from `ReachC (2,0)`. In particular, `first_parent_not_root` excludes every exact `ResetParent` predecessor of each of the five roots, and `U_odd_parent_not_root` shows that every first-tier odd U-parent candidate lies among them. This closes the first-tier n=887 U-odd arm, conditional only on the existing source lemmas and pending their integrated CI check.

## Files and verification boundary

- `QDepthDefs.lean`, `QDepthLift.lean`, `QDepthBase.lean`, `QDepthSelectorBase.lean`, `QDepthSelector.lean`, `QDepth887.lean`, `QDepthHensel.lean`: Q selector.
- `UParentBandBase.lean`, `UParentOddSelector.lean`, `UParentResetFilter.lean`, `UParentBand887.lean`: n=887 arithmetic and source-shaped odd/even filter.
- `UParentCone887.lean`: 31-state reverse cone and root-exclusion corollaries.
- `.github/workflows/agent7-u-parent-band.yml`: manual original-source compile chain, including the Q selector and cone.

Local compilation used exact interface stubs for the imported signed-ray lift lemmas, U-band filter, `parentsFast_iff`, and `closedCertFast_excludes`. The computational `parentsFast` definitions in the local cone harness were copied from the checked-in implementation. The workflow now checks the actual imported source proofs and the final theorem dependencies. The result is intermediate research, not a BB(6) solution or a complete closure of the n=887 machine branch; the T/z1 arm and other branches remain separate obligations.
