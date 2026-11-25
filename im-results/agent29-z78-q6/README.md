# Machine C low-stop exclusion: z = 846 (mod 2048)

**Status:** Lean source proof drafted. Run 45686539507 ended with runner shutdown (exit 143) during target compilation, without a Lean diagnostic. Rerun 45690298092 is still in the kernel-verification step. Do not count this as accepted until a run succeeds.

## Result being proved

For the Machine C low-stop family
\[
m=512z+67,\qquad k+3m+4=2^{2m+3},
\]
the blank section cannot reach the stopping state whenever
\[
z\equiv846\pmod{2048}.
\]
Equivalently, the corresponding stop-parameter residue is
\[
m\equiv433219\pmod{1048576}.
\]

The proof is an all-time source-inverse argument. It is not a bounded simulation or a finite search over bounce depth.

## Inverse chain

Write \(z=2048t+846\). The stopping equation gives
\[
k=256u+51,\qquad u+6z+1=2^{1024z+129}.
\]
Since the right-hand side is divisible by \(8192\), the parity of \(t\) forces
\[
u\equiv3115\pmod{8192}\quad(t\text{ even}),\qquad
u\equiv7211\pmod{8192}\quad(t\text{ odd}).
\]

The exact even-\(z\) source inverse reduces the low-ray target to
\[
P=\left(173u+24,\frac{339u+47}{2}\right).
\]
The specialized source section inverse gives exactly two predecessor types:

1. the direct predecessor \((X+Y-2,(Y-2)/2)\);
2. the depth-one high predecessor \((a,k)\), satisfying
   \[
   X+Y+1=4(a+3),\qquad 2k+a+10=X+2Y.
   \]

The direct branch has a fixed source-certified chain: odd/odd low-value inverse, then the six-even-right inverse, ending in an even/odd image with sum \(1\pmod4\), forbidden by the original blank-section image invariant.

For the high branch, the equations force
\[
8a=685u+73,\qquad16k=3411u+415.
\]
Its odd/odd low-value predecessor is
\[
D=\left(\frac{4781u+497}{32},\frac{11603u+1231}{64}\right),
\]
with even/odd coordinates and
\[
D_1+D_2+1=\frac{21165u+2289}{64}\equiv32\pmod{64}.
\]
This mass is at least 64 and is not a power of two. The full even/odd non-power parent theorem therefore applies to *every* source parent of \(D\), with no depth cutoff. Its equations force an even bounce depth \(n\); parity of the cost equation makes the left parent coordinate odd, so \(2^{n+2}\) divides the mass. The residue \(32\pmod{64}\) then leaves only \(n=0\) or \(n=2\).

- At \(n=0\), the parent is odd/odd with sum \(2\pmod4\), forbidden.
- At \(n=2\), the parent is odd/even. For \(u\equiv3115\pmod{8192}\), one six-even-right inverse followed by an odd/odd low-value inverse reaches an even/odd sum-one image. For \(u\equiv7211\pmod{8192}\), one six-even-right inverse reaches an odd/odd sum-two image. Both are forbidden.

Thus both direct and depth-one high source parents are impossible, and \(P\) is unreachable.

## Global low-stop integration

Z78Q6Source.lean defines lowAllowedSource1585 by adding the disjoint condition
\[
m\not\equiv433219\pmod{1048576}
\]
to the accepted 1583-class low-stop criterion. Its theorem blank_halts_iff_six_low1585 preserves the previous high-stop branch and removes exactly this additional low-stop cylinder.

The new residue is disjoint from the explicitly listed modular exclusions in the 1583-class chain (for example, it has \(m\equiv40003\pmod{65536}\), not \(7235\)). It contributes two z-classes modulo 4096. One nonredundancy check remains: the old predicate also contains the sixForcedExcluded normalizer. The new class increases the effective count to 1585 only if that normalizer is shown to stop at P rather than already excluding this class; the fixed gate residues strongly indicate that it does stop there, but this is not yet a formal lemma in this file.

## Source and verification

- Lean module: Z78Q6Source.lean
- CI target: sourceLowZ78Q6 in .github/workflows/agent13-m16-high-family-interface.yml
- Current CI run: [45690298092](https://github.com/FlareZ123/bb6/actions/runs/45690298092) (rerun after infrastructure shutdown in [45686539507](https://github.com/FlareZ123/bb6/actions/runs/45686539507))
- The proof imports the exact section-inverse, even-right, odd/odd low-value, and all-depth even/odd parent theorems. No native_decide, simulator trust, or finite bounce-depth bound is used.
