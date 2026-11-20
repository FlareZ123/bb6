# Seven-step 3-adic shadow of the D-start halting cylinder

**Status:** exact BigInt/model result with a short source-proof candidate. This is not a BB(6) solution, a halting proof, or a global exclusion theorem. Keep it in im-results.

## Result

For the D machine 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---, the external Lean proof at int-y1/proofs commit 1929f57df4dd7afcc11c3f458e20526fd1f991e0 proves that every

\[
A(3^{108}k+C,[])
\]

halts, where

\[
C=1975700577069254261393123959451562008800234946348086.
\]

Let L(a,q,b) be the repository's DRegular section with suffix (01)^q 1^b. Exact BigInt replay of the repository DRegular table from the blank-derived seed L(9,0,0) finds that its state after 2,640 regular-section transitions is

\[
L(a_{2640},0,0),\qquad
a_{2640}=C+3^7p,
\]

with

\[
p\equiv1\pmod3,\qquad p\equiv1\pmod2.
\]

The computed a_2640 has 3,740 bits and p has 3,729 bits. The 8,394th-return exit parameter has 11,882 bits. The relation is exact, not a floating-point or bounded-integer approximation.

The existing theorem DRegularShift.run_shift then gives, for each \(0\le j\le7\),

\[
a^{\rm root}_{2640+j}-a^{\rm ext}_{j}
   =3^{7-j}8^j p,
\]

with exactly the same (q,b) suffix state on both runs. The first seven branch labels in the external replay are

\[
\boxed{\mathrm{EEBBEBE}}.
\]

At the eighth input checkpoint (j=7), the external path has unary parameter 1 mod 3, while the blank-derived lift has parameter 0 mod 3. Thus the external next branch is E, whereas the lifted root's DRegular branch is A. Their next suffix states differ:

- external: (q,b)=(3,4);
- blank-derived lift: (q,b)=(1,5).

This is a seven-step 3-adic shadow, not entry into the 108-digit halting cylinder. In particular, p is not divisible by 3, so the lifted checkpoint after seven transitions is not in the residual cylinder requiring a further factor 3^101.

## Checkpoint-family screen on the first regular segment

The first ten external A-step2 calls have DRegular suffix checkpoints

\[
(0,0),(1,5),(3,2),(2,2),(1,2),(2,0),(1,0),(1,7),(3,4),(2,4),(4,1).
\]

The independent replay in Agent 4's macro trace records dregular_next_matches=true for the first ten calls. The associated checkpoint family after j calls has the form

\[
L(c_j+3^{108-j}8^j k,q_j,b_j).
\]

The script halting-cylinder-shadow.mjs scans the 8,395 DRegular section states at indices 0,...,8394, checking all eleven checkpoint families with exact BigInt arithmetic. It finds no endpoint hit. The best 3-adic valuations among states with the required suffix pairs are:

| Checkpoint j | Suffix (q_j,b_j) | Sampled states | Required v3 | Maximum observed v3 |
|---:|---:|---:|---:|---:|
| 0 | (0,0) | 5,157 | 108 | 7 |
| 1 | (1,5) | 1,744 | 107 | 6 |
| 2 | (3,2) | 578 | 106 | 5 |
| 3 | (2,2) | 193 | 105 | 4 |
| 4 | (1,2) | 62 | 104 | 3 |
| 5 | (2,0) | 69 | 103 | 2 |
| 6 | (1,0) | 22 | 102 | 1 |
| 7 | (1,7) | 4 | 101 | 0 |
| 8 | (3,4) | 1 | 100 | 0 |
| 9 | (2,4) | 0 | 99 | — |
| 10 | (4,1) | 0 | 98 | — |

The consecutive best matches at indices 2,640–2,647 are precisely the seven-step shadow above.

**Boundary of this screen:** it checks DRegular section endpoints, not every primitive configuration inside each source macro. Since a general first-return/minimality theorem identifying every DRegular.next with the external A_step2 macro is not established, this finite endpoint sieve does not exclude intermediate visits to an external checkpoint. It is a search discriminator, not a non-entry theorem.

## Source-proof route

The repository already has the ingredients for a compact kernel certificate:

- BlankRegular8394.blank8394 connects the authentic blank start to the DRegular seed L(9,0,0).
- ERemaining.source_contract and DRegular.transport_obs lift any successful finite DRegular run to the original six-state source.
- DRegularShift.run_shift proves the exact 3^k/8^k synchronization.
- ARegular3AdicBridge.synchronized_source packages the source-level lift in A-section notation.

The candidate HaltingCylinderShadow.lean formalizes the 2,640-step root state, its exact 3^7-lift relation, the seven-step synchronized source run, and the eighth-branch divergence. It is **not yet locally preflighted or CI-audited**. No CI was dispatched as a substitute for the required local Lean check.

## Research consequence

The useful new target is not another isolated residue check. Extend the eleven-checkpoint family screen to subsequent authentic root reentries, and search for a later section whose unary parameter has the full required 3-adic precision at one of the eleven suffix states. In parallel, settle the finite source correspondence between the first external A-step2 checkpoints and the DRegular endpoints; do not generalize it beyond the cases actually proved.

No conclusion about the exact BB(6) value, global D halting, or global D nonhalting follows.
