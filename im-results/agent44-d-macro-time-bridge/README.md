# First-ten A_step2 / DRegular timed correspondence

**Status:** a new exact arithmetic bridge for the first ten external A-macro calls. It strengthens the existing endpoint-only first-ten comparison with raw-step accounting. It is not yet a Lean theorem identifying the two machine semantics, does not cover the later noncanonical suffixes, and does not connect the halting cylinder to the true blank root.

## Scope and notation

The external proof is pinned at `int-y1/proofs` commit `1929f57df4dd7afcc11c3f458e20526fd1f991e0`, file `BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean`. Its first ten `A_step2` arguments are

```
13, 21, 5, 5, 21, 5, 17, 21, 5, 27.
```

The corresponding repository arithmetic states are the first ten states in [Agent 4's macro trace](../agent4-cryptid-macro-replay/macro_trace.json), and the endpoint-only all-`k` theorem is [First10AffineBridge.lean](../agent4-cryptid-macro-replay/First10AffineBridge.lean). The repository's original-source transport dependency is [DRegularSourceShift.lean](../agent2-cryptid-continuity/DRegularSourceShift.lean); its universal source contract is imported from the pinned original `ERemaining` source.

For a current external A-section input (a), write (k=lfloor a/3floor) on the B branch (a\equiv2\pmod3), and (k=lfloor a/3\rfloor-1) on the A/E branches (a\equiv0,1\pmod3). Let (m) be the literal argument of `A_step2 m), and let (K) be the number of alternating pairs consumed by its `step_01C_C11` sweep.

## Exact raw-step decomposition

The external macro has four consecutive pieces:

1. `step_An_1101`, whose exact cost is
   - B: (12k^2+41k+31);
   - A: (12k^2+41k+32);
   - E: (12k^2+41k+33).
2. The literal `iterate m step`: exactly (m) raw steps.
3. `step_01C_C11` on (K) alternating pairs: exactly (2K) raw steps, since its repeated one-pair body is `execute 2`.
4. The two final `step` calls: exactly two raw steps.

The quadratic prefix costs follow directly from the external proof's repeat lemma. In one `step_1101B111_1101B` repetition, if the incoming alternating-pair count is (j), the C-sweep sees (j+1) pairs and costs (4(j+1)); the B-sweep sees (j+4) pairs and costs (2(j+4)). Including the fixed (1+3+18+1) transitions gives

[
1+3+4(j+1)+18+1+2(j+4)=6j+35.
]

The (k) repetitions use (j=3,7,\ldots,4k-1), so their total is

[
\sum_{i=0}^{k-1}(6(3+4i)+35)=12k^2+41k.
]

Adding the initial eight transitions, the 23-step branch prefix, and the branch-specific final (0,1,2) transitions gives the three costs above. In particular, the (+4k) term is essential: omitting the extra pair in the C-sweep would undercount the prefix.

For each of the first ten calls, the symbolic alternating block passed to `step_01C_C11` has (K=4k+1). The independently reconstructed (k=0) trace confirms this in all ten cases. Consequently the complete `A_step2` raw duration is

[
P_{\mathrm{branch}}(k)+m+2(4k+1)+2.
]

## First-ten equality with DRegular duration

Substitution gives the following exact identities with the corresponding source-model `DRegular.duration` row:

| Call | Branch | Input ((q,b)) | `A_step2` (m) | (K-4k) | Total raw duration |
|---:|:---:|:---:|---:|---:|---|
| 1 | E | (0,0) | 13 | 1 | (12k^2+49k+50) |
| 2 | E | (1,5) | 21 | 1 | (12k^2+49k+58) |
| 3 | B | (3,2) | 5 | 1 | (12k^2+49k+40) |
| 4 | B | (2,2) | 5 | 1 | (12k^2+49k+40) |
| 5 | E | (1,2) | 21 | 1 | (12k^2+49k+58) |
| 6 | B | (2,0) | 5 | 1 | (12k^2+49k+40) |
| 7 | E | (1,0) | 17 | 1 | (12k^2+49k+54) |
| 8 | E | (1,7) | 21 | 1 | (12k^2+49k+58) |
| 9 | B | (3,4) | 5 | 1 | (12k^2+49k+40) |
| 10 | E | (2,4) | 27 | 1 | (12k^2+49k+64) |

For E with (q=0), the constant is (m+37=50). For E with (q>0,b=0), the external argument is (m=4q+13), giving (m+37=50+4q). For E with (q>0,b\ge2) on this path, (m=6q+15), giving (m+37=52+6q). For B on this path, (m=5), giving (m+35=40). These are exactly the corresponding DRegular duration formulas. The table is a BigInt arithmetic audit of the first ten concrete trace states at outer cylinder parameter zero. The displayed polynomial duration identities are conditional on the symbolic (K=4k_i+1) extraction; that is the remaining small proof obligation before calling the first-ten timed bridge formal.

The exact suffix updates and endpoint parameters remain those in Agent 4's trace and `First10AffineBridge`. The first ten calls end at (L(D_1,4,1)), with
[
D_1=35925965576050291197954676646168812866911688985763244505.
]

## Exact scope boundary

- **Branch labels:** external E/B/A are the (a\bmod3=1,2,0) branches respectively. The first ten calls use E and B only.
- **Raw duration:** the formula above establishes the first-ten timed equality with the corresponding DRegular rows. It is not merely an endpoint comparison.
- **Suffix:** all ten observed suffixes remain in the DRegular canonical language. The external macro proof is suffix-parametric, but the repository SourceContract being used here is only for canonical DRegular states; no arbitrary-suffix source theorem follows from it.
- **Padding/observation:** repository source transport is stated with physical `ObsEq` and `source_congr`, not literal equality of finite list representations. This is the correct way to handle omitted/trailing blank cells.
- **First exceptional exit:** call 11 starts from the canonical E state ((q,b)=(4,1)), where `DRegular.next` is undefined. The external `A_step2 35` nevertheless continues and produces a noncanonical suffix. This is a regular-language exit, **not** a machine halt. The later E/E plus P2 source reentry is a distinct longer source segment, not the next external macro.
- **Still missing:** a formal transition/conjugacy theorem between the external `TM62` configuration semantics and repository `CryptidBoundary` semantics, plus source-certified arbitrary-suffix/reentry handling for calls 11–107. The external halting-cylinder theorem does not establish that the genuine blank start (A(9,[])) reaches its cylinder.

## Next acceptance step

Formalize the implicit (K=4k+1) parameter for the first ten symbolic macros and prove the external-to-repository one-step conjugacy on the canonical section. Then integrate the existing DRegularSourceShift transport. Keep the call-11 E ((4,1)) exit explicit and require a separate arbitrary-suffix source certificate before composing the remaining 97 macros.
