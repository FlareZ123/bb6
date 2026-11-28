# Cryptids #429: finite-depth closure of four infinite signed inverse families

**Mathematical claim (Lean kernel checked):** Four full congruence cylinders of the signed inverse system terminate after uniformly bounded compressed length. Unlike finite traces or fixed-depth 2-adic sampling, the arguments universally quantify the natural family parameter and *all* admissible F/EF/SF branches. No Bad-filter hypothesis is used. This does **not yet prove original-machine blank-root exclusions**, because the established source signed-lift/precision bridge must be instantiated at the relevant exponentially large true parameters. BB(6) remains unknown.

## Source-compatible arithmetic model

The compressed signed inverse maps are F: (u,d)↦(u/2,d+3u+3) for even u, EF: (u,d)↦(u+(d+8)/8,d/4+4) for odd u and d divisible by eight, and SF: (u,d)↦(u+(d+20)/8,d/4−1) for even u and d≡4 (mod 8). The 3-branch `Step` in [Branch1315Finite.lean](Branch1315Finite.lean) encodes exactly these guarded actions as linear integer equations, with *no* source-derived Bad exclusions. In particular any path in the actual signed inverse filter is a Step-path.

Agent22's exact source-accepted branch arithmetic gives initial coordinates (48k+24,96k+66) for the 13-family and (48k+39,96k+96) for the 15-family (see [Branch13_15.lean](../agent22-429-signed-drift/Branch13_15.lean), CI 45683408657).

| Family | Universal k restriction | Max legal compressed transitions | Blocking theorem |
| --- | --- | ---: | --- |
| 13 | k≡0 (mod 4) | 3 | `branch13_mod4_zero_no_four` |
| 13 | k≡1 (mod 4) | 4 | `branch13_mod4_one_no_five` |
| 15 | k≡0 (mod 4) | 3 | `branch15_mod4_zero_no_four` |
| 15 | k≡1 (mod 8) | 5 | `branch15_mod8_one_no_six` |

The claims prohibit any chain of respectively 4, 5, 4, or 6 algebraically legal edges from the genuine parameterized initial signed state. The formal proof uses linear equations for each transition and Presburger decision (`omega`); the original inverse model's Bad leaves can only shorten a path.

For the 13 family with k≡0 mod4, the first two steps are F,F, then F or SF; each next state has odd u and d nonzero modulo eight. For the 15 family with k≡1 mod8, the first step is EF, followed by F or SF; the SF endpoint is terminal and the F branch terminates after four further F actions. These short recurrences provide human-checkable independent proofs of two rows.

## Exact research boundary

The genuine rooted last-reset equation in Agent33/18's programme is 4u+3n+15=3·2^(n+2), n≥18. It forces the 13 family to n=63+128k and the 15 family to n=103+128k. To turn a signed algebraic closure into a theorem excluding a genuine blank-root last-reset family, use the existing authenticated inverse source/BAD bridge and the finite-precision lift at the exact source scale; prove its offset and positivity inequalities for these parameter subfamilies. Other k residue classes remain open, including many algebraically possible (not necessarily genuinely reachable) paths.

**Proof evidence:** [Branch1315Finite.lean](Branch1315Finite.lean) compiles successfully in [manual pinned Lean 4.36.0-rc2 run 46097084000](https://github.com/FlareZ123/bb6/actions/runs/46097084000); every theorem reports axioms only `[propext, Quot.sound]`. This certifies the four arbitrary-k algebraic inverse-tree theorems, but not the original-machine reachability transport. No global Canonical40 count is changed. 

## Stronger original-root direct route (CI pending)

Two further modules target the genuine all-time blank-start source rather than the signed approximation. [BB429RootShortArithmetic.lean](BB429RootShortArithmetic.lean) encodes the exact positive-state F/S/E inverse equations and three already-source-certified root gates: positive even states must have second coordinate 2 modulo 8, 7-mod-8 first coordinates cannot coexist with 7-mod-8 second coordinates, and 1-mod-8 first coordinates cannot coexist with 3-mod-4 second coordinates. It proposes finite-chain contradictions, uniformly for all natural t, for:

- 13-family target (128t+77,256t+151), no 4-step rooted predecessor chain;
- 13-family target (128t+109,256t+215), no 4-step rooted predecessor chain;
- 15-family target (128t+47,256t+91), no 5-step rooted predecessor chain.

[BB429RootShortSource.lean](BB429RootShortSource.lean) imports the authentic `BB429NewResidue.odd_back/even_back`, `BB429RootEven8`, `BB429RootMod16`, and original `reach_allowed`; it connects every reachable predecessor to the exact arithmetic constraints and attempts to conclude no genuine `Reach` when t≥1. This would yield whole original-source forbidden last-reset q-cylinders q≡2 or3 (mod4) in the 13-family and q≡1 (mod4) in the 15-family, for q large enough. **Do not claim these original-root conclusions accepted until [focused manual run 46097369705](https://github.com/FlareZ123/bb6/actions/runs/46097369705) finishes successfully.** The source-equivalent accelerator and the pinned native Cryptids source have different layers; a native machine wrapper would still be a separate deliverable.
