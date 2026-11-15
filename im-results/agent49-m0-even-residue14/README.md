# m=0, n=32k+14: finite q4 bridge candidate

**Status: base q4-prefix source candidate drafted, not Lean-compiled.** This is the next root family after the candidate middle-17 endpoint. It is an intermediate artifact, not a complete counted increment theorem.

## Exact finite bridge

Direct simulation of the 12-entry TM2 table from the source configuration `S1(5,14,0,1,0,0,0)` gives:

- after the 9-step `3a` left sweep (`a=1`): state 3, head -3;
- relative to that head, the `[-9,2]` window has ones at `{-7,-6,-5,-4,-1,2}`;
- the next 39 transitions stay in `[-9,2]` and end in state 4 at relative head `+3`, with ones `{-9,-8,-7,-4,-1,1,2}` in the window.

The bridge is the existing canonical 39-step m=0,n=2 bridge, reused unchanged. The Lean file proves the five-block source/target BinDec decompositions and `m0EvenFourteenBridge_input_match`, which identifies the entire post-sweep `[-9,3]` window for arbitrary `a>0`. `M0EvenFourteenQ4Prefix.lean` then packages the base n=14 q4 prefix run, right shape, far-tail and left-facing facts, plus the q4 suffix target-left identity.

## Why this is the next root family

After the candidate middle-17 row, the state has marker 0 and counter

`n = 16*r-2 = 32*k+14`, where `r=2*k+1`.

The complement encoding has the exact five-block decompositions

- `binDec L (32*k+14) = d1 ++ d0 ++ d0 ++ d0 ++ d1 ++ binDec (L-5) k`,
- `binDec L (32*k+13) = d0 ++ d1 ++ d0 ++ d0 ++ d1 ++ binDec (L-5) k`.

The bridge reads only the first five blocks and the marker/d0 prefix. Its head trace never reaches the arbitrary higher-order tail. Thus the finite certificate is the missing local component for a uniform `n=32*k+14` frame-lifted q4 prefix.

Since `v2(32*k+14)=1`, the reset prefix cost predicted by the shared recurrence is

`resetPrefixCost 0 (32*k+14) a b = 75 + 12*a + 3*b`.

The 39-step bridge plus the 3a sweep and 3(a-1) E-scan gives q4-prefix cost `36+12*a`; the generic q4 suffix contributes `39+3*b`. The expected full counted increment endpoint is

`S1(L,32*k+13,2,a+b+1,0,2^b-1,h+5+3*b)`.

## Remaining proof obligations

1. Prove the two five-block `binDec` decompositions from `binDec_even` / `binDec_odd` under `L>=5` and the source bound.
2. Prove the post-sweep `[-9,2]` input match for arbitrary `a>0` using the exact left stream and `sweptLeft` frame lemmas.
3. Lift the finite bridge over the untouched `binDec (L-5) k` tail.
4. Prove the q4 cut right-shape/far-tail/left-facing facts, compose `q4_suffix_run_to_s1Config`, then attach the counted drain.
5. Compose the resulting `m=0,n=32*k+14` counted increment with the middle-17 root endpoint.

No local Lean runtime was available in this invocation, so the finite `decide` certificate and all proposed source-level generalizations remain uncompiled. Do not promote this directory to `results/` until the full source theorem compiles and passes transitive axiom checks.

The remaining work is the general tail lift for `L>=5`, `n=32*k+14`, the generic q4 suffix composition, and the counted drain. The expected counted increment endpoint is `S1(L,32*k+13,2,a+b+1,0,2^b-1,h+5+3*b)`. A final root wrapper can then compose this row with the middle-17 candidate.

## Independent finite simulations

A self-contained Lean 4.36.0-rc2 replay of the original 12-entry TM2 table (copied verbatim from `ChampionRootBridge.lean`) and S1 encoding was compiled locally on two sample configurations. The source is `LocalFiniteReplay.lean` and imports only `Lean`:

- `L=5,n=14,a=1,b=1`: 48 moves, state 4 at the original head, head range `[-12,1]`, and the complete left-facing stream agrees with the expected q4-cut word.
- `L=6,n=46=32*1+14,a=2,b=0`: 60 moves, state 4 at the original head, head range `[-15,1]`, and the complete left-facing stream agrees with the expected generalized target word.

The four sample theorems (`sample14_a1_b1`, `sample46_a2_b0`, and the two head-bound checks) compile by kernel `decide`; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. These are finite sample checks, not a proof of the general source family. The repository-dependent `M0EvenFourteenQ4Bridge.lean` and `M0EvenFourteenQ4Prefix.lean` still require the project dependency environment and have not been compiled.