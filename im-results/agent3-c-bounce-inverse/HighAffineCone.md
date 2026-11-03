# Original-source all-time Machine C affine-three forbidden cone

**Agent 3, 2026-11-03 20:07 UTC.** This result excludes an infinite **two-dimensional set of genuine blank-section states**, without assuming they satisfy a halting equation. It does **not** decide Machine C or BB(6), and is retained in `im-results/` pending review of external novelty.

## Statement

For all natural `x y time`, if

```
x % 8 = 5
(2*x+y) % 128 = 6
```

then

```
BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y).
```

The theorem `BB6.Agent3.affine_three_cone_unreachable` is in [HighAffineCone.lean](./HighAffineCone.lean). It is an exact semantic statement for the authentic repository Machine C first-section map `BB6.Agent46.secNext`; it is quantified over all times and natural coordinates, with no simulation bound. The cone is infinite in both coordinates. Neither condition invokes the Machine C stopping equation, and the theorem does not classify the other reachable states.

## Exact inverse proof

For a hypothetical reachable target `(x,y)`, the congruences force three **source-validated, unique predecessor edges** in succession:

1. An affine even-right parent `A=(x+y-2,(y-2)/2)`. The theorem `BB6.Agent15.blank_reach_iff_affine` applies since `y≥4`, `y` is even, and `(x+y)%4=1`.
2. An odd/odd parent `B=((A.1+A.2-4)/2,(A.1+3*A.2-10)/4)`. The theorem `oddodd_lowval_blank_reach_iff` applies since `A.1,A.2` are odd, `A.2≥5`, `A.1+A.2≥24`, `(A.1+A.2)%4=0`, and `(A.1+A.2)%16≠0`.
3. An even/odd seven-sector parent `C=((B.1+B.2-5)/2,(B.1+3*B.2-9)/4)`. The theorem `odd_seven_blank_reach_iff` applies since `B.1` is even, `B.2` odd≥5, `B.1+B.2≥23` and `(B.1+B.2+1)%16=8`.

The same congruences force `C.2≥5`, `C.2` odd and `(C.1+C.2)%4=2`. The original-source `blank_section_odd_image` theorem requires every positive-time blank-origin section image with odd right≥5 to have sum mod4 in `{0,3}`. The initial section has second counter 1. Both possibilities therefore contradict reachability of `C`, and the three exact reachability iff lemmas transfer the contradiction back to `(x,y)`.

The complete guard arithmetic is discharged by Lean `omega`; the proof does not rely on an exhaustive finite list, truncated inverse search or sampled prefix.

## Verification

**Full unmodified-source manual CI succeeded:** [run 41708666534](https://github.com/FlareZ123/bb6/actions/runs/41708666534), [job 126170658126](https://github.com/FlareZ123/bb6/actions/runs/41708666534/job/126170658126), completed 2026-11-03 20:04:30 UTC. The workflow compiled unchanged original [FastSectionDef](../agent46-c-jump/FastSectionDef.lean), [Agent3CImage](../agent3-c-odd-image/Agent3CImage.lean), [ReachAffine](../agent15-c-halting/ReachAffine.lean), [OddOddLowVal](./OddOddLowVal.lean) and [OddSevenOrbit](./OddSevenOrbit.lean), then this theorem. Axiom audit for `affine_three_cone_unreachable` was exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

The source bridge from this repository's accelerated Machine C semantics to unmodified upstream DeepMind Cryptids is a separate proof obligation from this statement. The preceding repository section sources have source-level proofs, but this theorem itself is stated in terms of `secNext`, not raw primitive machine steps. A universal Busy Beaver upper bound does not follow.

## New comparison against mixed96 finite abstraction

The independent reproducible C++17 program [Mixed96AffineAudit.cpp](./Mixed96AffineAudit.cpp) transcribes the complete Machine C `nextC` branches and the existing mixed96 abstract-representative relation, then performs BFS from abstract blank state `(5,0,1)`. It **reproduces** Agent41's published experiment: `260672` reached abstract vertices and `2022544` processed edges.

The 128-modulus cone has exactly 144 satisfying pairs in a `384×384` fundamental torus, projecting to **36 distinct cells** in the mixed96 terminal plane `c=0`. **All 36 lie in the forward BFS reached set**; the tester asserts zero missing. In particular, this all-time source theorem cannot be proved merely by showing target absence from this specific finite quotient, even if the quotient's complete reachable set were subsequently proved in Lean. Abstract reachability gives no actual-machine witness. This comparison is a finite computational claim with an independently reproduced census, not a second semantic proof.

## Original Machine C high halting-family consequence

For actual high-stopping parameters `m≥6`, `m%4=2`, `(j+127*m)%128=87`, and `k+j+3*m+5=2^(2*m+2)*(j+3)`, the stopping target `(x,y)=(2*j+3,k)` satisfies the above congruences, since `2^(2*m+2)` is divisible by 128. Consequently the earlier [HighAffineInfinite theorem](./HighAffineInfinite.md) is contained in this broader source-exact cone exclusion. The direct high-family Lean proof has also passed [CI 41698364955](https://github.com/FlareZ123/bb6/actions/runs/41698364955).

## Remaining work

Review overlap with source-certified inverse cones and external Machine C literature before promotion to `results/`. More importantly, seek a coverage argument over *all* remaining first- and second-stopping families, or a transferable symbolic invariant for their actual blank-root orbit. Excluding selected cylinders does not decide whether the machine ever halts.
