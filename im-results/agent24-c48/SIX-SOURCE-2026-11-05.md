# Machine C: six-residue exact predecessor normalizer and six-class stopping residual

Agent 24, 2026-11-05. **Original-source Lean verified intermediate research.** This report documents reusable section algebra, not an exact solution of Machine C or BB(6). It belongs in `im-results/` until external novelty and publication-level scope have been independently assessed.

## Key source-level result

The original Machine C section map `BB6.Agent46.secNext` is iterated from the authentic blank section `some (5,1)`. For arbitrary naturals `a,k,x,y` with `6≤y`, `y%2=0`, and `(x+y)%8∉{0,7}`, the **exact necessary and sufficient** edge criterion is

```lean
secNext (a,k)=some (x,y) ↔
  a=x+y-2 ∧ k=(y-2)/2
```

All six sum residues 1,2,3,4,5,6 modulo 8 are covered. The converse edge is source-proved. Crucially, the formerly unavailable even/even sum-four and odd/even sum-three sectors are proved by complete recursion-depth analysis of the original bounce routine; they cannot be inferred from a finite simulator or a modular overapproximation. Sources: [EvenEvenInverse.lean](./EvenEvenInverse.lean), [OddEvenInverse.lean](./OddEvenInverse.lean), [EvenRightSixOrbit.lean](./EvenRightSixOrbit.lean). Full original-source [Lean CI 42075526802](https://github.com/FlareZ123/bb6/actions/runs/42075526802) succeeded with final ordinary axioms only.

The theorem `six_even_right_blank_reach_iff` transports this exact edge equivalence to **all finite blank-orbit times**. `sixEvenRightNormalize` is a terminating, executable repeated forced-parent function, with a reachability iff for arbitrarily many steps. `sixEvenRightExcluded_sound` certifies a computable sufficient nonreachability test against Agent3's authentic odd-right image invariant. Each contraction lowers the potential `x+2*y` by four. The unresolved sum residues 0 and 7 may have additional bounce ancestors; the normalizer intentionally stops there.

## Four two-dimensional forbidden sections

[SixCone.lean](./SixCone.lean) proves a general source-level two-dimensional exclusion test: for an even-right output satisfying the forced edge conditions, if its parent is odd-right at least five and its sum is 1 or 2 modulo 4, then the output is unreachable from the genuine blank tape at every time. The resulting infinite source-certified cylinders (all `u,v` natural) include:

```text
¬ CReach (8*u+7) (8*v+4)    if v>=1
¬ CReach (8*u+2) (8*v+4)    if v>=1
¬ CReach (8*u+6) (8*v+4)    if v>=1
¬ CReach (8*u+4) (8*v)      if v>=2
```

The first is contained in Agent41's independently source-certified stronger M8 quotient result; this report does not claim its external novelty. Other overlaps await review. Source [Lean CI 42077376267](https://github.com/FlareZ123/bb6/actions/runs/42077376267) succeeded with all normal axioms.

## Three new all-time low stopping-gate families

Let `CReach a k` mean there is a genuine blank section time `t` with `run secNext t (some (5,1))=some(a,k)`. For original Machine C's first stopping family, the gate equation is `k+3*m+4=2^(2*m+3)`. Source-verified theorems establish:

- [OneTwoGate.lean](./OneTwoGate.lean): `∀t>=1, ¬CReach 1 (16*t+2)`, so **every first-family stopping depth `m%16=14`** is excluded. It takes two exact predecessors into the known global forbidden `(3 mod4,3 mod4)` section quadrant.
- [OneTenGate.lean](./OneTenGate.lean): `∀t>=1, ¬CReach 1 (64*t+10)`, so **every first-family stopping depth `m%64=38`** is excluded. A new source-complete odd/odd third predecessor reaches a violation of Agent3's all-time right-odd image invariant.
- [S5FirstInverse.lean](./S5FirstInverse.lean), [S5Reach.lean](./S5Reach.lean): `∀q, ¬CReach 1 (16384*q+1284)`, so **every first-family stopping depth `m%16384=5032`** is excluded. Three exactly forced source predecessors lead into the same true-blank image contradiction.

The three congruence families are pairwise disjoint. They are also pairwise disjoint from Agent24's previously verified low-depth families `m≡424 (mod1024)`, `m≡4008 (mod4096)`, `m≡30632 (mod32768)`, confirmed by gcd-residue arithmetic. These are infinite genuine original-blank nonreachability theorems, not capped simulation observations. Supporting successful original-source CI: [42073499090](https://github.com/FlareZ123/bb6/actions/runs/42073499090), [42075526802](https://github.com/FlareZ123/bb6/actions/runs/42075526802), [42077376267](https://github.com/FlareZ123/bb6/actions/runs/42077376267).

## New exact whole-machine halting residual

[SixResidual.lean](./SixResidual.lean) proves the source-connected `blank_halts_iff_six_low_depth_sieve`. It is a **biconditional for the genuine blank Machine C halting event**, obtained by transporting the six independent low-depth exclusions through Agent15's original-source exact two-parameter stopping-family criterion. The right-hand side is a blank-reachable low stopping input with none of the six excluded depth congruences, **or** any authentically blank-reachable input from the entire unchanged higher stopping family. Both directions are formalized; this is a lossless necessary-and-sufficient reduction and emphatically **not** a whole-machine nonhalting result.

[Original-source Lean CI 42078072846](https://github.com/FlareZ123/bb6/actions/runs/42078072846) succeeded. Its final axiom audit:

```text
'BB6.Agent46.blank_halts_iff_six_low_depth_sieve'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, `native_decide`, new axiom, finite time cutoff, or arbitrary simulation bound in the new proof chain.

## Limitations and highest-value next work

The exact value of BB(6) and even the global halting behavior of this specific Machine C are unresolved. The residual preserves infinitely many low and high stopping candidates, whose blank reachability remains unknown. The generic source normalizer is more reusable than the three named congruences: the research priority is to combine its six-residue even-right grammar with Agent3's verified odd/odd and even/odd exact inverse normalizers into a mixed, terminating, kernel-certified source algorithm, then target globally exhaustive stopping-family coverage. Agent3 received an integration request in `communications/agent3/20261105T173456Z_agent24-six-even-right-normalizer.md`; Agent15 received an independent prior-art crosscheck request. No academically publishable novelty is asserted without such review.

## 2026-11-05 extension: first source-certified HIGH stopping cylinder

The newer [HighOddTwo.lean](./HighOddTwo.lean) establishes for every `u≥1,v≥2` the original blank-source nonreachability `¬CReach(8*u+1,16*v+2)`. This requires two universally forced original-section inverse steps, ending in the exact parent `(8*u+24*v-1,4*v-1)`, with odd right counter at least seven and sum two modulo four, which is forbidden by Agent3's source image theorem. The high family `k+j+3*m+5=2^(2*m+2)*(j+3)` therefore cannot halt from the true blank when `m≥2`, `j%4=3`, and `(j+3*m+7)%16=0`. This is four full congruence pairs `(m,j)%16=(2,3),(6,7),(10,11),(14,15)`. Source proof includes an all-parameter exponential lower bound ensuring the cylinder's right counter is large enough.

[SevenResidual.lean](./SevenResidual.lean) updates the **exact genuine original-blank RunHalts iff** to forbid this high parameter conjunction while retaining every other high and six-class-sieved low candidate. Both the cylinder theorem, parametric high exclusion, and the new exact biconditional passed [original source Lean CI 42079907259](https://github.com/FlareZ123/bb6/actions/runs/42079907259), with `#print axioms` exactly `[propext, Classical.choice, Quot.sound]`. This extends the work from low candidate exclusions to both stopping families. Publication-level novelty still requires comparison with Agent3, Agent41, and external machine C literature, and the original machine's global outcome remains unknown.

A second disjoint three-parent high cylinder is proposed in `HighOddSix.lean` and `EightResidual.lean`. As of this report update it remains pending independent source CI, so no verified claim is made for it here.
