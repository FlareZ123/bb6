# Source-certified exact inverse-depth and cost laws for Machine C bounce

Agent 3, 2026-11-02. **Intermediate theorem; no BB(6) or six-state holdout decision.**

The original-source Lean file [BounceInverse.lean](./BounceInverse.lean) imports Agent 46's *unchanged* `BounceCalc.lean` and proves two universal invariants about its total recursive `bounce k c` function. In every displayed formula `k,c,x,y,n` range over natural numbers, and `(bounce k c).2 = some (x,y)`.

## Exact quantified theorems

**Odd middle counter**, `k%2=1`: some common `n` satisfies

```text
x+y = 2^n * (2*k+6)
c+(2*k+6)+3*n = x+2*y
```

**Even middle counter**, `k%2=0`, and terminal second coordinate `y>=4`: some common `n` satisfies

```text
x+y+1 = 2^n * (2*k+8)
c+(2*k+8)+3*n = x+2*y+2
```

The even-case height guard is essential: the source `bounce k 4` with even `k` returns `some (2*k+2,3)` and does not obey the displayed even invariant. The `c=5` even exit is `none`. There is no recursion-depth truncation. Each theorem is proved by strong induction over the decreasing original source's `c` argument, preserving both identities with **one witness n** through each recursive branch.

These laws sharpen the prior separately certified sum-only properties `BouncePowerOdd.lean` and `BouncePowerEven.lean` in [Agent3's source image directory](../agent3-c-odd-image/), and support exact algebraic inversion rather than finite modular filtering.

## Source-level check

The manual-only [.github workflow](../../.github/workflows/agent3-c-bounce-inverse.yml) compiles original unmodified Agent 11, Agent 8, Agent 21, and Agent 46 dependencies before checking the new proof with **Lean 4.36.0-rc2**. [Full-source run 41469025396](https://github.com/FlareZ123/bb6/actions/runs/41469025396) **succeeded** at source commit `428dd473bbba2806db01236c9dcce58acff76a93`. Local compiler's `#print axioms` reported `[propext, Quot.sound]` for the odd invariant and `[propext, Classical.choice, Quot.sound]` for the even invariant. No `sorryAx`, `native_decide`, or extra postulates.

## Research application and open obligations

Agent 6 proposed an additional all-depth Machine C one-left stopping family `d ≡ 592 (mod 1024)`; see [our targeted collaboration message](../../communications/agent6/20261102T1512Z_agent3-bounce-cost-lemmas.md) and Agent 6's private message to Agent 3 (2026-11-02T14:51Z). The above theorems constrain each inverse path of the candidate endpoint `(24t,20t-1)`, `t=16q+4`, to recursion depths `n=0,2` for its even-bounce high predecessor branch. The resulting possible input classes are incompatible with Agent 38's existing blank-orbit mod-4 restrictions, **conditional upon a complete source-certified `secNext` predecessor case split and its side conditions**. This final original-section exclusion has not yet been proved here. Agent 6 is independently pursuing it.

The complete Machine C blank halting question and BB(6) remain open. Nothing in this directory belongs in `results/` until a mathematically decisive new classification is established.

## Original-source verification update: complete two-parent inverse (15:27Z)

[AffineTarget.lean](./AffineTarget.lean) universally proves that the affine section target `(384q+96,320q+79)` has **no predecessors outside** the two families `(352q+85,336q+81)` and `(88q+19,468q+111)`; [AffineTargetExact.lean](./AffineTargetExact.lean) verifies **both converses**, so this is a true *if and only if* classification, at every `q:Nat`. Both parents are inaccessible to the authentic blank section. The universally quantified [AffineTargetReach.lean](./AffineTargetReach.lean) formalizes this at *every* return time. Source-integrated Lean CI [41471628244](https://github.com/FlareZ123/bb6/actions/runs/41471628244) succeeded with ordinary axioms only. The earlier parent-only plus reachability source CI [41471289475](https://github.com/FlareZ123/bb6/actions/runs/41471289475) also passed.

Agent 6 independently completed the corresponding **depth 592 mod 1024** original-source stopping-level result (see [CSecondDepth.lean](../agent6-c-feeder/CSecondDepth.lean), verified in their shared [source CI 41467708583](https://github.com/FlareZ123/bb6/actions/runs/41467708583)). Our separate exact two-parent classification provides a stronger backward-structural statement and an independent cross-check, but the depth-592 pruning itself is not solely ours.

## Second disjoint infinite stopping-depth exclusion (15:39Z)

A further target family `T_q=(1536q+672,1280q+559)` has, by [AffineTarget56.lean](./AffineTarget56.lean), **only** potential source parents

```text
P0(q) = (1408q+613,1344q+585)
P2(q) = (352q+151,1872q+813).
```

Both are forbidden from the authentic blank section, by independent previously certified Agent 38 all-time restrictions. Every `P0(q)` has odd second coordinate and coordinate sum `2 mod 4` (and is not the initial `(5,1)`), while each `P2(q)` obeys the stronger odd-special condition `(a+k)%8=4`, `(a+3k)%16=14`. [AffineTargetReach56.lean](./AffineTargetReach56.lean) formalizes permanent nonreachability of every `T_q`.

[Feeder56.lean](./Feeder56.lean) proves via the full original recursive bounce grammar that the only possible predecessor of `F_q=(2048q+899,1024q+449)` is `T_q`. Thus no `F_q` occurs on the true blank run; Agent 3's previously source-certified exact feeder equivalence gives permanent exclusion of all `(1,4(512q+225))`. The unchanged Machine C halting-level identity then implies:

```text
∀ k depth time,
  4≤k → 2k-3=haltLevel 4 depth → depth%4096=2128 →
  run secNext time (some (5,1)) ≠ some (1,k).
```

This is `BB6.Agent46.dyadic_one_depth2128_mod4096_excluded` in [Depth2128.lean](./Depth2128.lean). **Full original-source Lean 4.36.0-rc2 CI [41473479595](https://github.com/FlareZ123/bb6/actions/runs/41473479595) passed** after reconstructing hash-pinned third-stage sources and compiling the entire prior section/blank-reachability proof chain. All the final new theorem axiom sets contained only `[propext, Classical.choice, Quot.sound]`, without `sorryAx`. This depth class is disjoint from Agent 6's 592 modulo 1024 class and from previously recorded 48 modulo 64, 8 modulo 16, and 2 modulo 8 classes. These are **new infinite exact arithmetic stopping-basin exclusions, not a full Machine C nonhalting proof**, so they remain in `im-results/` pending independent novelty review and larger synthesis.

The next priority is a generic two-level reverse grammar for more `j=4t+1` families and stronger forward reachable-set restrictions on their surviving odd-odd inverse branches. Do not continue adding narrowly scoped residue classes without a route toward a complete halting decision.

## Universal exact two-step predecessor grammar, independent of residue subclasses

The most broadly reusable new result is the exact **all-parameter** feeder equation in [FeederGeneric.lean](./FeederGeneric.lean). For every natural `t≥1`, and every natural source `a,k`, the original unmodified Machine C section satisfies

```text
secNext(a,k)=some(16*t+3,8*t+1)
    ↔ a=12*t and k=10*t−1.
```

This is a true *if-and-only-if*, covering every special case and every recursive bounce depth. The proof combines the new joint odd-bounce sum/cost theorem, the even-bounce parity obstruction, and a fully explicit terminal odd-bounce witness.

[FeederOrbitGeneric.lean](./FeederOrbitGeneric.lean) upgrades the exact edge to **unbounded blank-origin reachability**, then composes it with the previously original-source checked one-left gate equivalence:

```text
For every t≥1,
    CReach 1 (16*t+4) ↔ CReach (12*t) (10*t−1).
```

The [manual original-source Lean CI run 41475840788](https://github.com/FlareZ123/bb6/actions/runs/41475840788) **passed** with source commit `6a5e0039519a00f84e59f9209946bf7a4960bd89`; both new theorem axiom audits output only standard Lean axioms and no `sorryAx`. This subsumes individual parametric feeder inverses for specific `j≡1(mod4)` from this and other agents' intermediate dossiers, and simplifies future two-level reverse classification work. It is a structural equivalence between **reachability** predicates, not a Machine C halting or nonhalting decision. The new universal grammar has no finite-time bound or simulation cutoff.

Future priority: classify all possible source predecessors of `(12*t,10*t−1)` simultaneously, ideally through symbolic 2-adic recursion-depth parameters rather than adding more isolated congruence-class cases. For t odd, this precursor has residue `(a%4,k%4)=(0,1)` and Agent38 already globally excludes it; the remaining even-t sectors are where genuinely new inverse analysis is needed.

## Universal full-source predecessor grammar for the high odd-second target family (2026-11-02, 19:40 UTC)

**New contribution, all recursion depths:** [EvenTargetForward.lean](./EvenTargetForward.lean) provides explicit source-valid predecessor transitions for every `r≥0,u≥1`:

```text
P := 4^r*u
secNext (22*u-3, 32*P-11*u-3-3*r) = some(24*P,20*P-1).
```

The proof uses a total recursive inverse-construction `invLiftK`, `invLiftC`, proves their exact exponential affine formulas, and shows each prescribed inverse recursion really follows the original `bounce` definition. [Manual unmodified-source Lean CI 41512023225](https://github.com/FlareZ123/bb6/actions/runs/41512023225) **succeeded**, with ordinary axiom dependencies only.

[EvenTargetExact.lean](./EvenTargetExact.lean) proves the **complete universal iff** for *every* source input `a,k`, parameter `t≥1`:

```text
secNext (a,k)=some(12*t,10*t-1)
 ↔ ∃ r u, 1≤u ∧ t=2*(4^r*u) ∧
        a=22*u-3 ∧ k=32*(4^r*u)-(11*u+3+3*r).
```

This is exhaustive over all low and high source-map branches, including every recursive bounce depth. It combines earlier independently checked necessary power-four/cost laws in [GeneralHighInverse.lean](./GeneralHighInverse.lean) with an entirely source-realized construction and the modulo-eleven divisibility argument. [Manual unmodified-source Lean CI 41512485158](https://github.com/FlareZ123/bb6/actions/runs/41512485158) **succeeded**, standard axiom audit only. The set of possible `r` is finite for each fixed `t`, and nonempty only when `t` is even.

[EvenTargetOrbit.lean](./EvenTargetOrbit.lean) attempts to lift this exact inverse classification to all-time genuine blank-section orbit reachability `CReach`, and compose with the prior `generic_one_gate_reach_iff`. This all-time genuine blank-orbit equivalence **passed original-source Lean CI 41513332787**, with only ordinary axioms and no sorryAx. Thus the complete inverse grammar is valid at every blank-return time, not merely for synthetic source states.

**Scientific scope:** This family is a structural intermediate theorem; no original blank-input Machine C stopping decision, BB(6) upper bound, or exact value follows. Avoid double-counting known isolated residue exclusions already proved using the earlier Agent38 parity rule; the contribution is the universal complete inverse grammar, independent of congruence subclasses. Further work should exploit the remaining reachable parent families via global invariant or exhaustive symbolic preimage closure.

## General all-depth even-bounce inverse completeness (19:53 UTC)

[**BounceEvenExact.lean**](./BounceEvenExact.lean) removes the fixed output-parameter shape entirely. For every even original middle counter `K`, `y≥5`, and natural `c,x`, the source's *total* even-counter recursive interpreter satisfies an exact iff:

```text
(bounce K c).2=some (x,y)
  ↔ ∃ n:Nat,
      x+y+1=2^n*(2*K+8) ∧
      c+(2*K+8)+3*n=x+2*y+2.
```

The forward direction is the earlier established invariant. **The new converse** is proven by constructing every arbitrary-depth inverse path using `invLiftK`, `invLiftC` and their exact closed forms from `EvenTargetForward.lean`. It proves that both equations suffice for a *genuine source transition*, so arbitrary-depth candidate inverses are not spurious abstract states. This removes any need to simulate or bound recursion depth when inverting the even-bounce branch and applies to every output `(x,y)` satisfying the guard. The guard `y≥5` is essential because the special even-`K` case `c=5` stops rather than returns.

[**Manual full original-source Lean 4.36.0-rc2 CI 41513833722**](https://github.com/FlareZ123/bb6/actions/runs/41513833722) succeeded, checking the unmodified original `bounce` with standard axioms only. This result remains intermediate until used to solve a genuine blank input or unlock a machine-wide conclusion; no BB(6) claim.

## Complete exact inverse across the entire even/odd section-output quadrant (19:57 UTC)

[SectionOddInverse.lean](./SectionOddInverse.lean) establishes an **all-input, original-source exact iff** for every output `(x,y)` with `x` even, `y` odd, and `y≥5`. The complete preimage consists of exactly four possibilities:

1. Exceptional one-left source `(a,k)=(1,2)` yielding `(x,y)=(2,5)`;
2. Exceptional one-left source `(1,3)` yielding `(0,7)`;
3. One-left source `a=1,k≥4` and some recursion depth `n` satisfying `x+y+1=16·2^n` and `2k+13+3n=x+2y+2`;
4. High odd-source `a≥3` odd, `a<2k`, and some depth `n` satisfying `x+y+1=2^n(2a+6)` and `2k+a+9+3n=x+2y+2`.

All four cases are **if-and-only-if**, with every feasible arithmetic pair producing a real source transition. They exhaust every direct source branch and every recursive bounce, unbounded in both input counters and recursion depth. The proof directly composes the new `bounce_even_output_exact` with source case analysis and the prior original-source odd-bounce invariant. The full-original-source Lean 4.36.0-rc2 [manual CI run 41514385714](https://github.com/FlareZ123/bb6/actions/runs/41514385714) **passed**, standard Lean axioms only.

This is a general exact inverse grammar for a full infinite output quadrant, stronger in scope than the fixed affine `(12t,10t-1)` family and earlier finite inverse sieves. The full Machine C blank-orbit halting decision remains open. Future research should apply this to complete symbolic antecedents of Agent15's odd-a halting locus, using actual blank-orbit invariants rather than mere numerical modular exclusions.

## Exact inverse grammar for both recursive bounce branches and all y≥5 section returns

[**BounceOddExact.lean**](./BounceOddExact.lean) proves a full **converse** to the earlier one-way odd-bounce invariant: for all odd K and right output y≥4,
```text
(bounce K c).2=some (x,y)
 ↔ ∃ n:Nat, x+y=2^n*(2*K+6) ∧
              c+(2*K+6)+3*n=x+2*y.
```
The proof constructs the exact reverse odd-counter recursion with source-defined `oddLiftK/C`, independently of any depth bound. Its original unmodified-source Lean 4.36.0-rc2 [CI 41514882527](https://github.com/FlareZ123/bb6/actions/runs/41514882527) **succeeded** with ordinary axioms only. This complements `BounceEvenExact.lean`: **both** surviving recursive source branches now have full, mathematically complete sum/cost inverse equations, each with its required terminal guard.

[**FullSectionInverse.lean**](./FullSectionInverse.lean) composes the two bounce iff theorems with an exhaustive source case split into `sectionPreimageCriterion a k x y`. For every natural source `a,k`, natural output `x,y` with **y≥5**:
```text
secNext (a,k)=some (x,y) ↔ sectionPreimageCriterion a k x y.
```
The predicate has exact source-specific exceptional and direct cases, and uses one arbitrary recursion-depth witness `n` with two explicit arithmetic equations per branch. The proven converse guarantees *every* arithmetic solution yields a genuine original-section transition. [**Full source CI 41515256605**](https://github.com/FlareZ123/bb6/actions/runs/41515256605) **passed** with standard axiom audit only. This provides a complete, quantified source inverse for the whole positive-large second-counter sector, going beyond the even-first, odd-second subset in `SectionOddInverse.lean`.

Neither a growing library of predecessor iff theorems nor these exact normal forms establish a global blank-orbit exclusion. Open objective: combine with a useful forward-reachable invariant or symbolic well-founded backward argument that blocks **all** Machine C halting inputs, then address remaining BB(6) holdouts and universal coverage.
