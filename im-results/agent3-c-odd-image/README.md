# Agent 3: Machine C exact section image and infinite affine gate equivalence

**Status: source-certified Lean intermediate research, 2026-11-02.** The genuine Machine C blank start, source definitions, published source semantics, and original Agent38 auxiliary proof are unchanged. No Machine C or BB(6) halting decision is claimed. All new source lives in this directory; the manually dispatched verification workflow is `.github/workflows/agent3-c-odd-image.yml`.

## All-input bounce-image invariant

Theorem `BB6.Agent3.bounce_large_image` (`Agent3CImage.lean`): for all natural `k,c,x,y`,

```
(bounce k c).2 = some (x,y) ∧ 4 ≤ y
  → (x+y)%4=0 ∨ (x+y)%4=3.
```

The proof uses strong induction on the **strictly decreasing** high counter in Agent46's original recursion. Terminal odd-middle branches have sum `2*k+6`, divisible by four; terminal even-middle branches of height ≥4 have sum `2*k+7`, congruent to three mod four. Only the exceptional height-three output lies outside the theorem. Recursive branches preserve the final output exactly.

Theorem `section_odd_image` transfers this to the **complete** original `secNext` map: for every input and successful output `(x,y)` with odd `y≥5`, the sum lies in `{0,3} (mod4)`. Theorem `blank_no_two_three_high` therefore globally excludes every blank-start section point

```
(4*u+2, 4*(v+1)+3),   u,v : Nat,
```

at **every** natural section time. This is a universal inductive image restriction rather than a bounded experiment.

## Exact all-natural predecessor for the infinite (1,4j) line

Theorem `BB6.Agent3.section_one_four_exact` (`Agent3COneFamily.lean`) proves for all natural `a,k,j` with `1≤j`:

```
secNext (a,k) = some (1,4*j)
  ↔ a=4*j-1 ∧ k=2*j-1.
```

For the forward direction, the preceding bounce-image theorem excludes every bounce predecessor since `(1+4j)%4=1`. The other direct section branches have incompatible output; the only possible affine high-input branch fixes `a=4j-1,k=2j-1`. Conversely these values satisfy the source's long-section branch and produce `(1,4j)` in one exact `secNext` call.

Theorem `BB6.Agent3.blank_one_four_iff_feeder` (`Agent3COrbitIff.lean`) upgrades this to genuine **all-time blank-orbit reachability**:

```
CReach 1 (4*j) ↔ CReach (4*j-1) (2*j-1)    (j≥1).
```

Here `CReach a k := ∃ t, run secNext t (some (5,1))=some (a,k)`; the start `(5,1)` is original-source checked through Agent46's existing semantic bridge. The right-to-left implication adds one section step; the left-to-right implication analyses the final predecessor. The initial state is distinct from `(1,4j)`.

This exact equivalence simultaneously handles all infinite dyadic a=1 halting-target indices with `k≡0(mod4)`. If any feeder is actually blank-reachable, its target is too. Proving none of these feeders is blank-reachable, or finding one, remains an **unbounded global obligation**.

## Exact exclusion of first dyadic halting target (1,4)

`Agent3C14.lean` imports the **unmodified** Agent38 theorem `bounce_positive` to show that `secNext` never outputs `(3,1)`. The unique predecessor formula for `(1,4)` is `(3,1)`, and the actual blank start is `(5,1)`. Consequently, for every time,

```
run secNext time (some (5,1)) ≠ some (1,4).
```

The `(1,4)` target corresponds to depth zero of the complete a=1 dyadic halting basin established by Agent46. Other infinitely many stopping targets remain.

## Source verification, reproducibility, limits

The [latest successful GitHub Actions run **41442813596**](https://github.com/FlareZ123/bb6/actions/runs/41442813596), job `125268594335`, checked source commit `273325989ffcffb9c0d27da839b0ef7008a16c18`. Original unchanged `CLine`, `GenericSection`, `CReachBridge`, `CPhaseRank`, `CSectionTotal`, all needed Agent46 jump/bounce modules, and original Agent38 `Agent38SectionParity` were compiled first. Then all four original Agent3 source files compiled with exit status zero:

- `Agent3CImage.lean`: global bounce and section image theorem.
- `Agent3C14.lean`: pointwise and blank-orbit forbidden `(3,1)` and `(1,4)`.
- `Agent3COneFamily.lean`: the uniform exact infinite predecessor line.
- `Agent3COrbitIff.lean`: the exact blank-origin reachability equivalence.

The last `#print axioms` audits for `section_one_four_exact` and `blank_one_four_iff_feeder` each output only `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or `native_decide`. The same applies to `blank_no_14` and `section_no_31`, verified in [prior complete source CI 41441884283](https://github.com/FlareZ123/bb6/actions/runs/41441884283).

The mathematical next step is to characterize the true forward blank-reachability of the infinite affine feeder `a=2k+1`, with `k=2j-1` odd. This requires more than a finite modulus sieve or a short inverse cone. The empirical absence of such feeders from a finite trace is **not** a proof, and the present theorem does not decide Machine C or BB(6). Please challenge every proposed global exclusion with exact original-source counterexamples before inferring closure.

All artifacts remain under `im-results/`, preserving the repository's requirement that only academically publishable frontier advances enter `results/`.
