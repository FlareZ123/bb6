# Exact logarithmic inverse candidates for **every** Machine C section output

**Agent 15, 2026-11-06. Original-source certified intermediate algorithmic theorem.** Machine C and exact BB(6) remain open.

## Result

Let `secNext : Nat × Nat → Option (Nat × Nat)` be the unchanged accelerated section function in [Agent46's FastSectionDef.lean](../agent46-c-jump/FastSectionDef.lean), with blank-section initial state `(5,1)`.

Agent 11's original-source-verified [SectionFastInverseOriginal.lean](../agent11-c-bounce-exact/SectionFastInverseOriginal.lean) gave an exact list `fastUnfiltered x y` of `4*(Nat.log2(x+y+1)+1)+4` candidate predecessors, but its completeness theorem only covered targets with **y≥5**. Its [FastRootBackward.lean](../agent11-c-bounce-exact/FastRootBackward.lean) therefore used a dense quadratic `sourceCandidates` grid for y<5.

[TotalFastInverse.lean](TotalFastInverse.lean) removes that exception for **all natural x,y**. For y=3, the previously omitted even-bounce terminal case allows a recursion-depth witness n with `2^n ≤ x+6`. Its extra candidates are:

```text
(1, (x-3-3n)/2)
(A, (x+1-A-3n)/2),  A = (x+6)/2^(n+1)-3,
0 ≤ n ≤ floor(log2(x+6)).
```

All operations use natural-number arithmetic, including saturating subtraction, and each candidate is filtered by the original `secNext`. The existing logarithmic list handles y≥5 and the relevant y=4 bounce branches. Three exceptional predecessor pairs `(0,1)`, `(1,0)` and `(1,1)` complete the y≤4 cases. The source's special `k=0` branch is covered by Agent11's already-enumerated `(x+2,0)`.

**Lean-verified, unconditional theorems:**

```lean
theorem totalFastCandidates_exact (a k x y : Nat) :
  (a,k) ∈ totalFastCandidates x y ↔ secNext (a,k) = some (x,y)

theorem totalFastUnfiltered_length (x y : Nat) :
  (totalFastUnfiltered x y).length =
    4*fastCap x y + 7 + 2*(Nat.log2 (x+6)+1)
```

In particular the generated candidate list has **O(log(x+y+6))** size for every successful output, without an exceptional quadratic case. This is a bound on one-step *candidate enumeration*, not a polynomial-time claim for arbitrary rooted reachability: the complete backward graph and depth can still be large.

[TotalFastRoot.lean](TotalFastRoot.lean) supplies an unbounded-output, **fixed-target** exact rooted search:

```lean
theorem backwardTotalHalfFull_iff (x y : Nat) :
  backwardTotal ((x+2*y)/2) (x,y) = true ↔
    BB6.Agent11Mass.SectionReach x y
```

The inherited half-mass depth bound is Agent11's existing original-source theorem. The new backward branching is logarithmic at **every** visited node. No finite parameter cutoff is used in these mathematical iff statements.

A further integration with Agent1's already original-source-certified [BlankMassFour.lean](../agent1-forward-mass/BlankMassFour.lean) sharpens the fixed-target fuel to the **optimal linear mass-growth cutoff**:

```lean
theorem backwardTotalQuarterFull_iff (x y : Nat) :
  backwardTotal ((x+2*y-7)/4) (x,y) = true ↔
    BB6.Agent11Mass.SectionReach x y
```

[TotalFastQuarter.lean](TotalFastQuarter.lean) composes Agent1's authentic blank-source rank `7+4*n ≤ x+2*y` with the complete logarithmic predecessor oracle; the source step is sharp at gain four, but this does not assert that the complete reachability search has logarithmic runtime. It improves the **root depth cutoff** by nearly a factor two on large inputs, with no extra assumptions. This depth bound was already known separately in Agent1's research; the contribution here is its rigorously checked combination with the new logarithmic all-output inverse.

## Source integrity and verification

The manually dispatched [agent15-c-total-fast.yml](../../.github/workflows/agent15-c-total-fast.yml) compiles the unchanged full Machine C bounce, section, complete all-output inverse and Agent11 fast inverse, then both new modules under **Lean 4.36.0-rc2**.

[**Original-source CI 42197944716 PASSED**](https://github.com/FlareZ123/bb6/actions/runs/42197944716) (2026-11-06 09:50 UTC, source head `cb95c28567599e2c1717f5047a680291ca9dda3f`). Earlier [CI 42196614039](https://github.com/FlareZ123/bb6/actions/runs/42196614039) independently verified the two initial modules. The final `#print axioms` outputs for `totalFastCandidates_exact`, `backwardTotal_iff`, `backwardTotalHalfFull_iff`, and `backwardTotalQuarterFull_iff` were exactly `[propext, Classical.choice, Quot.sound]`; `totalFastUnfiltered_length` reported `[propext, Quot.sound]`. There are no `sorryAx`, custom axioms, or stub dependencies in this CI. During development the source theorem interfaces were mimicked by local stubs; those experiments do not replace the successful original-source audit.

Independent exact-integer finite reproduction tested all 21,025 source pairs `0≤a,k<145` for candidate inclusion, and exhaustively compared exact candidates with all mass-admissible source predecessors for 450 targets `0≤x<75`, `0≤y<6`. Both checks passed. Examples of **unfiltered** list sizes versus dense old grid positions:

| Target | New list | Old dense search grid positions |
|---|---:|---:|
| (10,000, 3) | 91 | 100,140,049 |
| (100,000, 4) | 109 | 10,001,800,081 |
| (1,000,000, 3) | 127 | 1,000,014,000,049 |

The numbers count candidate positions before exact source filtering; they are **not runtime speedup measurements**, and the dense search grid may be optimized in other ways. The Lean theorem, rather than finite sampling, supplies completeness.

## Scope and future use

This extends Agent11's algorithm and Agent3's previously certified unbounded complete inverse grammar [SectionAllInverse.lean](../agent3-c-bounce-inverse/SectionAllInverse.lean). It improves reusable verification infrastructure rather than identifying a new Turing-machine halting behavior.

The remaining genuine blank-origin Machine C halting reduction comprises two **infinite** stopping-parameter families. This fixed-target method cannot decide their joint existential without a new uniform stopping-family closure argument. Hence **no Machine C nonhalting theorem, six-state upper bound, or exact BB(6)** follows. Keep this intermediate tool in `im-results/`, not `results/`, pending external novelty and practical solver integration.
