# Original-source Sheep even-return inverse gateway

Agent 14, 2026-11-03. **Intermediate formally checked proof component. Sheep and BB(6) remain open.**

## Exact all-time theorem

Lean files:
- [SheepEvenInverseAlgebra.lean](SheepEvenInverseAlgebra.lean), the generic and exceptional predecessor equations.
- [SheepEvenSourceAlgebra.lean](SheepEvenSourceAlgebra.lean), a proof from the authentic Agent16 `SheepEven.Step` and `EvenEdge` definitions.
- [SheepEvenReachInverse.lean](SheepEvenReachInverse.lean), the theorem `blank_even_inverse_cases`, preserving genuine `EvenReach 10 x` for the last predecessor of every reachable noninitial rational-power target.

For any actual `EvenReach 10 y` with `y ≠ 10`, `d*y+c=2^n`, there is an even-reachable last parent `x`. Define `D=d*3^h`. The source-complete alternatives are:

Generic: `x=2^a*v`, `a≥1`, odd `v≥5`, and

```
D*(2^(a+1)+1)*v + 2*a*D + 2^(h+1)*(d+c)
  = 2^(n+h+1)+3*D.
```

Exceptional: `x=3*2^a`, `a≥1`, and

```
D*(3*2^a+a+2) + 2^h*(d+c) = 2^(n+h).
```

Both retain an odd `u` satisfying `y=1+3^h*u`. This exact universal necessary split follows by induction on the last edge of the original `EvenReach` relation, with no finite-horizon assumption. It is available for the three existing r=138 inverse-cone targets.

Local Lean 4.36.0-rc2 compiled all three files against the **original hash-pinned Agent16 Lean archive** modules `SheepEven.lean`, `EvenEdge.lean`, `OddPrefix.lean`, `EvenReach.lean`. The final axiom audit reports `[propext, Classical.choice, Quot.sound]`, without sorry or axiomatized source signatures. Reconstruct modules using `im-results/agent16-sheep-even-return/reconstruct_all.py`. Agent16's earlier original six-state-machine semantic bridge passed source-level [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547).

## Earlier cutoff correction

The previous `UniformH.lean` lemma `root138_node0_hstop` proved an exponent `141+4860*k` modular property; the r=138 root h≥3 inverse requires `2^(138+4860*k)%27 ≠1`. Corrected in commit `e7bd19c828d0a78f978222caad20a8a28c363684`. The old statement was true but applied to the wrong symbolic target. The corrected modular property follows from `2^18%27=1` and `4860=18*270`. No counterexample to the underlying written exclusion was found.

## Verification status and missing result

The expanded existing [manual source workflow](../../.github/workflows/agent22-sheep-source-bridge.yml) includes these modules. First dispatch [41639176407](https://github.com/FlareZ123/bb6/actions/runs/41639176407) failed in three seconds; the logs returned HTTP 404, so this was **not a new original-upstream CI verification**. No blind rerun was attempted. Local kernel verification against unmodified archived source is successful.

The full `∀k, ¬EvenReach 10 (2^(138+4860*k))` theorem still needs a Lean proof combining the present exact source gateway with low-a modular, all-large-a, high-h, exceptional, and rational-child closures. Earlier written proof and executable checker `uniform_138.py` remain the baseline. This is a genuine source-checkable integration step; external novelty has not been assessed. Keep in `im-results/`. Next work should construct the r=138 source predecessor classification using the corrected h cutoff, without new residue enumeration.
