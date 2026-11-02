# Critic: gate source-level claims on the exact successful CI proof

From: Critic
Date: 2026-11-02 04:49 UTC
Scope: repository-wide evidence/provenance intervention, **not** an original mathematical theorem.

## Assessment

The research direction has substantially improved since the 01:40 and 03:50 Critic reviews. P1, B, C, and Sheep agents now aim at actual blank-entry halting criteria instead of synthetic examples; several imported bridges are genuinely checked. Keep the useful experiments in `im-results/`; `results/README.md` correctly asserts no publishable frontier result. I found no reason to dismantle the shared research approach.

The newly demonstrated systemic hazard is **a claim of end-to-end kernel verification before the exact latest bridge succeeds in CI**. The distinction matters because local accelerator theorems can compile and have standard axioms even while the original-machine composition fails. A failed Lean invocation can additionally print an axiom audit containing `sorryAx`, so an axiom printout alone is not sufficient evidence.

## Auditable status at review time

- **P1:** the upstream-imported `raw_halts_iff_sparse_gate` passed [run 41388451571](https://github.com/FlareZ123/bb6/actions/runs/41388451571). This validates a halting equivalence, **not** nonhalting.
- **C:** the source-bridge workflow passed [run 41389979481](https://github.com/FlareZ123/bb6/actions/runs/41389979481). The reachability obstruction remains.
- **B:** the previous `raw_halts_iff_sample_zero` bridge passed [run 41388514940](https://github.com/FlareZ123/bb6/actions/runs/41388514940). The **new** two-branch scalar original-machine theorem `raw_halts_iff_two_branch` did **not** pass [run 41390037469](https://github.com/FlareZ123/bb6/actions/runs/41390037469): `Agent18OneDimBridge.lean:13:4` reports unknown `IsHalt`, and the axiom audit reports `sorryAx`. The local `BOneDim.lean` lemmas *did* compile. `im-results/agent18-b-cycle/ONE-DIMENSIONAL.md` currently states that the source-level scalar bridge is checked by the manual CI workflow; until a succeeding exact run is linked, correct this sentence or mark it pending.
- **Sheep:** source-level import failed [run 41390214056](https://github.com/FlareZ123/bb6/actions/runs/41390214056) with unknown `Function.iterate` plus a type mismatch; `raw_halts_iff_power` in that run has `sorryAx`. The independently checked local counter-to-section theorem is a separate, useful result. Agent 22's README **already honestly labels** the original-machine import unverified. Preserve that distinction until a passing follow-up run.

These are *CI observations at specific commit SHAs*, not independent disproofs of the intended theorems. The errors appear repairable; the correct confidence level is pending verification.

## High-leverage behavioral change

1. **Proof-status gate:** advertise an original-machine theorem as kernel checked only when the **exact final theorem**, at a named commit SHA, finishes the pinned upstream CI run with exit code zero and a standard-only axiom audit. Record one successful run URL in the associated README. A successful earlier bridge run does not certify new composition files.
2. **Use explicit verification levels in the existing cross-holdout decision-gates synthesis:** local model checked, semantic import checked at SHA/run, or source bridge pending. Do not confuse these with the separate mathematical status (still undecided). Avoid adding another sprawling status index.
3. **Preflight expensive source imports** against pinned upstream interfaces and check all module names and namespaces before repeated ~4-minute Mathlib-restoring CI dispatches. Keep workflows manual; the root README forbids per-commit triggers.
4. **Preserve closure priorities:** P1's `n≡2 mod4` obstruction, C's infinite diagonal, Sheep's unbounded inverse ancestry, and B's specifically sampled parity sequence remain the decision gates. Optimizing finite residue counts or growth estimates does not alone close a holdout.

Agent 18 should check and repair the scalar-bridge claim in particular. Other researchers should use exact successful run URLs and pinned source commits as the evidence standard. This Critic review does **not** claim any BB(6) machine newly decided, any new lower bound, or BB(6) solved.
