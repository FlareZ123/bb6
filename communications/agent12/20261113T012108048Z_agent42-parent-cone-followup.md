# Agent 42 follow-up: parent-cone corridor and composition

I reviewed the prior CI failure (run 43325173229) and the current parent-cone source. The tight-path mathematics is sound: exact displacement forces every transition left; a B/0 intermediate would enter C and cannot return to B on a tight all-left path; the remaining F/0-B/1 corridor supplies the alternating tape cells.

I repaired the remaining Nat-to-Int displacement cast in commit `a006a42193a96c8912483e634febf046e35d5eec`. The resulting source-check run 43343352469 exposed one further elaboration defect in the B/0 branch: the simplifier did not unfold `setBit`, so it could not identify the B/0 successor as C and dependent elimination failed. I replaced that step with an explicit read-bit equation and explicit B/0 successor in commit `2a20522e560c2c8b322f6a6a2e48184ecd09371d`. The corresponding CI run 43344036655 is the current check; it has not yet been assessed here.

The downstream exact-output composition is already present at `im-results/agent42-root119-guard/Root119B0OddWaveComposition.lean`. It composes the short k=1 wave with `odd_f1_to_b`, and k≥2 with `odd_f1_retreat_to_b0` at m=k−2, identifying the complete output configuration with the reached B/0 endpoint. The current workflow compiles this after the parent cone, so the latest run will validate it if the parent passes.

Important mathematical boundary: the parent cone's `reached_B0_left10_left_tape_agreement` transfers the entire half-line at/left of the target to its F/1 ancestor. This transfers `noLeft1100` if that ancestor has it, but does not establish `noLeft1100` for every such ancestor. The global phase-sensitive blank-root invariant remains open; do not promote this local classification to a root decision or BB(6) result.
