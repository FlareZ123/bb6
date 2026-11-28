#!/usr/bin/env node
'use strict';
const fs = require('fs');
const path = require('path');
const outDir = process.argv[2] || path.join(__dirname, '..', 'agent16-raw44', 'generated-c1ra');
fs.mkdirSync(outDir, { recursive: true });
const source = String.raw`import Raw44CutAssembled
import Raw44B1RC_C1RA_A1LE_F0LE_Growth
import Raw44B1RC_C1RA_A1LE_F1Variants_Growth
import WeightedSymmetry
import WeightedTNF

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent8Raw44C1RAClosed
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16WeightedSymmetry
open BB6.Agent16Raw44Cut

private abbrev ef : StatePerm := swapStates (4 : Fin 6) 5

theorem hard0_source :
    hard0 = BB6.Agent16Raw44C1RA_A1LE_F0LE.table := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl

theorem hard2_source :
    hard2 = BB6.Agent16Raw44C1RA_A1LE_F1Variants.table true := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl

theorem hard4_source :
    hard4 = BB6.Agent16Raw44C1RA_A1LE_F1Variants.table false := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl

theorem hard1_renamed : renamePartial ef hard1 = hard0 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide +kernel

theorem hard3_renamed : renamePartial ef hard3 = hard2 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide +kernel

theorem hard5_renamed : renamePartial ef hard5 = hard4 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide +kernel

private theorem rename_never_back (e : StatePerm) (hroot : e.forward (0 : Fin 6) = 0)
    (m : Machine) (h : NeverHalts (renameTable e m)) : NeverHalts m := by
  intro n
  have hrun : run (renameTable e m) n blank =
      (run m n blank).map (renameConfig e) := by
    simpa [renameConfig,blank,hroot] using rename_run e m blank n
  have hn := h n
  rw [hrun] at hn
  simpa [blank] using hn

theorem hard0_never (m : Machine) (hm : compatible hard0 m) : NeverHalts m := by
  rw [hard0_source] at hm
  exact BB6.Agent16Raw44C1RA_A1LE_F0LE.never m hm

theorem hard2_never (m : Machine) (hm : compatible hard2 m) : NeverHalts m := by
  rw [hard2_source] at hm
  exact BB6.Agent16Raw44C1RA_A1LE_F1Variants.never true m hm

theorem hard4_never (m : Machine) (hm : compatible hard4 m) : NeverHalts m := by
  rw [hard4_source] at hm
  exact BB6.Agent16Raw44C1RA_A1LE_F1Variants.never false m hm

theorem hard1_never (m : Machine) (hm : compatible hard1 m) : NeverHalts m := by
  have hc := rename_compatible ef hm
  rw [hard1_renamed] at hc
  have hn := hard0_never (renameTable ef m) hc
  exact rename_never_back ef (by decide +kernel) m hn

theorem hard3_never (m : Machine) (hm : compatible hard3 m) : NeverHalts m := by
  have hc := rename_compatible ef hm
  rw [hard3_renamed] at hc
  have hn := hard2_never (renameTable ef m) hc
  exact rename_never_back ef (by decide +kernel) m hn

theorem hard5_never (m : Machine) (hm : compatible hard5 m) : NeverHalts m := by
  have hc := rename_compatible ef hm
  rw [hard5_renamed] at hc
  have hn := hard4_never (renameTable ef m) hc
  exact rename_never_back ef (by decide +kernel) m hn

theorem weighted_bound (m : Machine) (hm : compatible parent m) : WeightedBound 211 m :=
  BB6.Agent16Raw44Cut.weighted_bound
    hard0_never hard1_never hard2_never hard3_never hard4_never hard5_never m hm

theorem parent_cover : Cover (WeightedBound 211) parent :=
  Cover.leaf parent (fun m hm => weighted_bound m hm)

#print axioms hard0_source
#print axioms hard2_source
#print axioms hard4_source
#print axioms hard1_renamed
#print axioms hard3_renamed
#print axioms hard5_renamed
#print axioms hard0_never
#print axioms hard1_never
#print axioms hard2_never
#print axioms hard3_never
#print axioms hard4_never
#print axioms hard5_never
#print axioms weighted_bound
#print axioms parent_cover
end BB6.Agent8Raw44C1RAClosed
`;
const out = path.join(outDir, 'Raw44C1RAClosed.lean');
fs.writeFileSync(out, source);
console.log(out);
