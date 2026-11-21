import ARegular3AdicBridge
import DRegularFast
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 180000

namespace BB6.Agent32HaltingCylinderShadowFast

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent2ARegular3AdicBridge
open BB6.DRegularFast

def seed9 : DRegular.L := ⟨9,0,0⟩

def cylinderC : Nat :=
  1975700577069254261393123959451562008800234946348086

def cylinderStart : DRegular.L := ⟨cylinderC,0,0⟩

/-- Evaluate the long regular prefix by the existing residue-reduced block
    evaluator, rather than reducing 2,640 individual transitions directly. -/
def root2640 : DRegular.L :=
  (fastRun 2640 seed9).getD seed9

def shadowParam : Nat := (root2640.a - cylinderC) / 3^7

def cylinderCheckpoint7 : DRegular.L :=
  ⟨1894533340924527074892141151262808491028546098858608597,1,7⟩

def rootCheckpoint7 : DRegular.L :=
  BB6.DRegularShift.shiftNat cylinderCheckpoint7 (8^7*shadowParam)

theorem root2640_some : (fastRun 2640 seed9).isSome = true := by
  decide

theorem root2640_run : DRegular.run 2640 seed9 = some root2640 := by
  have hc : DRegular.Canon seed9 := by
    norm_num [DRegular.Canon, seed9]
  rw [fastRun_correct 2640 seed9 hc]
  cases h : fastRun 2640 seed9 with
  | none => simp [h] at root2640_some
  | some s => simp [root2640,h]

/-- Exact arithmetic shadow: the 2,640th root section is a 3^7 lift
    of the external halting-cylinder start, with lift parameter 1 mod 3. -/
theorem root2640_shape :
    root2640.q = 0 ∧ root2640.b = 0 ∧
    root2640.a = cylinderC + 3^7*shadowParam ∧
    shadowParam % 3 = 1 ∧ shadowParam % 2 = 1 := by
  decide

theorem root2640_lift :
    root2640 =
      BB6.DRegularShift.shiftNat cylinderStart (3^7*shadowParam) := by
  decide

theorem cylinder_run7 :
    DRegular.run 7 cylinderStart = some cylinderCheckpoint7 := by
  decide

/-- Model synchronization for the seven-step prefix. This does not assert
    a general identification of DRegular.next with external A_step2. -/
theorem root_shadow_model :
    DRegular.run 7 root2640 =
      (DRegular.run 7 cylinderStart).map
        (fun t => BB6.DRegularShift.shiftNat t (8^7*shadowParam)) := by
  rw [root2640_lift]
  exact BB6.DRegularShift.run_shift 7 cylinderStart shadowParam
    (by norm_num [DRegular.Canon,cylinderStart,cylinderC])

theorem root_shadow_checkpoint7 :
    DRegular.run 7 root2640 = some rootCheckpoint7 := by
  rw [root_shadow_model,cylinder_run7]
  rfl

theorem root_checkpoint7_mod3 : rootCheckpoint7.a % 3 = 0 := by
  decide

theorem cylinder_checkpoint7_mod3 : cylinderCheckpoint7.a % 3 = 1 := by
  decide

/-- The next regular-model branches diverge: root lift takes A, while
    the external cylinder path takes E. -/
theorem root_eighth_suffix :
    (DRegular.next rootCheckpoint7).map (fun s => (s.q,s.b)) =
      some (1,5) := by
  decide

theorem cylinder_eighth_suffix :
    (DRegular.next cylinderCheckpoint7).map (fun s => (s.q,s.b)) =
      some (3,4) := by
  decide

/-- Seven original-source transitions from the lifted root section to
    the shifted external checkpoint, using the existing source contract. -/
theorem root_source_shadow :
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run (DRegular.accumulated 7 root2640)
        (DRegularSource.sourceSection root2640))
      (DRegularSource.sourceSection rootCheckpoint7) := by
  have hc : DRegular.Canon cylinderStart := by
    norm_num [DRegular.Canon,cylinderStart,cylinderC]
  have h := BB6.DRegularSourceShift.lifted_original_run
    cylinderStart cylinderCheckpoint7 7 shadowParam hc cylinder_run7
  simpa [root2640_lift,rootCheckpoint7,
    BB6.DRegularSourceShift.inputLift,
    BB6.DRegularSourceShift.outputLift,
    BB6.DRegularShift.shiftNat] using h

private theorem seed9_source :
    DRegularSource.sourceSection seed9 =
      CryptidBoundary.init (List.replicate 7 true) := by
  simp [seed9,DRegularSource.sourceSection,oppairs]

/-- The 2,640th DRegular section is connected to the authentic blank
    start by the original six-state source contract. -/
theorem blank_root_at_2640 :
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run
        (36 + DRegular.accumulated 2640 seed9) CryptidBoundary.blank)
      (DRegularSource.sourceSection root2640) := by
  have hc : DRegular.Canon seed9 := by
    norm_num [DRegular.Canon,seed9]
  have h := DRegular.transport_obs
    CryptidBoundary.run DRegularSource.sourceSection BB6.BoundaryPadding.ObsEq
    (fun c => rfl) CryptidBoundary.run_add
    (fun c => cfgEq_refl (represent c))
    (fun x y z h g => cfgEq_trans h g)
    (fun n x y h => source_congr n h)
    BB6.ERemaining.source_contract
    2640 seed9 root2640 hc root2640_run
  rw [CryptidBoundary.run_add,CryptidBoundary.blank36,←seed9_source]
  exact h

/-- Composed authentic blank-root path to the shifted seventh checkpoint.
    The target is not in the remaining 3^101 halting cylinder because its
    unary parameter is 0 mod 3 rather than 1 mod 3. -/
theorem blank_root_to_checkpoint7 :
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run
        (36 + DRegular.accumulated 2640 seed9 +
          DRegular.accumulated 7 root2640) CryptidBoundary.blank)
      (DRegularSource.sourceSection rootCheckpoint7) := by
  have h0 := blank_root_at_2640
  have h1 := root_source_shadow
  have h0' := source_congr (DRegular.accumulated 7 root2640) h0
  rw [CryptidBoundary.run_add]
  exact cfgEq_trans h0' h1

#print axioms root2640_run
#print axioms root2640_shape
#print axioms root_shadow_model
#print axioms root_source_shadow
#print axioms blank_root_at_2640
#print axioms blank_root_to_checkpoint7

end BB6.Agent32HaltingCylinderShadowFast
