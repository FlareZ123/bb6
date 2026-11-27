import PackedAudit
import RootShift
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw139E1ZeroRD
open BB6Coverage BB6Coverage.FAR BB6.Agent50TNFPilot BB6.Agent13BlankDelay

def parentPrefix : PartialMachine := fromCodes [7,24,11,24,14,24,24,16,24,13,24,24]
def seed : Config := { state := 3, head := 1, tape := fun x => decide (x = 2) }

theorem prefix_run (m : Machine) (hm : compatible parentPrefix m) : run m 5 blank = some seed := by
  apply knownRun_sound parentPrefix m hm
  change knownRun parentPrefix 5 = some seed
  have h : (knownRun parentPrefix 5).isSome = true := by decide +kernel
  have hread : (knownRun parentPrefix 5).map (fun c => (c.state,c.head)) = some (3,1) := by decide +kernel
  change knownRun parentPrefix 5 = some seed
  rw [show knownRun parentPrefix 5 = some ({state := 3, head := 1, tape := fun x => if x = 0 then false else if x = 1 then false else if x = 2 then true else if x = 1 then true else if x = 0 then true else false} : Config) by rfl]
  congr 1
  congr 1
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> by_cases h2 : x = 2 <;> simp_all

theorem c_one (m : Machine) (hm : compatible parentPrefix m) :
    run m 1 (blankAt 2) = some (shiftConfig (-2) seed) := by
  have h : m (2,false) = some ⟨true,false,3⟩ := hm (2,false) _ (by decide)
  simp [run, rawStep, readSlot, blankAt, h, applyMove, shiftConfig, seed]
  funext x
  simp
  congr 1
  omega

theorem restart_tail (m : Machine) (hm : compatible parentPrefix m) (k : Nat) :
    run m (5+k) blank = (run m (1+k) (blankAt 2)).map (shiftConfig 2) := by
  rw [run_append, prefix_run m hm, run_append m (blankAt 2) 1 k, c_one m hm]
  simp only [Option.bind_some, shift_run]
  cases h : run m k seed with
  | none => rfl
  | some c =>
    simp only [Option.map_some, shift_shift]
    cases c
    simp [shiftConfig]

theorem restart_halts (m : Machine) (hm : compatible parentPrefix m) (k : Nat) :
    HaltsAfter m (5+k) ↔ HaltsAfterAt m 2 (1+k) := by
  unfold HaltsAfter HaltsAfterAt
  rw [restart_tail m hm k, show 5+k+1 = 5+(k+1) by omega, restart_tail m hm (k+1)]
  rw [show 1+(k+1) = 1+k+1 by omega]
  cases h : run m (1+k) (blankAt 2) <;> cases h' : run m (1+k+1) (blankAt 2) <;> simp

#print axioms restart_halts
end BB6.Agent3Raw139E1ZeroRD
