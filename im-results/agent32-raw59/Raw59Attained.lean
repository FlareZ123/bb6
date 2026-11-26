import Raw590LB190Data
import Raw59Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59Sharp
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit
open BB6.Agent32Raw590LB190

def longest : Machine := fun s => (table s).getD none

theorem compatible_longest : compatible table longest := by
  intro s t h
  simp [longest,h]

theorem parent_compatible : compatible BB6.Agent32Raw59.p59 longest := by
  intro s t h
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first | contradiction | (cases h; rfl)

theorem halts_of_read (p : PartialMachine) (m : Machine) (n : Nat) (s : Slot)
    (hc : compatible p m) (hread : zipRead p n = some s) (hh : m s = none) : HaltsAfter m n := by
  rw [zipRead_eq] at hread
  cases hr : knownRun p n with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = s := by simpa [hr] using hread
    have hrun := knownRun_sound p m hc n c hr
    constructor
    · change (run m n blank).isSome = true
      rw [hrun]
      rfl
    · rw [run,hrun]
      simp [rawStep,hs,hh]

theorem longest_halts : HaltsAfter longest 4136170 :=
  halts_of_read table longest 4136170 (2,true) compatible_longest read_eq (by decide)
theorem longest_delay : 0 ∈ delays (zeroNext longest) 0 := by decide

theorem lower (B : Nat) (h : ∀ m, compatible BB6.Agent32Raw59.p59 m → WeightedBound B m) : 4136171 ≤ B :=
  h longest parent_compatible 4136170 0 longest_halts longest_delay
#print axioms longest_halts
#print axioms lower
end BB6.Agent32Raw59Sharp
