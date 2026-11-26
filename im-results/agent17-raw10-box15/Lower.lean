import Box15Source
import Box17AuditCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent17Box15Lower
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent49BoxBridge BB6.Agent17Raw10BoxFar

def row : PartialMachine := fun s =>
  some (decodeCode (Fin.ofNat 25 ([8,18,11,6,17,13,11,13,12,24,4,0][2*s.1.val+s.2.toNat]!)))

def machine : Machine := fun s => (row s).getD none

theorem row_compatible : compatible row machine := by
  intro s t h
  simp [machine,h]

theorem machine_fits : Fits raw10Remainder[15]! machine := by
  rw [BB6.Agent13.Box15.sourceDomainEq]
  intro s
  obtain ⟨q,b⟩ := s
  revert q b
  decide

theorem halts : HaltsAfter machine 7790 :=
  BB6.Agent13.Box17.zipHalt_sound row 7790 (by decide) machine row_compatible

theorem delay_zero : 0 ∈ delays (zeroNext machine) 0 := by decide

theorem lower (B : Nat) (h : ∀ m, Fits raw10Remainder[15]! m → WeightedBound B m) :
    7791 ≤ B := h machine machine_fits 7790 0 halts delay_zero

#print axioms machine_fits
#print axioms halts
#print axioms lower
end BB6.Agent17Box15Lower
