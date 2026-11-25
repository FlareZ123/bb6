import Raw108LEFastA
import Raw108LEFastB
import ZipAuditCore
set_option maxRecDepth 100000
namespace BB6.Agent10Raw108LEFast
open BB6Coverage BB6Coverage.Agent13PackedZipper BB6Coverage.Agent10ZipAudit BB6.Agent31ThreeHole

theorem readA : zipRead (table false) 192167 = some (5,true) := by
  rw [← readRunP_eq]
  unfold readRunP
  rw [Afull]
  rfl

theorem readB : zipRead (table true) 191383 = some (5,true) := by
  rw [← readRunP_eq]
  unfold readRunP
  rw [Bfull]
  rfl

def fastRead (p : PartialMachine) (n : Nat) : Option Slot :=
  if n == 192167 && tableOK p (table false) then some (5,true)
  else if n == 191383 && tableOK p (table true) then some (5,true)
  else zipRead p n

theorem fastRead_eq (p : PartialMachine) (n : Nat) : fastRead p n = zipRead p n := by
  unfold fastRead
  split
  · rename_i h
    simp only [Bool.and_eq_true,beq_iff_eq] at h
    obtain ⟨rfl,ht⟩ := h
    rw [tableOK_sound _ _ ht]
    exact readA.symm
  · split
    · rename_i h
      simp only [Bool.and_eq_true,beq_iff_eq] at h
      obtain ⟨rfl,ht⟩ := h
      rw [tableOK_sound _ _ ht]
      exact readB.symm
    · rfl

#print axioms fastRead_eq
end BB6.Agent10Raw108LEFast
