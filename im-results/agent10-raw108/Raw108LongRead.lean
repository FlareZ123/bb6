import Raw108LongProof
import ZipAuditCore

namespace BB6.Agent10Raw108Long
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit
open BB6.Agent31ThreeHole BB6.Agent13BlankDelay

theorem zipRead_of_run0 (p : PartialMachine) (n : Nat) (c : Z0)
    (h : run0 p n ⟨0,[],[]⟩ = some c) :
    zipRead p n = some (c.q,c.l.headD false) := by
  have H : (zrun p n BB6Coverage.Agent31Pump.start).map BB6Coverage.Agent31Pump.project = some c :=
    (run_project p n BB6Coverage.Agent31Pump.start).trans h
  unfold zipRead
  cases hr : zrun p n BB6Coverage.Agent31Pump.start with
  | none => simp [hr] at H
  | some z =>
    have hz : BB6Coverage.Agent31Pump.project z = c := Option.some.inj (by simpa only [hr,Option.map_some] using H)
    subst c
    simp [hr,BB6Coverage.Agent31Pump.project]

theorem read_entry : zipRead (table none) 91502 = some (0,true) := by
  rw [zipRead_of_run0 (table none) 91502 (pr A15) segmentA]
  rfl

theorem read_kid1 : zipRead (table kid1) 4136170 = some (2,true) := by
  rw [zipRead_of_run0 (table kid1) 4136170 (pr C49) full_kid1]
  rfl

theorem read_kid5 : zipRead (table kid5) 4136170 = some (2,true) := by
  rw [zipRead_of_run0 (table kid5) 4136170 (pr C49) full_kid5]
  rfl

theorem read_kid22 : zipRead (table kid22) 4136174 = some (2,true) := by
  rw [zipRead_of_run0 (table kid22) 4136174 (pr C49) full_kid22]
  rfl

/-- Four exact table/time matches, all other cases use the ordinary zipper. -/
def longRead (p : PartialMachine) (n : Nat) : Option Slot :=
  if n == 91502 && tableOK p (table none) then some (0,true)
  else if n == 4136170 && tableOK p (table kid1) then some (2,true)
  else if n == 4136170 && tableOK p (table kid5) then some (2,true)
  else if n == 4136174 && tableOK p (table kid22) then some (2,true)
  else zipRead p n

theorem longRead_eq (p : PartialMachine) (n : Nat) : longRead p n = zipRead p n := by
  unfold longRead
  split
  · rename_i h
    simp only [Bool.and_eq_true,beq_iff_eq] at h
    obtain ⟨rfl,ht⟩ := h
    rw [tableOK_sound _ _ ht]
    exact read_entry.symm
  · split
    · rename_i h
      simp only [Bool.and_eq_true,beq_iff_eq] at h
      obtain ⟨rfl,ht⟩ := h
      rw [tableOK_sound _ _ ht]
      exact read_kid1.symm
    · split
      · rename_i h
        simp only [Bool.and_eq_true,beq_iff_eq] at h
        obtain ⟨rfl,ht⟩ := h
        rw [tableOK_sound _ _ ht]
        exact read_kid5.symm
      · split
        · rename_i h
          simp only [Bool.and_eq_true,beq_iff_eq] at h
          obtain ⟨rfl,ht⟩ := h
          rw [tableOK_sound _ _ ht]
          exact read_kid22.symm
        · rfl

#print axioms longRead_eq
end BB6.Agent10Raw108Long
