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

/-- The seven shorter continuations reuse the same accepted 91,502-step
prefix and a constant-length suffix. -/
def scan (z : Z0) := (z.q,z.l.headD false)

theorem patch_scan (a1 : Option (Option Move)) (k : Nat)
    (h : (run0 (table a1) k (pr A15)).map scan = some (2,true)) :
    (run0 (table a1) (91502+k) (pr A0)).map scan = some (2,true) := by
  rw [run0_add,run_refine a1 91502 (pr A0) (pr A15) segmentA]
  exact h

theorem zipRead_scan (a1 : Option (Option Move)) (n : Nat)
    (h : (run0 (table a1) n (pr A0)).map scan = some (2,true)) :
    zipRead (table a1) n = some (2,true) := by
  cases hr : run0 (table a1) n (pr A0) with
  | none => simp [hr] at h
  | some c =>
    rw [zipRead_of_run0 (table a1) n c hr]
    simpa only [hr,Option.map_some,scan] using h

def shortKid2 : Option (Option Move) := some (some ⟨false,false,2⟩)
theorem read_short2 : zipRead (table shortKid2) 91503 = some (2,true) :=
  zipRead_scan shortKid2 91503 (patch_scan shortKid2 1 (by rfl))

def shortKid4 : Option (Option Move) := some (some ⟨false,false,4⟩)
theorem read_short4 : zipRead (table shortKid4) 91505 = some (2,true) :=
  zipRead_scan shortKid4 91505 (patch_scan shortKid4 3 (by rfl))

def shortKid8 : Option (Option Move) := some (some ⟨false,true,2⟩)
theorem read_short8 : zipRead (table shortKid8) 91503 = some (2,true) :=
  zipRead_scan shortKid8 91503 (patch_scan shortKid8 1 (by rfl))

def shortKid10 : Option (Option Move) := some (some ⟨false,true,4⟩)
theorem read_short10 : zipRead (table shortKid10) 91505 = some (2,true) :=
  zipRead_scan shortKid10 91505 (patch_scan shortKid10 3 (by rfl))

def shortKid14 : Option (Option Move) := some (some ⟨true,false,2⟩)
theorem read_short14 : zipRead (table shortKid14) 91503 = some (2,true) :=
  zipRead_scan shortKid14 91503 (patch_scan shortKid14 1 (by rfl))

def shortKid16 : Option (Option Move) := some (some ⟨true,false,4⟩)
theorem read_short16 : zipRead (table shortKid16) 91505 = some (2,true) :=
  zipRead_scan shortKid16 91505 (patch_scan shortKid16 3 (by rfl))

def shortKid20 : Option (Option Move) := some (some ⟨true,true,2⟩)
theorem read_short20 : zipRead (table shortKid20) 91503 = some (2,true) :=
  zipRead_scan shortKid20 91503 (patch_scan shortKid20 1 (by rfl))

/-- Eleven exact table/time matches, all other cases use the ordinary zipper. -/
def longRead (p : PartialMachine) (n : Nat) : Option Slot :=
  if n == 91502 && tableOK p (table none) then some (0,true)
  else if n == 4136170 && tableOK p (table kid1) then some (2,true)
  else if n == 4136170 && tableOK p (table kid5) then some (2,true)
  else if n == 4136174 && tableOK p (table kid22) then some (2,true)
  else if n == 91503 && tableOK p (table shortKid2) then some (2,true)
  else if n == 91505 && tableOK p (table shortKid4) then some (2,true)
  else if n == 91503 && tableOK p (table shortKid8) then some (2,true)
  else if n == 91505 && tableOK p (table shortKid10) then some (2,true)
  else if n == 91503 && tableOK p (table shortKid14) then some (2,true)
  else if n == 91505 && tableOK p (table shortKid16) then some (2,true)
  else if n == 91503 && tableOK p (table shortKid20) then some (2,true)
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
        · split
          · rename_i h
            simp only [Bool.and_eq_true,beq_iff_eq] at h
            obtain ⟨rfl,ht⟩ := h
            rw [tableOK_sound _ _ ht]
            exact read_short2.symm
          · split
            · rename_i h
              simp only [Bool.and_eq_true,beq_iff_eq] at h
              obtain ⟨rfl,ht⟩ := h
              rw [tableOK_sound _ _ ht]
              exact read_short4.symm
            · split
              · rename_i h
                simp only [Bool.and_eq_true,beq_iff_eq] at h
                obtain ⟨rfl,ht⟩ := h
                rw [tableOK_sound _ _ ht]
                exact read_short8.symm
              · split
                · rename_i h
                  simp only [Bool.and_eq_true,beq_iff_eq] at h
                  obtain ⟨rfl,ht⟩ := h
                  rw [tableOK_sound _ _ ht]
                  exact read_short10.symm
                · split
                  · rename_i h
                    simp only [Bool.and_eq_true,beq_iff_eq] at h
                    obtain ⟨rfl,ht⟩ := h
                    rw [tableOK_sound _ _ ht]
                    exact read_short14.symm
                  · split
                    · rename_i h
                      simp only [Bool.and_eq_true,beq_iff_eq] at h
                      obtain ⟨rfl,ht⟩ := h
                      rw [tableOK_sound _ _ ht]
                      exact read_short16.symm
                    · split
                      · rename_i h
                        simp only [Bool.and_eq_true,beq_iff_eq] at h
                        obtain ⟨rfl,ht⟩ := h
                        rw [tableOK_sound _ _ ht]
                        exact read_short20.symm
                      · rfl

#print axioms longRead_eq
end BB6.Agent10Raw108Long
