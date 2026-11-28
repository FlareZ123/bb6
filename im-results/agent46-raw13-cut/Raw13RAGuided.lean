import Raw13Coupled6OneRAPacked
namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
open BB6Coverage Agent31Pump Raw13Coupled6OneRAHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

inductive Instr where
 | raw (n : Nat)
 | fill (j : Nat) (w : PWord)
 | one (k : Nat) (w : PWord)

def guidedStep (z : PZ) : Instr → Option (Nat × PZ)
 | .raw n => do
    let u ← runP n z
    return (n,u)
 | .fill j w => fastFillP z j w
 | .one k w => fastOneP z k w

theorem guidedStep_sound {z : PZ} {i : Instr} {n : Nat} {out : PZ} (h : guidedStep z i=some (n,out)) : PackedOK z n out := by
  cases i with
  | raw k =>
    unfold guidedStep at h
    cases hr : runP k z with
    | none => simp [hr] at h
    | some u => simp only [hr] at h; cases h; exact packed_raw hr
  | fill j w => exact fastFillP_sound h
  | one k w => exact fastOneP_sound h

def guidedReplay : List Instr → PZ → Option (Nat × PZ)
 | [],z => some (0,z)
 | i::is,z => do
   let (a,u) ← guidedStep z i
   let (b,v) ← guidedReplay is u
   return (a+b,v)

theorem guidedReplay_sound {is : List Instr} {z : PZ} {n : Nat} {out : PZ} (h : guidedReplay is z=some (n,out)) : PackedOK z n out := by
  induction is generalizing z n out with
  | nil => cases h; intro a ha; exact ⟨a,rfl,ha⟩
  | cons i is ih =>
    cases hm : guidedStep z i with
    | none => simp [guidedReplay,hm] at h
    | some a =>
      obtain ⟨t,u⟩ := a
      cases hr : guidedReplay is u with
      | none => simp [guidedReplay,hm,hr] at h
      | some b =>
        obtain ⟨s,v⟩ := b
        simp [guidedReplay,hm,hr] at h
        obtain ⟨rfl,rfl⟩ := h
        exact packed_join (guidedStep_sound hm) (ih hr)

#print axioms guidedReplay_sound
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
