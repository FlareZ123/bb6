import Raw34Plan
namespace BB6.Agent50Raw34Plan
open BB6Coverage

theorem finiteHaltCheck_exact (p : PartialMachine) (n : Nat)
    (h : finiteHaltCheck p n = true) (m : Machine) (hm : compatible p m) : HaltsAfter m n := by
  cases he : finitePartialRun p n finiteBlank with
  | none => simp [finiteHaltCheck,he] at h
  | some c =>
    have hhalt : p (c.state,finiteTape c c.head) = some none := by
      simpa only [finiteHaltCheck,he,decide_eq_true_eq] using h
    have hr : run m n blank = some (embedFinRay c) := by
      simpa only [embedFinRay_blank] using finitePartialRun_sound p m hm finiteBlank c n he
    have hnone : m (c.state,finiteTape c c.head) = none := hm _ _ hhalt
    exact ⟨by simp [hr],by simp [run,hr,rawStep,readSlot,embedFinRay,hnone]⟩

def extendsTable (p q : PartialMachine) : Bool :=
  slots.all fun s => match p s with
    | none => true
    | some t => decide (q s = some t)

theorem extendsTable_sound (p q : PartialMachine) (h : extendsTable p q = true)
    (m : Machine) (hm : compatible q m) : compatible p m := by
  intro s t hs
  have hb := List.all_eq_true.mp h s (slots_complete s)
  have ht : q s = some t := by simpa [hs] using hb
  exact hm s t ht

#print axioms finiteHaltCheck_exact
#print axioms extendsTable_sound
end BB6.Agent50Raw34Plan
