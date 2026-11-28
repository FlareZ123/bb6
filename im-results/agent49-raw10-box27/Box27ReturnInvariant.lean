import SweepPumping
namespace BB6Coverage.Agent31Pump
open BB6Coverage Agent50Zipper

/-- An inductive return relation suffices for infinite execution; the next
return need not be an affine function of a numerical family index. -/
theorem never_of_return (p : PartialMachine) (I : Z0 → Prop)
    (entry : Nat) (first : ∃ z, I z ∧ run0 p entry ⟨0,[],[]⟩ = some z)
    (advance : ∀ z, I z → ∃ t z', 0 < t ∧ I z' ∧ run0 p t z = some z')
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t z, k ≤ t ∧ I z ∧ run0 p t ⟨0,[],[]⟩ = some z := by
    intro k
    induction k with
    | zero =>
      obtain ⟨z,hI,hz⟩ := first
      exact ⟨entry,z,by omega,hI,hz⟩
    | succ k ih =>
      obtain ⟨t,z,ht,hI,hz⟩ := ih
      obtain ⟨u,z',hu,hI',hz'⟩ := advance z hI
      exact ⟨t+u,z',by omega,hI',join0 hz hz'⟩
  intro n
  obtain ⟨t,u,ht,_,hr⟩ := arbitrary n
  have hz : (zrun p t start).map project = some u := (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms never_of_return
end BB6Coverage.Agent31Pump
