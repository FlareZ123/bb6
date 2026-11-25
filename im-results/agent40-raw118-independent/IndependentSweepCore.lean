import SweepPumping
namespace BB6Coverage.Agent40Independent
open BB6Coverage Agent31Pump Agent50Zipper

theorem rep_uniform (x : Bool) (k n : Nat) :
    rep (List.replicate k x) n = List.replicate (k*n) x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep, ih, List.replicate_append_replicate]; congr 1; simp [Nat.mul_succ, Nat.add_comm]

/-- Positive exact macro returns to any member of a family suffice; its
    parameters need not increase together, or even be monotone. -/
theorem closed_arbitrary (p : PartialMachine) (I : Z0 → Prop)
    (entry : ∃ t z, run0 p t ⟨0,[],[]⟩ = some z ∧ I z)
    (closed : ∀ z, I z → ∃ k z', 0 < k ∧ run0 p k z = some z' ∧ I z') :
    ∀ n, ∃ t z, n ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some z ∧ I z := by
  intro n
  induction n with
  | zero =>
    obtain ⟨t,z,h,hi⟩ := entry
    exact ⟨t,z,by omega,h,hi⟩
  | succ n ih =>
    obtain ⟨t,z,ht,h,hi⟩ := ih
    obtain ⟨k,z',hk,h',hi'⟩ := closed z hi
    exact ⟨t+k,z',by omega,join0 h h',hi'⟩

/-- The same original zipper-to-raw bridge as never_of_growth, but for
    an arbitrary positively recurrent set of section configurations. -/
theorem never_of_closed (p : PartialMachine) (I : Z0 → Prop)
    (entry : ∃ t z, run0 p t ⟨0,[],[]⟩ = some z ∧ I z)
    (closed : ∀ z, I z → ∃ k z', 0 < k ∧ run0 p k z = some z' ∧ I z')
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨t,z0,ht,hr,_⟩ := closed_arbitrary p I entry closed n
  have hz : (zrun p t start).map project = some z0 :=
    (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms rep_uniform
#print axioms closed_arbitrary
#print axioms never_of_closed
theorem rep_add (P : List Bool) (n k : Nat) :
    rep P (n+k) = rep P n ++ rep P k := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [Nat.succ_add, rep, ih, rep]; simp only [List.append_assoc]

end BB6Coverage.Agent40Independent
