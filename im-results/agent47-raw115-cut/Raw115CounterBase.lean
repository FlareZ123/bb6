import SweepPumping

namespace BB6Coverage.Agent31Pump.Raw115CounterBase
open BB6Coverage Agent50Zipper

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => simp [Nat.succ_add,rep,ih,List.append_assoc]

theorem rep_group (P : List Bool) (k n : Nat) : rep (rep P k) n = rep P (k*n) := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [rep,ih,Nat.mul_succ,Nat.add_comm (k*n) k,rep_add]

/-- A positive-cost return on a preserved parameter domain is sufficient;
    no globally affine single-parameter growth hypothesis is needed. -/
theorem never_of_returns (p : PartialMachine) (family : Nat → Z0) (good : Nat → Prop)
    (seed : Nat) (hseed : good seed) (entry : Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some (family seed))
    (next : ∀ b, good b → ∃ b' t, good b' ∧ 0<t ∧ run0 p t (family b) = some (family b'))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t b, k ≤ t ∧ good b ∧ run0 p t ⟨0,[],[]⟩ = some (family b) := by
    intro k
    induction k with
    | zero => exact ⟨entry,seed,by omega,hseed,first⟩
    | succ k ih =>
      obtain ⟨t,b,ht,hb,hr⟩ := ih
      obtain ⟨b',s,hb',hs,hstep⟩ := next b hb
      exact ⟨t+s,b',by omega,hb',join0 hr hstep⟩
  intro n
  obtain ⟨t,b,ht,_,hr⟩ := arbitrary n
  have hz : (zrun p t start).map project = some (family b) :=
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

#print axioms never_of_returns
end BB6Coverage.Agent31Pump.Raw115CounterBase
