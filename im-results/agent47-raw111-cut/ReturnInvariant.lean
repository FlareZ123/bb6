import SweepPumping

namespace BB6Coverage.Agent31Pump
open BB6Coverage

/-- A live invariant with a strictly positive return suffices for nonhalting.
    The return relation may be nondeterministic and have non-affine costs. -/
theorem never_of_return (p : PartialMachine) (I : Z0 → Prop)
    (entry : Nat) (z : Z0) (first : run0 p entry ⟨0,[],[]⟩ = some z)
    (hi : I z)
    (advance : ∀ c, I c → ∃ k d, 0 < k ∧ run0 p k c = some d ∧ I d)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let S := {c : Z0 // I c}
  have H (c : S) : ∃ k (d : S), 0 < k ∧ run0 p k c.val = some d.val := by
    obtain ⟨k,d,hk,hr,hd⟩ := advance c.val c.property
    exact ⟨k,⟨d,hd⟩,hk,hr⟩
  let cost (c : S) := Classical.choose (H c)
  let next (c : S) := Classical.choose (Classical.choose_spec (H c))
  have step (c : S) : 0 < cost c ∧ run0 p (cost c) c.val = some (next c).val :=
    Classical.choose_spec (Classical.choose_spec (H c))
  let seq : Nat → S := Nat.rec ⟨z,hi⟩ (fun _ c => next c)
  exact never_of_growth p (fun n => (seq n).val) entry
    (fun n => cost (seq n)) first
    (fun n => (step (seq n)).1) (fun n => (step (seq n)).2) m hm

#print axioms never_of_return
end BB6Coverage.Agent31Pump
