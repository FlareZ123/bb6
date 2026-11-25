import Raw121BinarySweep
import Raw121TripleSweep
import Raw121TripleCounter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw121Exceptions
open BB6Coverage BB6Coverage.Agent31Pump

/-- Convert a closed positive-time invariant into a single indexed infinite run. -/
theorem family_of_invariant (p : PartialMachine) (I : Z0 → Prop) (z : Z0)
    (hz : I z) (h : ∀ c, I c → ∃ d k, 0<k ∧ run0 p k c = some d ∧ I d) :
    ∃ f : Nat → Z0, ∃ cost : Nat → Nat,
      f 0 = z ∧ (∀ n, 0 < cost n) ∧
      (∀ n, run0 p (cost n) (f n) = some (f (n+1))) := by
  classical
  let next (c : {c : Z0 // I c}) : {c : Z0 // I c} :=
    ⟨Classical.choose (h c.val c.property),
      (Classical.choose_spec (Classical.choose_spec (h c.val c.property))).2.2⟩
  let k (c : {c : Z0 // I c}) : Nat := Classical.choose (Classical.choose_spec (h c.val c.property))
  let f : Nat → {c : Z0 // I c} := fun n => Nat.rec ⟨z,hz⟩ (fun _ c => next c) n
  refine ⟨fun n => (f n).val, fun n => k (f n), rfl, ?_, ?_⟩
  · intro n
    exact (Classical.choose_spec (Classical.choose_spec (h (f n).val (f n).property))).1
  · intro n
    exact (Classical.choose_spec (Classical.choose_spec (h (f n).val (f n).property))).2.1

open BB6.Agent11Raw121BinarySweep in
theorem binary_family (v : V) : ∃ f : Nat → Z0, ∃ k : Nat → Nat,
    run0 (table v) 8 ⟨0,[],[]⟩ = some (f 0) ∧ (∀ n, 0 < k n) ∧
    (∀ n, run0 (table v) (k n) (f n) = some (f (n+1))) := by
  let I := fun c => ∃ n j R, c = fam n j R
  have hc : ∀ c, I c → ∃ d k, 0<k ∧ run0 (table v) k c = some d ∧ I d := by
    intro c hc
    obtain ⟨n,j,R,he⟩ := hc
    subst c
    obtain ⟨j',R',k,hk,hr⟩ := grow v n j R
    exact ⟨_,k,hk,hr,n+1,j',R',rfl⟩
  obtain ⟨f,k,h0,hk,hr⟩ := family_of_invariant (table v) I (fam 0 0 []) ⟨0,0,[],rfl⟩ hc
  exact ⟨f,k,(entry v).trans (congrArg some h0.symm),hk,hr⟩

open BB6.Agent11Raw121TripleSweep in
theorem triple_family : ∃ f : Nat → Z0, ∃ k : Nat → Nat,
    run0 table 25 ⟨0,[],[]⟩ = some (f 0) ∧ (∀ n, 0 < k n) ∧
    (∀ n, run0 table (k n) (f n) = some (f (n+1))) := by
  let I := fun c => ∃ n j R, c = fam n j R
  have hc : ∀ c, I c → ∃ d k, 0<k ∧ run0 table k c = some d ∧ I d := by
    intro c hc
    obtain ⟨n,j,R,he⟩ := hc
    subst c
    obtain ⟨j',R',k,hk,hr⟩ := grow n j R
    exact ⟨_,k,hk,hr,n+1,j',R',rfl⟩
  obtain ⟨f,k,h0,hk,hr⟩ := family_of_invariant table I (fam 0 0 [true]) ⟨0,0,[true],rfl⟩ hc
  exact ⟨f,k,entry.trans (congrArg some h0.symm),hk,hr⟩

open BB6.Agent11Raw121TripleCounter in
theorem counter_family : ∃ f : Nat → Z0, ∃ k : Nat → Nat,
    run0 table 8 ⟨0,[],[]⟩ = some (f 0) ∧ (∀ n, 0 < k n) ∧
    (∀ n, run0 table (k n) (f n) = some (f (n+1))) := by
  obtain ⟨f,k,h0,hk,hr⟩ := family_of_invariant table Inv (X 1 false []) (Inv.x 1 false [] (Good.terminal 0)) (fun _ h => closed h)
  exact ⟨f,k,entry.trans (congrArg some h0.symm),hk,hr⟩

open BB6.Agent11Raw121BinarySweep in
theorem binary_never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  obtain ⟨f,k,h0,hk,hr⟩ := binary_family v
  exact never_of_growth (table v) f 8 k h0 hk hr m hm

open BB6.Agent11Raw121TripleSweep in
theorem triple_never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  obtain ⟨f,k,h0,hk,hr⟩ := triple_family
  exact never_of_growth table f 25 k h0 hk hr m hm

open BB6.Agent11Raw121TripleCounter in
theorem counter_never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  obtain ⟨f,k,h0,hk,hr⟩ := counter_family
  exact never_of_growth table f 8 k h0 hk hr m hm

#print axioms binary_family
#print axioms triple_family
#print axioms counter_family
#print axioms binary_never
#print axioms triple_never
#print axioms counter_never
end BB6.Agent11Raw121Exceptions
