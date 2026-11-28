import Raw40CrossingLeaves
import Raw40LongCycles

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40Exceptional28
open BB6Coverage

/-- The 28 previously certified one-hole exceptional Raw40 sources.
    They are distinct literal cylinders, not a claim that their six-hole
    parent or the complete 6-state search has been covered. -/
def bank : List PartialMachine := [
  BB6Coverage.Agent42Raw40Crossing.C1RBM71.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM74.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM75.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM153.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM154.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM155.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM156.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM157.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM158.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM159.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM160.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM161.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM185.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM186.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM188.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM189.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM190.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM191.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM192.table,
  BB6Coverage.Agent42Raw40Crossing.C1RBM193.table,
  BB6Coverage.Agent42Raw40Crossing.C0RDM71.table,
  BB6Coverage.Agent42Raw40Crossing.C0RDM73.table,
  BB6Coverage.Agent42Raw40Crossing.C1LAM156.table,
  BB6.Agent42Raw40LongCycles.C1LCM201.table,
  BB6.Agent42Raw40LongCycles.C1RCM160.table,
  BB6.Agent42Raw40LongCycles.C1RBM54.table,
  BB6.Agent42Raw40LongCycles.C0RDM150.table,
  BB6.Agent42Raw40LongCycles.C1LAM161.table
]

theorem bank_size : bank.length = 28 := by decide

/-- A finite, syntactic conflict between sparse tables: their common
    assigned slots demand different transitions. -/
def clash (p q : PartialMachine) : Bool :=
  (List.finRange 6).any fun a =>
    ([false, true] : List Bool).any fun b =>
      match p (a,b), q (a,b) with
      | some x, some y => decide (x ≠ y)
      | _, _ => false

theorem clash_sound {p q : PartialMachine} (hc : clash p q = true)
    (m : Machine) (hp : compatible p m) (hq : compatible q m) : False := by
  unfold clash at hc
  obtain ⟨a, _, ha⟩ := List.any_eq_true.mp hc
  obtain ⟨b, _, hb⟩ := List.any_eq_true.mp ha
  cases hx : p (a,b) with
  | none => simp [hx] at hb
  | some x =>
    cases hy : q (a,b) with
    | none => simp [hx,hy] at hb
    | some y =>
      have hxy : x ≠ y := of_decide_eq_true (by simpa [hx,hy] using hb)
      exact hxy ((hp (a,b) x hx).symm.trans (hq (a,b) y hy))

def pairwiseCheck : List PartialMachine → Bool
  | [] => true
  | p::ps => ps.all (clash p) && pairwiseCheck ps

theorem pairwiseCheck_sound : ∀ xs, pairwiseCheck xs = true →
    List.Pairwise (fun p q : PartialMachine =>
      ∀ m : Machine, compatible p m → compatible q m → False) xs := by
  intro xs
  induction xs with
  | nil => intro _; exact List.Pairwise.nil
  | cons p ps ih =>
    intro h
    have hh : ps.all (clash p) = true ∧ pairwiseCheck ps = true := by
      exact Bool.and_eq_true.mp (by simpa only [pairwiseCheck] using h)
    apply List.Pairwise.cons
    · intro q hq m hp hqm
      exact clash_sound (List.all_eq_true.mp hh.1 q hq) m hp hqm
    · exact ih hh.2

theorem checked_disjointness : pairwiseCheck bank = true := by decide +kernel

/-- No one total machine lies in two distinct entries of this bank.
    This is constructive, not an assumption of disjointness. -/
theorem all_pairwise_disjoint :
    List.Pairwise (fun p q : PartialMachine =>
      ∀ m : Machine, compatible p m → compatible q m → False) bank :=
  pairwiseCheck_sound bank checked_disjointness

/-- Every complete machine matching any of the 28 input cylinders
    has an infinite authentic blank execution. -/
theorem all_never (p : PartialMachine) (hp : p ∈ bank)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  simp only [bank, List.mem_cons, List.mem_singleton] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM71.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM74.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM75.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM153.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM154.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM155.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM156.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM157.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM158.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM159.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM160.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM161.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM185.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM186.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM188.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM189.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM190.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM191.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM192.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1RBM193.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C0RDM71.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C0RDM73.never m hm
  · subst p
    exact BB6Coverage.Agent42Raw40Crossing.C1LAM156.never m hm
  · subst p
    exact BB6.Agent42Raw40LongCycles.C1LCM201.never m hm
  · subst p
    exact BB6.Agent42Raw40LongCycles.C1RCM160.never m hm
  · subst p
    exact BB6.Agent42Raw40LongCycles.C1RBM54.never m hm
  · subst p
    exact BB6.Agent42Raw40LongCycles.C0RDM150.never m hm
  · subst p
    exact BB6.Agent42Raw40LongCycles.C1LAM161.never m hm

/-- A single original-source certificate for a pairwise-disjoint finite
    family of 28 nonhalting cylinders. The soundness of each crossing
    recurrence is imported from the generic temporal transcript proof. -/
theorem certificate :
    bank.length = 28 ∧
    List.Pairwise (fun p q : PartialMachine =>
      ∀ m : Machine, compatible p m → compatible q m → False) bank ∧
    (∀ p ∈ bank, ∀ m, compatible p m → NeverHalts m) :=
  ⟨bank_size, all_pairwise_disjoint, all_never⟩

#print axioms certificate
end BB6.Agent42Raw40Exceptional28
