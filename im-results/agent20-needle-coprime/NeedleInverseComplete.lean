import NeedleValHalf
import Lean.Elab.Tactic.Omega

namespace NeedleInverse

def den (v : Nat) : Nat := 2^(v+1)+3
def bias (v : Nat) : Nat := 3*2^v+v+3

def equation (q v K : Nat) : Prop :=
  2^v*(2*q+3)+v+3*(q+1)=2^K

instance (q v K : Nat) : Decidable (equation q v K) := by
  unfold equation
  infer_instance

theorem affine_identity (q v : Nat) :
    2^v*(2*q+3)+v+3*(q+1)=den v*q+bias v := by
  simp [den,bias,Nat.pow_succ', Nat.add_mul, Nat.mul_add,
    Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem equation_affine (q v K : Nat) :
    equation q v K ↔ 2^K=den v*q+bias v := by
  dsimp [equation]
  rw [affine_identity]
  exact eq_comm

private theorem den_pos (v : Nat) : 0 < den v := by simp [den]

theorem unique_predecessor_at_valuation (q r v K : Nat)
    (hq : equation q v K) (hr : equation r v K) : q=r := by
  have hq' := (equation_affine q v K).mp hq
  have hr' := (equation_affine r v K).mp hr
  have h : den v*q = den v*r := by omega
  exact Nat.mul_left_cancel (den_pos v) h

def candidateQ (v K : Nat) : Nat :=
  (2^K-bias v)/den v

theorem eq_implies_candidate (q v K : Nat) (h : equation q v K) :
    candidateQ v K=q := by
  have ha := (equation_affine q v K).mp h
  have hminus : 2^K-bias v=den v*q := by omega
  dsimp [candidateQ]
  rw [hminus]
  exact Nat.mul_div_cancel_left q (den_pos v)

def candidate (v K : Nat) : Option Nat :=
  if equation (candidateQ v K) v K then some (candidateQ v K) else none

theorem candidate_correct (q v K : Nat) :
    candidate v K=some q ↔ equation q v K := by
  constructor
  · intro h
    unfold candidate at h
    split at h
    · case isTrue hc =>
      have hq : candidateQ v K=q := by simpa using h
      simpa [←hq] using hc
    · contradiction
  · intro heq
    have hc := eq_implies_candidate q v K heq
    simp only [candidate, hc, heq, ite_true]

theorem candidate_bound (q v K : Nat) (h : candidate v K=some q) :
    2*v < K :=
  NeedleValHalf.predecessor_valuation_strict q v K ((candidate_correct q v K).mp h)

theorem exact_finite_search (q v K : Nat) :
    equation q v K ↔ v < (K+1)/2 ∧ candidate v K=some q := by
  constructor
  · intro h
    have hv := NeedleValHalf.predecessor_valuation_strict q v K h
    refine ⟨?_, (candidate_correct q v K).mpr h⟩
    omega
  · intro ⟨_,h⟩
    exact (candidate_correct q v K).mp h

theorem original_source_equation_iff (q v k : Nat) :
    equation q v (k+1) ↔
      2^(k+2)+3=(2^(v+1)+3)*(2*q+3)+2*v := by
  dsimp [equation]
  have hk : (2:Nat)^(k+2)=2*2^(k+1) := by
    rw [show k+2=(k+1)+1 by omega, Nat.pow_succ']
  have hv : (2:Nat)^(v+1)=2*2^v := by rw [Nat.pow_succ']
  rw [hk,hv]
  have hmul : (2*2^v+3)*(2*q+3) =
      2*(2^v*(2*q+3))+3*(2*q+3) := by
    simp [Nat.add_mul, Nat.mul_assoc]
  rw [hmul]
  omega

def allTerminalPredecessors (K : Nat) : List (Nat × Nat) :=
  (List.range ((K+1)/2)).filterMap fun v =>
    (candidate v K).map fun q => (v,q)

theorem at_most_half_fanin (K : Nat) :
    (allTerminalPredecessors K).length ≤ (K+1)/2 := by
  simpa only [allTerminalPredecessors, List.length_range] using
    (List.length_filterMap_le
      (fun v => (candidate v K).map fun q => (v,q)) (List.range ((K+1)/2)))

theorem allTerminalPredecessors_spec (q v K : Nat) :
    (v,q) ∈ allTerminalPredecessors K ↔ equation q v K := by
  constructor
  · intro h
    obtain ⟨v',hsize,hmap⟩ := List.mem_filterMap.mp h
    cases hc : candidate v' K with
    | none => simp [hc] at hmap
    | some q' =>
      have hp : (v',q')=(v,q) := by
        simpa [hc] using hmap
      obtain ⟨hv,hq⟩ := Prod.mk.inj hp
      subst v'
      subst q'
      exact (candidate_correct q v K).mp hc
  · intro heq
    obtain ⟨hv,hc⟩ := (exact_finite_search q v K).mp heq
    apply List.mem_filterMap.mpr
    refine ⟨v, List.mem_range.mpr hv, ?_⟩
    simp [hc]

#eval allTerminalPredecessors 4
#eval allTerminalPredecessors 9
#eval allTerminalPredecessors 12
#eval allTerminalPredecessors 13
#print axioms at_most_half_fanin
#print axioms allTerminalPredecessors_spec
#print axioms exact_finite_search
#print axioms unique_predecessor_at_valuation
end NeedleInverse
