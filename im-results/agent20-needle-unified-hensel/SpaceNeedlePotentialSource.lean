import SpaceNeedleClosed
import IndexPotential
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20NeedlePotentialSource
open BB6.Agent48.SpaceNeedle
open BB6.Agent20IndexPotential
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- A genuine high-level source chain in which every edge has the same
    dyadic valuation w; the unshifted source counter d becomes b=d+2. -/
inductive SourceChain (w : Nat) : Nat → Nat → Nat → Prop
  | zero (d : Nat) : SourceChain w 0 d d
  | step {k e f : Nat} (q : Nat)
      (he : highLevelNext (.N (oddTower q w)) = some (.N e))
      (tail : SourceChain w k (oddTower q w) f) :
      SourceChain w (k+1) e f

private theorem target_of_successor (w q e : Nat)
  (he : highLevelNext (.N (oddTower q w)) = some (.N e)) :
  e = oddTower q w + w + 3*(q+1) := by
  have hs : highLevelNext (.N (oddTower q w)) =
       some (.N (oddTower q w + w + 3*(q+1))) :=
    (highLevelNext_iff_oddTower _ _).mpr ⟨q,w,rfl,rfl⟩
  rw [hs] at he
  simp only [Option.some.injEq, HighLevelState.N.injEq] at he
  omega

private theorem general_edge_algebra (X w q : Nat) (hw : 2≤w) :
  2*X*(X*(2*q+3)+w+3*(q+1)) =
  (2*X+3)*(X*(2*q+3))+X*(2*w-3) := by
  have ht : 2*w-3+3=2*w := by omega
  have hm : X*(2*w-3)+3*X=2*(X*w) := by
    calc
      X*(2*w-3)+3*X = X*(2*w-3+3) := by rw [Nat.mul_add]; omega
      _ = X*(2*w) := by rw [ht]
      _ = 2*(X*w) := by ac_rfl
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_succ]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at hm ⊢
  omega

private theorem source_edge (w q e : Nat) (hw : 2≤w)
  (he : highLevelNext (.N (oddTower q w)) = some (.N e)) :
  2^(w+1)*(e+2) = (2^(w+1)+3)*(oddTower q w+2) +
      2^w*(2*w-3) := by
  have hn := target_of_successor w q e he
  have ho := oddTower_factor q w
  rw [hn]
  have hs : oddTower q w+w+3*(q+1)+2 = 2^w*(2*q+3)+w+3*(q+1) := by
    omega
  rw [hs,ho,Nat.pow_succ']
  exact general_edge_algebra (2^w) w q hw

private theorem source_to_affine {w L D d : Nat}
  (edge : ∀ q e, highLevelNext (.N (oddTower q w)) = some (.N e) →
    L*(e+2)=D*(oddTower q w+2)+d)
  {k e f : Nat} (hs : SourceChain w k e f) :
  Chain L D d k (e+2) (f+2) := by
  induction hs with
  | zero x => exact .zero (x+2)
  | @step j e f q he ht ih => exact .step (edge q e he) ih

private theorem pow_two_plus_three_coprime (w : Nat) :
  (2^(w+1)+3).Coprime (2^(w+1)) := by
  have h : (3:Nat).Coprime (2^(w+1)) :=
    (by decide : (3:Nat).Coprime 2).pow_right (w+1)
  apply Nat.coprime_iff_gcd_eq_one.mpr
  change (2^(w+1)+3).gcd (2^(w+1))=1
  rw [Nat.add_comm (2^(w+1)) 3]
  rw [Nat.gcd_add_self_left]
  exact h.gcd_eq_one

/-- Uniform source theorem for ALL fixed dyadic valuations w>=2:
    a length-k all-w reverse chain requires approach to the negative
    2^w*(3-2w)/3 fixed point modulo (2^(w+1)+3)^k. -/
theorem allValuationsSource {w k e f : Nat} (hw : 2≤w)
  (hs : SourceChain w k e f) :
  (2^(w+1)+3)^k ∣ 3*(e+2)+2^w*(2*w-3) := by
  have hcore := source_to_affine (fun q e he => source_edge w q e hw he) hs
  exact chainDivisibility (by rfl) (pow_two_plus_three_coprime w) hcore

/-- Specialization to the 19-adic valuation-three family. -/
theorem valuationThreeSource {k e f : Nat} (h : SourceChain 3 k e f) :
  19^k ∣ 3*(e+2)+24 := by
  simpa using allValuationsSource (w:=3) (by decide) h

/-- Specialization to the 35-adic valuation-four family. -/
theorem valuationFourSource {k e f : Nat} (h : SourceChain 4 k e f) :
  35^k ∣ 3*(e+2)+80 := by
  simpa using allValuationsSource (w:=4) (by decide) h

/-- Specialization to the 67-adic valuation-five family. -/
theorem valuationFiveSource {k e f : Nat} (h : SourceChain 5 k e f) :
  67^k ∣ 3*(e+2)+224 := by
  simpa using allValuationsSource (w:=5) (by decide) h

/-- Exact original-source transport of the affine potential along
    every length-k fixed-valuation inverse history. -/
theorem allValuationsPotential {w k e f : Nat} (hw : 2≤w)
    (hs : SourceChain w k e f) :
    (2^(w+1))^k * (3*(e+2)+2^w*(2*w-3)) =
    (2^(w+1)+3)^k * (3*(f+2)+2^w*(2*w-3)) := by
  exact chainPotential (by rfl)
    (source_to_affine (fun q e he => source_edge w q e hw he) hs)

#print axioms allValuationsPotential

#print axioms allValuationsSource
#print axioms valuationThreeSource
#print axioms valuationFourSource
#print axioms valuationFiveSource
end BB6.Agent20NeedlePotentialSource
