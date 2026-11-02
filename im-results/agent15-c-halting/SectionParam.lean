import SectionPower
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

private theorem pow_four_lower (m : Nat) : 3*m+4 ≤ 2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2 = (2*m+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide] at *
      omega

private theorem pow_eight_lower (m : Nat) : 3*m+8 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3 = (2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide] at *
      omega

private theorem low_iff (k : Nat) :
    (4≤k ∧ ∃ n, 2*k+3*n+8=2^(n+4)) ↔
    ∃ m, k+3*m+4=2^(2*m+3) := by
  constructor
  · rintro ⟨hk,n,hn⟩
    have he : 2^(n+4)%2=0 := by
      have e : n+4=(n+3)+1 := by omega
      rw [e,Nat.pow_succ]
      omega
    have hnEven : n%2=0 := by omega
    let m := n/2
    have hm : n=2*m := by dsimp [m]; omega
    refine ⟨m,?_⟩
    rw [hm] at hn
    have he : 2*m+4=(2*m+3)+1 := by omega
    rw [he,Nat.pow_succ] at hn
    omega
  · rintro ⟨m,hm⟩
    have hb := pow_eight_lower m
    have hk : 4≤k := by omega
    refine ⟨hk,2*m,?_⟩
    have he : 2*m+4=(2*m+3)+1 := by omega
    rw [he,Nat.pow_succ]
    omega

private theorem high_iff (a k : Nat) :
    (2≤a ∧ 1≤k ∧ a<2*k ∧ a%2=1 ∧
      ∃ n, 2*k+a+3*n+4=2^(n+1)*(a+3)) ↔
    (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3)) := by
  constructor
  · rintro ⟨ha,hk,har,hodd,n,hn⟩
    have he : (2^(n+1)*(a+3))%2=0 := by
      rw [Nat.pow_succ]
      simp [Nat.mul_assoc, Nat.mul_comm]
    have hnOdd : n%2=1 := by omega
    let j := (a-3)/2
    let m := n/2
    have hj : a=2*j+3 := by dsimp [j]; omega
    have hm : n=2*m+1 := by dsimp [m]; omega
    refine ⟨j,m,hj,?_⟩
    rw [hj,hm] at hn
    have h2 : (2*m+1)+1=2*m+2 := by omega
    rw [h2] at hn
    have hscale : 2^(2*m+2)*(2*j+3+3)=2*(2^(2*m+2)*(j+3)) := by
      have heq : 2*j+3+3=2*(j+3) := by omega
      rw [heq]
      ac_rfl
    rw [hscale] at hn
    omega
  · rintro ⟨j,m,ha,hm⟩
    subst a
    have hp := pow_four_lower m
    have p4 : 4≤2^(2*m+2) := by omega
    have hLeft : 4*j ≤ 2^(2*m+2)*j := Nat.mul_le_mul_right j p4
    have hRight : 3*(3*m+4) ≤ 3*2^(2*m+2) := Nat.mul_le_mul_left 3 hp
    have hprod : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
      simp [Nat.mul_add, Nat.mul_comm]
    rw [hprod] at hm
    have hk : 1≤k := by omega
    have har : 2*j+3<2*k := by omega
    refine ⟨by omega, hk,har,by omega,2*m+1,?_⟩
    have htwo : (2*m+1)+1=2*m+2 := by omega
    rw [htwo]
    have hscale : 2^(2*m+2)*(2*j+3+3)=2*(2^(2*m+2)*(j+3)) := by
      have heq : 2*j+3+3=2*(j+3) := by omega
      rw [heq]
      ac_rfl
    rw [hscale]
    omega

/-- Closed, nonrecursive parameterization of the full C section halting locus. -/
theorem section_halts_iff_parametric (a k : Nat) :
    secNext (a,k)=none ↔
      (a=0 ∧ k=0) ∨
      (a=1 ∧ ∃ m, k+3*m+4=2^(2*m+3)) ∨
      (∃ j m, a=2*j+3 ∧ k+j+3*m+5=2^(2*m+2)*(j+3)) := by
  rw [section_halts_iff_diophantine]
  simp only [low_iff,high_iff]

#print axioms section_halts_iff_parametric
end BB6.Agent15
