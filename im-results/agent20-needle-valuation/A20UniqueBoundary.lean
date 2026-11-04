import A20NeedleGap
import Lean.Elab.Tactic.Omega

namespace NeedleGap

private theorem pow_two_ge (v : Nat) : v ≤ 2^v := by
  induction v with
  | zero => decide
  | succ v ih =>
    rw [Nat.pow_succ]
    have hp : 0 < (2:Nat)^v := Nat.pow_pos (by decide)
    omega

/-- Equality in the sharp lower bound is uniquely realized at valuation six. -/
theorem gap_equality_unique (q v K : Nat)
    (h : 2^v*(2*q+3)+v+3*(q+1)=2^K)
    (he : K=2*v+1) : v=6 ∧ q=61 := by
  subst K
  have hv : 2 ≤ v := by
    by_cases hv0 : 2 ≤ v
    · exact hv0
    · have hhcases : v=0 ∨ v=1 := by omega
      rcases hhcases with h0 | h1
      · subst v; simp at h; omega
      · subst v; simp at h; omega
  let B := 2^v
  let D := 2*B+3
  have hp : (2:Nat)^(2*v+1) = 2*(B*B) := by
    dsimp [B]
    calc
      (2:Nat)^(2*v+1) = 2^((v+v)+1) := by congr 1; omega
      _ = (2^v * 2^v)*2 := by rw [Nat.pow_succ,Nat.pow_add]
      _ = 2*(2^v*2^v) := by ac_rfl
  rw [hp] at h
  change B*(2*q+3)+v+3*(q+1)=2*(B*B) at h
  have hb : (2*B+3)*(q+3) = 2*(B*q)+3*q+6*B+9 := by
    simp only [Nat.add_mul,Nat.mul_add]
    have h1 : (2*B)*q=2*(B*q) := by ac_rfl
    have h2 : (2*B)*3=6*B := by omega
    rw [h1,h2]
    omega
  have hc : (2*B+3)*B = 2*(B*B)+3*B := by
    simp only [Nat.add_mul]
    have h1 : (2*B)*B=2*(B*B) := by ac_rfl
    rw [h1]
  have ha : B*(2*q+3) = 2*(B*q)+3*B := by
    simp only [Nat.mul_add]
    have h1 : B*(2*q)=2*(B*q) := by ac_rfl
    rw [h1]
    omega
  have hkey : D*(q+3)+v = D*B+6 := by
    dsimp [D]
    rw [hb,hc]
    rw [ha] at h
    omega
  have hmod : v%D=6%D := by
    have hm := congrArg (fun x : Nat => x%D) hkey
    simpa [Nat.add_mod,Nat.mul_mod] using hm
  have hvsmall : v < D := by
    have hpow := pow_two_ge v
    dsimp [D,B]
    omega
  have h6small : 6 < D := by
    have hpow : 4 ≤ 2^v := by
      have hp := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hv
      simpa using hp
    dsimp [D,B]
    omega
  rw [Nat.mod_eq_of_lt hvsmall, Nat.mod_eq_of_lt h6small] at hmod
  constructor
  · exact hmod
  · have hv6 : v=6 := hmod
    subst v
    dsimp [B] at h
    omega

theorem gap_strict_except_unique (q v K : Nat)
    (h : 2^v*(2*q+3)+v+3*(q+1)=2^K)
    (hne : v ≠ 6 ∨ q ≠ 61) :
    2*v+2 ≤ K := by
  by_cases hk : 2*v+2 ≤ K
  · exact hk
  · have hmin := gap_all q v K h
    have he : K=2*v+1 := by omega
    obtain ⟨hv,hq⟩ := gap_equality_unique q v K h he
    rcases hne with hn|hn
    · exact False.elim (hn hv)
    · exact False.elim (hn hq)

#print axioms gap_equality_unique
#print axioms gap_strict_except_unique
end NeedleGap
