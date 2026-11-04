import One64Ten
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

private theorem pow_m_bound (r : Nat) :
    3*(r+3)+80 ≤ 2^(2*(r+3)+3) := by
  induction r with
  | zero => decide
  | succ r ih =>
      have he : 2*((r+1)+3)+3 = (2*(r+3)+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem pow_m_div64 (m : Nat) (hm : 3≤m) :
    2^(2*m+3)=64*2^(2*m-3) := by
  have he : 2*m+3=(2*m-3)+6 := by omega
  rw [he,Nat.pow_add]
  have hp : (2:Nat)^6=64 := by decide
  rw [hp]
  ac_rfl

/-- Every exact original first-family immediate stopping input indexed
    by m ≡ 38 (mod 64) is unreachable from blank Machine C, at all times.
    This follows from the stronger source cylinder (1,64u+10) exclusion. -/
theorem first_family_m38_mod64_excluded (r k time : Nat)
    (hk : k+3*(64*r+38)+4=2^(2*(64*r+38)+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (1,k) := by
  let m := 64*r+38
  have hm : 3≤m := by dsimp [m]; omega
  have hp := pow_m_div64 m hm
  have hb := pow_m_bound (35+64*r)
  have he : 35+64*r+3=m := by dsimp [m]; omega
  rw [he] at hb
  have hk' : k+3*m+4=2^(2*m+3) := by simpa [m] using hk
  have hk74 : 74≤k := by omega
  have hmod : k%64=10 := by
    dsimp [m] at hp hk'
    omega
  let u := k/64
  have hu : 1≤u := by dsimp [u]; omega
  have heq : k=64*u+10 := by
    dsimp [u]
    have hdiv := Nat.mod_add_div k 64
    omega
  rw [heq]
  exact blank_no_one_64u10 u time hu

#print axioms first_family_m38_mod64_excluded
end BB6.Agent15
