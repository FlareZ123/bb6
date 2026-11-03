import OddSliver
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem four_double_large (m : Nat) (hm : 1≤m) : 2*(m+1)≤4^m := by
  induction m with
  | zero => omega
  | succ m ih =>
      rw [Nat.pow_succ]
      by_cases hz : m=0
      · subst m; decide
      · have hh := ih (by omega)
        omega

/-- Four indexed infinite parameter rectangles of the authentic higher
    Machine C halting equation are in the true blank-forbidden wedge.
    This is a real full-time reachability exclusion, not merely image-counting. -/
theorem high_halt_sliver_mod16_unreachable (j m k time : Nat)
    (hclass : (j%16=7 ∧ m%16=15) ∨
              (j%16=15 ∧ m%16=7) ∨
              (j%16=3 ∧ m%16=3) ∨
              (j%16=11 ∧ m%16=11))
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (2*j+3,k) := by
  have hm : 1≤m := by rcases hclass with h|h|h|h <;> omega
  have hj : 3≤j := by rcases hclass with h|h|h|h <;> omega
  let P := 2^(2*m+2)
  have hP : P=4*4^m := by
    dsimp [P]
    rw [Nat.pow_add]
    have hdouble : 2^(2*m)=4^m := by
      calc
        2^(2*m)=(2^2)^m := Nat.pow_mul (2:Nat) 2 m
        _=4^m := by simp
    rw [hdouble,show (2:Nat)^2=4 by decide]
    ac_rfl
  have hPbound : 8*(m+1)≤P := by
    rw [hP]
    have hh := four_double_large m hm
    omega
  have hPone : 1≤P := by omega
  have hmult : j≤P*j := by
    calc
      j≤j*P := Nat.le_mul_of_pos_right j hPone
      _=P*j := by ac_rfl
  have htrip : 3*m+20≤3*P := by omega
  have hdist : P*(j+3)=P*j+3*P := by
    rw [Nat.mul_add]
    ac_rfl
  have hk15 : 15≤k := by
    change k+j+3*m+5=P*(j+3) at hgate
    rw [hdist] at hgate
    omega
  have hpowdiv : 16 ∣ P := by
    dsimp [P]
    change 2^4 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hgate16 : (k+j+3*m+5)%16=0 := by
    have hd : 16 ∣ P*(j+3) := by
      rcases hpowdiv with ⟨u,hu⟩
      refine ⟨u*(j+3),?_⟩
      rw [hu]
      ac_rfl
    have hrel : P*(j+3)=k+j+3*m+5 := by simpa only [P] using hgate.symm
    rw [hrel] at hd
    exact Nat.mod_eq_zero_of_dvd hd
  have hx : (2*j+3)%8=1 := by rcases hclass with h|h|h|h <;> omega
  have hy : k%2=1 := by rcases hclass with h|h|h|h <;> omega
  have hsum : ((2*j+3)+k)%16=8 := by rcases hclass with h|h|h|h <;> omega
  have hsize : 24≤(2*j+3)+k := by omega
  exact odd_sliver_blank_unreachable (2*j+3) k time hx hy (by omega) hsum hsize

#print axioms high_halt_sliver_mod16_unreachable
end BB6.Agent3
