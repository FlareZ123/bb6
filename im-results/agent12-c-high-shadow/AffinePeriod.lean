import Lean
namespace MachineCAffinePeriod

theorem no_exp_linear (p A B : Nat) (hp : 2 ≤ p)
    (h : ∀ n, p^n ≤ A*n+B) : False := by
  have hsmall (n : Nat) : n+1 ≤ p^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.pow_succ]
      have hn := Nat.mul_le_mul ih hp
      omega
  let n := 2*A+B+1
  have hsq : (n+1)*(n+1) ≤ p^(n+n) := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul (hsmall n) (hsmall n)
  have hb := h (n+n)
  have hnn : (A+A)*n ≤ n*n := Nat.mul_le_mul_right n (by dsimp [n]; omega)
  rw [Nat.mul_add] at hb
  rw [Nat.add_mul] at hnn
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hsq
  have hnB : B < n := by dsimp [n]; omega
  omega

theorem exp_sequence_zero (p A B : Nat) (hp : 2 ≤ p) (E : Nat → Int)
    (hstep : ∀ n, E (n+1) = (p:Int)*E n)
    (hbound : ∀ n, (E n).natAbs ≤ A*n+B) : ∀ n, E n = 0 := by
  have he (n : Nat) : E n = (p:Int)^n * E 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [hstep, ih, Int.pow_succ]; ac_rfl
  have hz : E 0 = 0 := by
    by_cases hh : E 0 = 0
    · exact hh
    · have habs : 1 ≤ (E 0).natAbs := Int.natAbs_pos.mpr hh
      exfalso
      apply no_exp_linear p A B hp
      intro n
      have h1 := hbound n
      rw [he, Int.natAbs_mul, Int.natAbs_pow] at h1
      simp at h1
      have hm := Nat.mul_le_mul_left (p^n) habs
      simp at hm
      exact Nat.le_trans hm h1
  intro n
  rw [he, hz, Int.mul_zero]

theorem affine_increment (p : Nat) (q C : Int) (M0 W : Nat)
    (A : Nat → Int) (hp : 2 ≤ p)
    (hA : ∀ n, A (n+1) = (p:Int)*A n-q*(↑(M0+W*n):Int)+C)
    (hbound : ∀ n, 0 ≤ A n ∧ A n ≤ (↑(M0+W*n):Int)) :
    ∀ n, ((p:Int)-1)*(A (n+1)-A n) = q*(W:Int) := by
  let E (n : Nat) := ((p:Int)-1)*(A (n+1)-A n)-q*(W:Int)
  have hs (n : Nat) : E (n+1) = (p:Int)*E n := by
    dsimp [E]
    have h0 := hA n
    have h1 := hA (n+1)
    push_cast at h0 h1
    rw [h1]
    grind
  have habs (n : Nat) : (A n).natAbs ≤ M0+W*n := by
    have h := hbound n
    omega
  have hb (n : Nat) : (E n).natAbs ≤ (p-1)*(2*W)*n+((p-1)*(2*M0+W)+q.natAbs*W) := by
    have h1 := Int.natAbs_sub_le (((p:Int)-1)*(A (n+1)-A n)) (q*(W:Int))
    have h2 := Int.natAbs_sub_le (A (n+1)) (A n)
    rw [Int.natAbs_mul, Int.natAbs_mul] at h1
    have h3 : ((p:Int)-1).natAbs = p-1 := by omega
    rw [h3] at h1
    simp only [Int.natAbs_natCast] at h1
    have h4 : (A (n+1)-A n).natAbs ≤ (M0+W*(n+1))+(M0+W*n) := by
      have := habs n
      have := habs (n+1)
      omega
    have h5 := Nat.mul_le_mul_left (p-1) h4
    calc
      (E n).natAbs ≤ (p-1)*(A (n+1)-A n).natAbs+q.natAbs*W := h1
      _ ≤ (p-1)*((M0+W*(n+1))+(M0+W*n))+q.natAbs*W := Nat.add_le_add_right h5 _
      _ = _ := by grind
  have hz := exp_sequence_zero p ((p-1)*(2*W)) ((p-1)*(2*M0+W)+q.natAbs*W) hp E hs hb
  intro n
  have h := hz n
  dsimp [E] at h
  omega

theorem cycle211_no_affine (a M o : Int) (ho : o=0 ∨ o=1)
    (h : 256*a-119*M-454+120*o=a+14) : False := by omega

theorem cycle211_block (a M o : Int) :
    2*(2*(4*a-M+1+2*o)-(M+7))-(M+11) = 16*a-7*M-21+8*o := by omega

theorem cycle211_twoblock (a M o : Int) :
    16*(16*a-7*M-21+8*o)-7*(M+15)-21+8*(1-o) =
      256*a-119*M-454+120*o := by omega

def halfCount (d R u : Nat) : Nat :=
    ((List.range R).filter (fun i => d < 2*((u*2^i)%d))).length

example : halfCount 15 4 1 = 1 ∧ halfCount 15 4 7 = 3 := by decide
example : halfCount 21 6 1 = 2 ∧ halfCount 21 6 5 = 4 := by decide
example : 2^5 % 33 = 32 := by decide
example : halfCount 39 12 1 = 4 ∧ halfCount 39 12 7 = 8 := by decide

end MachineCAffinePeriod
