import Lean

namespace BB429Q0Macro.HalfStep
set_option maxHeartbeats 8000000

/-- A nearly linear window in the rank scale, with a logarithmic divisor. -/
def wideRadius (k : Nat) : Nat := 4^k / (128*(k+1))

private theorem power_margin (t : Nat) (ht : 12≤t) : 512*(t+1)≤4^t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases h : 12≤t
    · have h₁ := ih h
      rw [Nat.pow_succ]
      omega
    · have he : t=11 := by omega
      subst t
      decide

private theorem radius_bound (k : Nat) : 128*((k+1)*wideRadius k)≤4^k := by
  have h := Nat.div_mul_le_self (4^k) (128*(k+1))
  simpa only [wideRadius,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

/-- The growth budget suffices for a nearly linear two-sided window at
    one of three adjacent powers of two. No hypothesis about actual
    crossings is used. -/
theorem wide_rank_cover (t p P : Nat) (ht : 12≤t)
    (hl : 4^t≤p) (hh : p<4^(t+1))
    (growth : ∀ j : Nat, 6*j*(t+1)+14≤p → 2*p+2*j≤P+14) :
    ∃ a k, (a=1 ∨ a=2) ∧ 12≤k ∧
      p+9*wideRadius k≤a*4^k ∧ a*4^k+8+9*wideRadius k≤P := by
  let F := 4^t
  let K := t+1
  let A := wideRadius t
  let B := wideRadius (t+1)
  have hpow : 4^(t+1)=4*F := by simp [F,Nat.pow_succ,Nat.mul_comm]
  have hmargin : 512*K≤F := power_margin t ht
  have hK : 1≤K := by dsimp [K]; omega
  have hA : 128*(K*A)≤F := radius_bound t
  have hB₀ : 128*((K+1)*B)≤4*F := by
    have h := radius_bound (t+1)
    rw [hpow] at h
    exact h
  have hB : 32*(K*B)≤F := by
    have h := Nat.mul_le_mul_right B (show K≤K+1 by omega)
    omega
  have hAl : A≤K*A := by
    simpa using Nat.mul_le_mul_right A hK
  have hBl : B≤K*B := by
    simpa using Nat.mul_le_mul_right B hK
  have hF : 4*F=4^(t+1) := hpow.symm
  have hp0 : F≤p := hl
  have hp1 : p<4*F := by omega
  by_cases ha : p+9*A≤2*F
  · let j := 5*A+11
    have hbudget : 6*j*K+14≤p := by
      have h : 6*j*K=30*(K*A)+66*K := by
        dsimp [j]
        rw [Nat.mul_add,Nat.add_mul]
        grind
      omega
    have hg := growth j hbudget
    refine ⟨2,t,Or.inr rfl,ht,ha,?_⟩
    change 2*F+8+9*A≤P
    dsimp [j] at hg
    omega
  by_cases hb : p+9*B≤4*F
  · let j := 9*A+5*B+11
    have hbudget : 6*j*K+14≤p := by
      have h : 6*j*K=54*(K*A)+30*(K*B)+66*K := by
        dsimp [j]
        rw [Nat.mul_add,Nat.mul_add,Nat.add_mul,Nat.add_mul]
        grind
      omega
    have hg := growth j hbudget
    refine ⟨1,t+1,Or.inl rfl,by omega,?_,?_⟩
    · simpa only [Nat.one_mul,hpow] using hb
    · rw [Nat.one_mul,hpow]
      change 4*F+8+9*B≤P
      dsimp [j] at hg
      omega
  · let j := 14*B+11
    have hbudget : 6*j*K+14≤p := by
      have h : 6*j*K=84*(K*B)+66*K := by
        dsimp [j]
        rw [Nat.mul_add,Nat.add_mul]
        grind
      omega
    have hg := growth j hbudget
    refine ⟨2,t+1,Or.inr rfl,by omega,?_,?_⟩
    · rw [hpow]
      change p+9*B≤2*(4*F)
      omega
    · rw [hpow]
      change 2*(4*F)+8+9*B≤P
      dsimp [j] at hg
      omega

/-- At every relevant scale the new radius is at least the earlier square-root radius. -/
theorem wideRadius_ge_sqrt (k : Nat) (hk : 12≤k) : 2^k≤wideRadius k := by
  have h : 128*(k+1)≤2^k := by
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hh : 12≤k
      · have h₁ := ih hh
        rw [Nat.pow_succ]
        omega
      · have he : k=11 := by omega
        subst k
        decide
  have hp : 4^k=2^k*2^k := by
    rw [←Nat.pow_mul 2 2 k,show 2*k=k+k by omega,Nat.pow_add]
  unfold wideRadius
  apply (Nat.le_div_iff_mul_le (by omega)).2
  rw [hp]
  exact Nat.mul_le_mul_left (2^k) h

#print axioms wide_rank_cover
#print axioms wideRadius_ge_sqrt
end BB429Q0Macro.HalfStep
