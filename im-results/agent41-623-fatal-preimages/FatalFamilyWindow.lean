import FatalFamilyInverseActual

namespace BB6.Agent41FatalInverse
open BB6.Agent49CorrectionGrowth

def targetX (k : Nat) : Nat := (3^(k+1)-5)/2

def targetY (k : Nat) : Nat := 3*base k - 2*(k+1)+5

theorem base_parity (k : Nat) : base k%2=k%2 := by
  induction k with
  | zero => decide
  | succ k ih => rw [base]; omega

theorem pow_margin (k : Nat) (hk : 7≤k) : 4*(k+1)+4 < 3^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 7≤k
    · have hh := ih h
      rw [Nat.pow_succ]; omega
    · have he : k=6 := by omega
      subst k; decide

theorem targetY_formula (k : Nat) (hk : 7≤k) :
    (targetY k:Int)=3*(base k:Int)-2*((k:Int)+1)+5 := by
  have hp := pow_margin k hk
  have hb := base_lower k
  unfold targetY
  omega

theorem targetY_even (k : Nat) (hk : 7≤k) (ho : k%2=1) : targetY k%2=0 := by
  have hp := pow_margin k hk
  have hb := base_lower k
  have he := base_parity k
  unfold targetY
  omega

theorem targetX_lower (k : Nat) (hk : 7≤k) : 4*(k+1)+6 ≤ targetX k := by
  have h : 8*(k+1)+17 ≤ 3^(k+1) := by
    have hh := pow_margin k hk
    rw [Nat.pow_succ]
    omega
  unfold targetX
  omega

theorem targetY_gt14 (k : Nat) (hk : 7≤k) : 14<targetY k := by
  have hp := pow_margin k hk
  have hb := base_lower k
  unfold targetY
  omega

theorem pow3_le_pow2 (k : Nat) : 3^k ≤ 2^(2*k) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ,show 2*(k+1)=2*k+1+1 by omega,Nat.pow_succ,Nat.pow_succ]
    omega

theorem targetY_binary_bound (k : Nat) (hk : 7≤k) : targetY k < 2^(2*(k+1)+3) := by
  have hb := base_power k
  have hp := pow3_le_pow2 k
  have hpos : 0<2^(2*k) := Nat.pow_pos (by decide)
  unfold targetY
  rw [show 2*(k+1)+3=2*k+1+1+1+1+1 by omega]
  simp only [Nat.pow_succ]
  omega

theorem budget_le (k : Nat) (hk : 7≤k) : (targetY k).log2+1 ≤ 2*(k+1)+3 := by
  have hp := targetY_binary_bound k hk
  have hy := targetY_gt14 k hk
  have hh := (Nat.log2_lt (show targetY k ≠ 0 by omega)).mpr hp
  omega

theorem large_first (k : Nat) (hk : 7≤k) : 2*((targetY k).log2+1) ≤ targetX k := by
  have h1 := targetX_lower k hk
  have h2 := budget_le k hk
  omega

def LeftParameter (k t : Nat) : Prop :=
  (k:Int)+1 = 3*(t:Int)-1-2*(ordinary k t).1-(ordinary k t).2

def RightParameter (k t : Nat) : Prop :=
  3*((k:Int)+1) = 3*(t:Int)+(balanced k t).1+2*(balanced k t).2+1

/-- The finite-digit ordinary weight is never greater than twice the input. -/
theorem ordinary_weight (k : Nat) : ∀ t, 2*(ordinary k t).1+(ordinary k t).2≤2*t := by
  induction k with
  | zero => intro t; simp [ordinary]
  | succ k ih =>
    intro t
    have h := ih (t/3)
    have hr : t%3=0 ∨ t%3=1 ∨ t%3=2 := by omega
    rcases hr with hr|hr|hr <;> simp [ordinary,hr] <;> omega

/-- Every left-even image in the window forces the ordinary digit parameter. -/
theorem left_parameter_necessary (k b : Nat) (hk : 7≤k) (ho : k%2=1)
    (hb : b%2=0) (hy : targetY k=2+image b)
    (hE : excess b ≤ 4*(2*(k+1)+3)) :
    ∃ t, t≤k+2 ∧ LeftParameter k t := by
  have hform := targetY_formula k hk
  have hpar := base_parity k
  have hp := pow_margin k hk
  have hi : targetY k=2+3*b+excess b := by unfold image at hy; omega
  let j := base k-b
  have hj : base k=b+j := by dsimp [j]; omega
  have hjodd : j%2=1 := by omega
  have hjbound : j<4*(k+1)+4 := by omega
  let t := j/2
  have hje : j=2*t+1 := by dsimp [t]; omega
  have hbt : b=base k-(2*t+1) := by omega
  have ht : t<3^k := by omega
  have hh := (actual_left k t ht).mp (by rw [←hbt]; omega)
  have hw := ordinary_weight k t
  exact ⟨t,by omega,hh⟩

/-- Every right-odd image in the window forces the balanced digit parameter. -/
theorem right_parameter_necessary (k b : Nat) (hk : 7≤k) (ho : k%2=1)
    (hb : b%2=1) (hy : targetY k=3+image b)
    (hE : excess b ≤ 4*(2*(k+1)+3)) :
    ∃ t, t≤k+1 ∧ RightParameter k t := by
  have hform := targetY_formula k hk
  have hpar := base_parity k
  have hp := pow_margin k hk
  have hi : targetY k=3+3*b+excess b := by unfold image at hy; omega
  let j := base k-b
  have hj : base k=b+j := by dsimp [j]; omega
  have hjeven : j%2=0 := by omega
  have hjbound : j<4*(k+1)+4 := by omega
  let t := j/2
  have hje : j=2*t := by dsimp [t]; omega
  have hbt : b=base k-2*t := by omega
  have ht : 2*t<3^k := by omega
  have hh := (actual_right k t ht).mp (by rw [←hbt]; omega)
  exact ⟨t,by omega,hh⟩

#print axioms targetY_formula
#print axioms large_first
#print axioms left_parameter_necessary
#print axioms right_parameter_necessary
end BB6.Agent41FatalInverse
