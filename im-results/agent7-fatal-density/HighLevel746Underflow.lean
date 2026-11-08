import Lean
set_option maxHeartbeats 0
set_option maxRecDepth 8192

namespace Agent7HighLevel746

inductive State where
  | C (a b : Nat)
  deriving DecidableEq, Repr

/-- Exact high-level transition map from the independent Cryptids #746 formalization. -/
def next : State → Option State
  | .C a 0 => some (.C 2 (2*a+1))
  | .C _ 1 => none
  | .C a (d+2) =>
      if 2*a ≤ d then some (.C (2*a+2) (d-2*a))
      else if d%2=1 then
        some (.C ((6*a+d+5)/4) ((6*a+d+5)%4))
      else
        some (.C ((6*a+d+8)/4) ((6*a+d+8)%4))

@[simp] theorem next_C_zero (a:Nat) :
  next (.C a 0) = some (.C 2 (2*a+1)) := rfl

@[simp] theorem next_C_one (a:Nat) :
  next (.C a 1) = none := rfl

theorem next_C_two_even (a:Nat) (ha:1≤a) (he:a%2=0) :
  next (.C a 2) = some (.C ((3*a+4)/2) 0) := by
  have hlow : ¬ 2*a ≤ 0 := by omega
  simp [next, hlow]
  omega

theorem next_C_two_odd (a:Nat) (ha:1≤a) (ho:a%2=1) :
  next (.C a 2) = some (.C ((3*a+3)/2) 2) := by
  have hlow : ¬ 2*a ≤ 0 := by omega
  simp [next, hlow]
  omega

theorem next_C_two_even_c (c:Nat) (hc:7≤c) (he:c%2=0) :
  next (.C (c-3) 2) = some (.C (3*c/2-3) 2) := by
  have ha : 1≤c-3 := by omega
  have ho : (c-3)%2=1 := by omega
  rw [next_C_two_odd (c-3) ha ho]
  congr 2
  omega

theorem next_C_two_odd_c (c:Nat) (hc:7≤c) (ho:c%2=1) :
  next (.C (c-3) 2) = some (.C ((3*c-5)/2) 0) := by
  have ha : 1≤c-3 := by omega
  have he : (c-3)%2=0 := by omega
  rw [next_C_two_even (c-3) ha he]
  congr 2
  omega

def underflowC (t z i:Nat) : Nat := 2^(t-i)*3^i*z

theorem underflowC_even (t z i:Nat) (hi:i<t) :
  underflowC t z i %2=0 := by
  unfold underflowC
  have hdiff : t-i=(t-i-1)+1 := by omega
  rw [hdiff, Nat.pow_succ]
  simp [Nat.mul_mod]

theorem underflowC_step (t z i:Nat) (hi:i<t) :
  2*underflowC t z (i+1)=3*underflowC t z i := by
  unfold underflowC
  have hdiff : t-(i+1)+1=t-i := by omega
  rw [← hdiff, Nat.pow_succ]
  simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem next_underflow_step (t z i:Nat) (hi:i<t)
    (hlarge:7≤underflowC t z i) :
  next (.C (underflowC t z i-3) 2) =
    some (.C (underflowC t z (i+1)-3) 2) := by
  have he := underflowC_even t z i hi
  have hstep := underflowC_step t z i hi
  have hdiv : 3*underflowC t z i/2 = underflowC t z (i+1) := by omega
  rw [next_C_two_even_c (underflowC t z i) hlarge he, hdiv]

private theorem pow_three_odd (t:Nat) : (3^t)%2=1 := by
  induction t with
  | zero => decide
  | succ t ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      simp [ih]

theorem next_underflow_exit (t z:Nat) (hz:z%2=1)
    (hlarge:7≤3^t*z) :
  next (.C (3^t*z-3) 2) = some (.C ((3^(t+1)*z-5)/2) 0) := by
  have hp : (3^t)%2=1 := pow_three_odd t
  have ho : (3^t*z)%2=1 := by simp [Nat.mul_mod, hp, hz]
  rw [next_C_two_odd_c (3^t*z) hlarge ho]
  congr 2
  rw [Nat.pow_succ]
  simp [Nat.mul_left_comm, Nat.mul_comm]

inductive Steps : State → State → Prop where
  | refl (s:State) : Steps s s
  | step {s t u:State} (h:next s=some t) (ht:Steps t u) : Steps s u

theorem Steps.trans {s t u:State} (h:Steps s t) (ht:Steps t u) : Steps s u := by
  induction h with
  | refl _ => exact ht
  | step hstep htail ih => exact Steps.step hstep (ih ht)

theorem underflow_path (t z:Nat) (hz:z%2=1) (hlarge:7≤2^t*z) :
  Steps (.C (2^t*z-3) 2) (.C ((3^(t+1)*z-5)/2) 0) := by
  induction t generalizing z with
  | zero =>
      have hlarge' : 7≤z := by simpa using hlarge
      have h := next_C_two_odd_c z hlarge' hz
      simpa using Steps.step h (Steps.refl _)
  | succ t ih =>
      have hcEven : (2^(t+1)*z)%2=0 := by
        rw [Nat.pow_succ]
        simp [Nat.mul_mod]
      have hcLarge : 7≤2^(t+1)*z := hlarge
      have hfirst := next_C_two_even_c (2^(t+1)*z) hcLarge hcEven
      have hnum : 3*(2^(t+1)*z) = (2^t*(3*z))*2 := by
        rw [Nat.pow_succ]
        simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      have hnext : 3*(2^(t+1)*z)/2 = 2^t*(3*z) :=
        Nat.div_eq_of_eq_mul_left (by decide) hnum
      rw [hnext] at hfirst
      have hzle : 2*z ≤ 3*z := by omega
      have hcomp : 2^t*(2*z) ≤ 2^t*(3*z) := Nat.mul_le_mul_left _ hzle
      have hpow : 2^(t+1)*z = 2^t*(2*z) := by
        rw [Nat.pow_succ]
        simp [Nat.mul_assoc, Nat.mul_comm]
      have hlarge' : 7≤2^t*(2*z) := by simpa [hpow] using hlarge
      have hnextLarge : 7≤2^t*(3*z) := Nat.le_trans hlarge' hcomp
      have hz3 : (3*z)%2=1 := by omega
      have htail := ih (z:=3*z) hz3 hnextLarge
      have htail' : Steps (.C (2^t*(3*z)-3) 2) (.C ((3^(t+2)*z-5)/2) 0) := by
        simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm] using htail
      exact Steps.step hfirst htail'

theorem odd_parent_underflow_path (g l t z:Nat) (hz:z%2=1)
    (hband:6*2^l+1≤2^t*z) (hnum:2*g+5=3^(t+1)*z) :
  Steps (.C (2^t*z-3) 2) (.C g 0) := by
  have hs : 1≤2^l := Nat.one_le_pow l 2 (by decide)
  have hlarge : 7≤2^t*z := by omega
  have hpath := underflow_path t z hz hlarge
  have hfinal : (3^(t+1)*z-5)/2=g := by
    rw [← hnum]
    omega
  rw [hfinal] at hpath
  exact hpath

end Agent7HighLevel746
