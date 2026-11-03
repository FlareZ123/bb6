module
public import GateExistence
@[expose] public section
namespace BB6.Agent16OddPower

/-- A reusable universal forbidden-odd-gap theorem for the exact modular orbit. -/
theorem odd_gap_any (a n d : Nat) (hodd : d%2=1)
   (hgt : 1<d) (hlt : d<2^a) :
   2^n % (2^(a+1)+1) ≠ d := by
  intro he
  obtain ⟨r,hr,hpos|hneg⟩ := pow2_pm_mod a n
  · have hd : d=2^r := by omega
    cases r with
    | zero => simp only [Nat.pow_zero] at hd; omega
    | succ b =>
      have heven : 2^(b+1)%2=0 := by rw [Nat.pow_succ]; omega
      rw [hd] at hodd
      omega
  · have hle : 2^r ≤ 2^a := Nat.pow_le_pow_right (by decide) hr
    have hpow : 2^(a+1)=2*2^a := by rw [Nat.pow_succ]; omega
    omega

private theorem exp10_aux (k : Nat) : 10*(k+6)-1 < 2^(k+6) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hp : 64 ≤ 2^(k+6) := by
      have h := Nat.pow_le_pow_right (by decide : 0<2) (show 6≤k+6 by omega)
      simpa using h
    have hs : 2^((k+1)+6) = 2*2^(k+6) := by
      rw [show (k+1)+6=(k+6)+1 by omega, Nat.pow_succ]
      omega
    rw [hs]
    omega

private theorem exp10_gap (a : Nat) (ha : 6≤a) :
    1<10*a-1 ∧ 10*a-1 < 2^a := by
  have hr : a=(a-6)+6 := by omega
  have he := exp10_aux (a-6)
  rw [←hr] at he
  omega

/-- The second-generation power candidate p_j is always 3-divisible. -/
theorem gateOdd_div3 (k : Nat) : gateOdd k %3=0 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h : gateOdd (k+1)=16*gateOdd k+3 := rfl
    rw [h, Nat.add_mod, Nat.mul_mod, ih]

/-- No generic a≥6 section source returns to an odd-power gateway word. -/
theorem no_large_generic_second_gate
    (a v k : Nat) (ha : 6≤a) (hv : 5≤v) (hodd : v%2=1)
    (hstep : 2^a*v + a+(v-1)/2 = 2*gateOdd k) : False := by
  have hd : 2*((v-1)/2)=v-1 := by omega
  have hm : (2^(a+1)+1)*v =2*(2^a*v)+v := by
    rw [Nat.pow_succ, Nat.add_mul]
    simp only [Nat.one_mul]
    ac_rfl
  have heq : (2^(a+1)+1)*v+(2*a-1)=4*gateOdd k := by
    omega
  have hgate : 5*gateOdd k +1=2^(4*k+4) := gateOdd_equation k
  have hnext : 2^(4*k+6)=4*2^(4*k+4) := by
    rw [show 4*k+6=(4*k+4)+2 by omega, Nat.pow_add]
    change 2^(4*k+4)*4 = 4*2^(4*k+4)
    omega
  have hbig : 5*(2^(a+1)+1)*v+(10*a-1) = 2^(4*k+6) := by
    have hmul : 5*(2^(a+1)+1)*v = 5*((2^(a+1)+1)*v) := by ac_rfl
    rw [hmul]
    omega
  have hgap := exp10_gap a ha
  have hoddgap : (10*a-1)%2=1 := by omega
  have hmod : 2^(4*k+6) % (2^(a+1)+1) = 10*a-1 := by
    rw [←hbig]
    have hmul : 5*(2^(a+1)+1)*v = (2^(a+1)+1)*(5*v) := by ac_rfl
    rw [hmul, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by
      have hs : 2^(a+1)=2*2^a := by rw [Nat.pow_succ]; omega
      omega)
  exact odd_gap_any a (4*k+6) (10*a-1) hoddgap hgap.1 hgap.2 hmod

#print axioms odd_gap_any
#print axioms gateOdd_div3
#print axioms no_large_generic_second_gate
end BB6.Agent16OddPower
