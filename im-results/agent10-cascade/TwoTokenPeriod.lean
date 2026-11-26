import Std

namespace BB6.Agent10TwoTokenPeriod

set_option maxHeartbeats 1000000

/-- 3^A dominates twice the other term of the beta-cycle denominator
    whenever A≥6. -/
theorem denominator_dominates (A : Nat) (hA : 6≤A) : 2*2^(A+2)≤3^A := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hA
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      2*2^(6+(k+1)+2) = 2*(2*2^(6+k+2)) := by
        rw [show 6+(k+1)+2=(6+k+2)+1 by omega,Nat.pow_succ]; ac_rfl
      _ ≤ 2*3^(6+k) := Nat.mul_le_mul_left _ (ih (by omega))
      _ ≤ 3*3^(6+k) := Nat.mul_le_mul_right _ (by decide)
      _ = 3^(6+(k+1)) := by rw [show 6+(k+1)=(6+k)+1 by omega,Nat.pow_succ,Nat.mul_comm]

/-- A common reduced beta denominator r with numerator cancellation factor g
    is large when one of the two positive valuations is at most A/2. -/
theorem beta_lower {A m r g : Nat} (hA : 6≤A) (hm : 2*m≤A)
    (hv : 3^A-2^(A+2)=r*g) (hg : g≤3*3^m) : 3^A≤36*r^2 := by
  have hdom := denominator_dominates A hA
  have hd : 3^A≤2*(r*g) := by omega
  have h6 : 3^A≤6*r*3^m := by
    calc
      _ ≤ 2*(r*g) := hd
      _ ≤ 2*(r*(3*3^m)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hg)
      _ = _ := by change _ = (2*3)*r*3^m; ac_rfl
  have hs := Nat.pow_le_pow_left h6 2
  simp only [Nat.mul_pow] at hs
  have hp3 : (3^m)^2=3^(2*m) := by rw [← Nat.pow_mul,Nat.mul_comm m 2]
  rw [hp3] at hs
  change (3^A)^2≤36*r^2*3^(2*m) at hs
  have hh : 3^A*3^A≤(36*r^2)*3^A := by
    rw [show (3^A)^2=3^A*3^A by rw [Nat.pow_succ,Nat.pow_one]] at hs
    exact Nat.le_trans hs (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hm))
  exact Nat.le_of_mul_le_mul_right hh (Nat.pow_pos (by decide))

/-- Elementary monotonicity for the explicit tail bound. -/
theorem square_step (n : Nat) (hn : 7≤n) : 3*(n+1)^2≤4*n^2 := by
  have h := Nat.mul_le_mul_right n hn
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul] at *
  omega

theorem tail_step (n : Nat) (hn : 7≤n) (h : 729*n^2*3^n≤4*4^n) :
    729*(n+1)^2*3^(n+1)≤4*4^(n+1) := by
  calc
    729*(n+1)^2*3^(n+1) = 729*(3*(n+1)^2)*3^n := by
      rw [Nat.pow_succ 3 n]; ac_rfl
    _ ≤ 729*(4*n^2)*3^n := Nat.mul_le_mul_right (3^n)
      (Nat.mul_le_mul_left 729 (square_step n hn))
    _ = 4*(729*n^2*3^n) := by ac_rfl
    _ ≤ 4*(4*4^n) := Nat.mul_le_mul_left 4 h
    _ = 4*4^(n+1) := by rw [Nat.pow_succ 4 n]; ac_rfl

theorem tail_bound (A : Nat) (hA : 45≤A) : 729*A^2*3^A≤4*4^A := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hA
  clear hA
  induction k with
  | zero => decide +kernel
  | succ k ih => exact tail_step (45+k) (by omega) ih

/-- All hypothetical two-token periods with positive valuations have total
    valuation at most 44, using the first-difference denominator bound. -/
theorem valuation_bound {A D r : Nat} (hA : 6≤A) (hD : 0<D) (hDA : D≤A)
    (hlo : 3^A≤36*r^2) (hhi : r≤D*(2^D-1))
    (hs : 2^(A+2+D)<3^(A+2)) : A<45 := by
  have hp : 2^D-1<2^D := by have := Nat.two_pow_pos D; omega
  have hr : r<A*2^D := by
    exact Nat.lt_of_le_of_lt hhi (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hp hD)
      (Nat.mul_le_mul_right _ hDA))
  have hh : 4*2^A*r<9*A*3^A := by
    calc
      _ < 4*2^A*(A*2^D) := Nat.mul_lt_mul_of_pos_left hr (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
      _ = A*2^(A+2+D) := by rw [Nat.pow_add 2 (A+2) D,Nat.pow_add 2 A 2]; change _ = A*(2^A*4*2^D); ac_rfl
      _ < A*3^(A+2) := Nat.mul_lt_mul_of_pos_left hs (by omega)
      _ = _ := by rw [Nat.pow_add 3 A 2]; change A*(3^A*9) = 9*A*3^A; ac_rfl
  have hsq := Nat.pow_lt_pow_left hh (show 2≠0 by decide)
  simp only [Nat.mul_pow] at hsq
  have hp2 : (2^A)^2=4^A := by rw [← Nat.pow_mul,Nat.mul_comm A 2,Nat.pow_mul]
  have hp3 : (3^A)^2=9^A := by rw [← Nat.pow_mul,Nat.mul_comm A 2,Nat.pow_mul]
  rw [hp2,hp3] at hsq
  change 16*4^A*r^2<81*A^2*9^A at hsq
  have hx : 4*3^A*(4*4^A)<4*3^A*(729*A^2*3^A) := by
    calc
      _ = (16*4^A)*3^A := by change _ = (4*4*4^A)*3^A; ac_rfl
      _ ≤ (16*4^A)*(36*r^2) := Nat.mul_le_mul_left _ hlo
      _ = 36*(16*4^A*r^2) := by ac_rfl
      _ < 36*(81*A^2*9^A) := Nat.mul_lt_mul_of_pos_left hsq (by decide)
      _ = (36*81)*A^2*(3^A*3^A) := by rw [← hp3,Nat.pow_succ (3^A) 1,Nat.pow_one]; ac_rfl
      _ = (4*729)*A^2*(3^A*3^A) := by rfl
      _ = _ := by ac_rfl
  have hh2 := Nat.lt_of_mul_lt_mul_left hx
  by_cases h : A<45
  · exact h
  · have htail := tail_bound A (by omega)
    omega

/-- Necessary band constraints on a positive slope token. -/
def admissible (a d : Nat) : Bool := decide (3*3^a<2^(a+2+d) ∧ 2^(a+d)<2*3^a)

def tokens : List (Nat × Nat) := (List.range 44).flatMap fun a0 =>
  let a := a0+1
  ((List.range (a+1)).filter (admissible a)).map fun d => (a,d)

def candidate (t u : Nat × Nat) : Bool :=
  let (a,d) := t
  let (b,e) := u
  let D := d+e
  let P1 := 2^(a+1+d)
  let P2 := 2^(b+1+e)
  let R1 := 3^a
  let R2 := 3^b
  let Q := P1*P2-R1*R2
  let n := R2*(R1+P1)
  let n1 := R1*(R2+P2)
  let q := Q/Q.gcd n
  decide (a+b<45 ∧ 0<D ∧ 0<Q ∧ Q<2*n ∧ n<Q ∧ Q<2*n1 ∧ n1<Q ∧ (2^D-1)^2 % q=0)

def checked : Bool := tokens.all fun t => tokens.all fun u => !candidate t u

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem check_all : checked = true := by decide +kernel

theorem token_mem {a d : Nat} (ha : 0<a) (ha44 : a≤44) (hd : d≤a)
    (h : admissible a d=true) : (a,d)∈tokens := by
  unfold tokens
  apply List.mem_flatMap.mpr
  refine ⟨a-1,List.mem_range.mpr (by omega),?_⟩
  have he : a-1+1=a := by omega
  simp only [he]
  exact List.mem_map.mpr ⟨d,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),h⟩,rfl⟩

theorem no_candidate {a b d e : Nat}
    (ha : 0<a) (hb : 0<b) (hA : a+b<45) (hd : d≤a) (he : e≤b)
    (ht : admissible a d=true) (hu : admissible b e=true) :
    candidate (a,d) (b,e)=false := by
  have hm := token_mem ha (by omega : a≤44) hd ht
  have hn := token_mem hb (by omega : b≤44) he hu
  have h := List.all_eq_true.mp check_all _ hm
  have h' := List.all_eq_true.mp h _ hn
  exact (Bool.not_eq_true' _).mp h'

#print axioms beta_lower
#print axioms tail_bound
#print axioms valuation_bound
#print axioms check_all
#print axioms no_candidate
#eval tokens.length

end BB6.Agent10TwoTokenPeriod
