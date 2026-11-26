import Std

namespace BB6.Agent10ThreeTokenPeriod

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 100000

private theorem ratio_step (n k p q : Nat) (hn : 32 ≤ n)
    (h : p*33^k ≤ q*32^k) : p*(n+1)^k ≤ q*n^k := by
  have ha : 32*(n+1) ≤ 33*n := by omega
  have hp := Nat.pow_le_pow_left ha k
  rw [Nat.mul_pow, Nat.mul_pow] at hp
  apply Nat.le_of_mul_le_mul_right (c:=32^k) _ (Nat.pow_pos (by decide))
  calc
    p*(n+1)^k*32^k = p*(32^k*(n+1)^k) := by ac_rfl
    _ ≤ p*(33^k*n^k) := Nat.mul_le_mul_left _ hp
    _ = (p*33^k)*n^k := by ac_rfl
    _ ≤ (q*32^k)*n^k := Nat.mul_le_mul_right _ h
    _ = (q*n^k)*32^k := by ac_rfl

private theorem tail_le (n k C p q E : Nat) (hn : 300 ≤ n)
    (hbase : (C*300)^k*p^300 ≤ E*q^300)
    (hr : p*33^k ≤ q*32^k) : (C*n)^k*p^n ≤ E*q^n := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => exact hbase
  | succ m ih =>
    rw [show 300+(m+1)=(300+m)+1 by omega]
    calc
      (C*((300+m)+1))^k*p^((300+m)+1) = C^k*(p*((300+m)+1)^k)*p^(300+m) := by
        rw [Nat.mul_pow,Nat.pow_succ p]; ac_rfl
      _ ≤ C^k*(q*(300+m)^k)*p^(300+m) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (ratio_step _ _ _ _ (by omega) hr))
      _ = q*((C*(300+m))^k*p^(300+m)) := by rw [Nat.mul_pow]; ac_rfl
      _ ≤ q*(E*q^(300+m)) := Nat.mul_le_mul_left _ ih
      _ = E*q^((300+m)+1) := by rw [Nat.pow_succ q]; ac_rfl

/-- The largest preceding valuation forces a large reduced beta denominator. -/
theorem large_valuation {A a r : Nat} (h : 2*A≤5*a) (hr : 3^a≤14*r) :
    3^(2*A) ≤ (14*r)^5 := by
  calc
    3^(2*A) ≤ 3^(5*a) := Nat.pow_le_pow_right (by decide) h
    _ = (3^a)^5 := by rw [Nat.mul_comm 5 a,Nat.pow_mul]
    _ ≤ (14*r)^5 := Nat.pow_le_pow_left hr 5

/-- Two distinct phase numerators, each divisible by a high power of three,
    force a second denominator lower bound. The paper reduction supplies
    b≥c, b+c>3A/5 and 3^(b+c)≤28 r 2^c. -/
theorem close_numerators {A b c r : Nat} (hbc : c≤b)
    (hA : 3*A≤5*(b+c)) (h : 3^(b+c)≤28*r*2^c) :
    3^(6*A) ≤ (28*r)^10*2^(3*A) := by
  have hh := Nat.pow_le_pow_left h 2
  rw [Nat.mul_pow,← Nat.pow_mul,← Nat.pow_mul] at hh
  have h2 : 3^(2*(b+c)) ≤ (28*r)^2*2^(b+c) := by
    rw [Nat.mul_comm 2 (b+c)]
    exact Nat.le_trans hh (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))
  -- To reduce the exponent, use monotonicity of (9/2)^s via cancellation.
  have h5 := Nat.pow_le_pow_left h2 5
  rw [Nat.mul_pow,← Nat.pow_mul,← Nat.pow_mul,← Nat.pow_mul] at h5
  let S := 5*(b+c)
  have hs : 3*A≤S := hA
  have hp : 3^(2*S) ≤ (28*r)^10*2^S := by
    simpa [S,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h5
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hs
  rw [hk, Nat.mul_add, Nat.pow_add 3, Nat.pow_add 2] at hp
  have hmul : 2^k≤3^(2*k) := by
    calc
      2^k ≤ 9^k := Nat.pow_le_pow_left (by decide) _
      _ = 3^(2*k) := (Nat.pow_mul 3 2 k).symm
  apply Nat.le_of_mul_le_mul_right (c:=2^k) _ (Nat.two_pow_pos _)
  calc
    3^(6*A)*2^k ≤ 3^(6*A)*3^(2*k) := Nat.mul_le_mul_left _ hmul
    _ = 3^(2*(3*A))*3^(2*k) := by rw [show 6*A=2*(3*A) by omega]
    _ ≤ (28*r)^10*(2^(3*A)*2^k) := hp
    _ = ((28*r)^10*2^(3*A))*2^k := by ac_rfl

private theorem tail1 (A : Nat) (hA : 300≤A) :
    (378*A)^5*27^A ≤ 8^5*32^A :=
  tail_le A 5 378 27 32 (8^5) hA (by decide +kernel) (by decide)

private theorem tail2 (A : Nat) (hA : 300≤A) :
    (756*A)^10*81^A ≤ 8^10*128^A :=
  tail_le A 10 756 81 128 (8^10) hA (by decide +kernel) (by decide)

/-- Every putative three-token period satisfying either denominator bound
    and the slope/first-difference upper bound has A<300. -/
theorem valuation_bound {A r : Nat} (hupper : 8*2^A*r < 27*A*3^A)
    (hlower : 3^(2*A)≤(14*r)^5 ∨ 3^(6*A)≤(28*r)^10*2^(3*A)) : A<300 := by
  by_cases hA : A<300
  · exact hA
  exfalso
  have ha : 300≤A := by omega
  rcases hlower with h1|h2
  · have ht := Nat.pow_lt_pow_left (Nat.mul_lt_mul_of_pos_left hupper (by decide : 0<14)) (show 5≠0 by decide)
    have hp : 3^(2*A)*(8^5*32^A) < 3^(2*A)*((378*A)^5*27^A) := by
      calc
        _ = (8*2^A)^5*3^(2*A) := by
          rw [Nat.mul_pow,show (2^A)^5=32^A by rw [← Nat.pow_mul,Nat.mul_comm A 5,Nat.pow_mul]]; ac_rfl
        _ ≤ (8*2^A)^5*(14*r)^5 := Nat.mul_le_mul_left _ h1
        _ = (14*(8*2^A*r))^5 := by rw [← Nat.mul_pow]; congr 1; ac_rfl
        _ < (14*(27*A*3^A))^5 := ht
        _ = 3^(2*A)*((378*A)^5*27^A) := by
          have he : 14*(27*A*3^A) = (378*A)*3^A := by change 14*(27*A*3^A) = ((14*27)*A)*3^A; ac_rfl
          rw [he,Nat.mul_pow,show (3^A)^5=3^(2*A)*27^A by
            rw [← Nat.pow_mul,Nat.mul_comm A 5,show 5*A=2*A+3*A by omega,Nat.pow_add,Nat.pow_mul 3 3 A]]; ac_rfl
    exact Nat.not_lt_of_ge (tail1 A ha) (Nat.lt_of_mul_lt_mul_left hp)
  · have ht := Nat.pow_lt_pow_left (Nat.mul_lt_mul_of_pos_left hupper (by decide : 0<28)) (show 10≠0 by decide)
    have hp : (3^(6*A)*2^(3*A))*(8^10*128^A) < (3^(6*A)*2^(3*A))*((756*A)^10*81^A) := by
      calc
        _ = (8*2^A)^10*3^(6*A) := by
          rw [Nat.mul_pow,show (2^A)^10=2^(3*A)*128^A by
            rw [← Nat.pow_mul,Nat.mul_comm A 10,show 10*A=3*A+7*A by omega,Nat.pow_add,Nat.pow_mul 2 7 A]]; ac_rfl
        _ ≤ (8*2^A)^10*((28*r)^10*2^(3*A)) := Nat.mul_le_mul_left _ h2
        _ = (28*(8*2^A*r))^10*2^(3*A) := by rw [Nat.mul_pow (28) (8*2^A*r),Nat.mul_pow (8*2^A) r,Nat.mul_pow (28) r]; ac_rfl
        _ < (28*(27*A*3^A))^10*2^(3*A) := Nat.mul_lt_mul_of_pos_right ht (Nat.two_pow_pos _)
        _ = _ := by
          have he : 28*(27*A*3^A) = (756*A)*3^A := by change 28*(27*A*3^A) = ((28*27)*A)*3^A; ac_rfl
          rw [he,Nat.mul_pow,show (3^A)^10=3^(6*A)*81^A by
            rw [← Nat.pow_mul,Nat.mul_comm A 10,show 10*A=6*A+4*A by omega,Nat.pow_add,Nat.pow_mul 3 4 A]]; ac_rfl
    exact Nat.not_lt_of_ge (tail2 A ha) (Nat.lt_of_mul_lt_mul_left hp)

/-- A cap for the reduced slope denominator, using both the periodic affine
    equation and the integer first-difference constraint. -/
def slopeCap (A D : Nat) : Nat :=
  (2^(A+3+D)-3^A).gcd ((2^D-1)^2)

/-- The second-coordinate denominator divides this integer. -/
def betaCap (A D : Nat) : Nat :=
  let P := 2^(A+3)
  let R := 3^A
  let g := slopeCap A D
  ((P-R)+(R-P)).gcd (D*(g/g.gcd (2^D-1)))

def possible (A D : Nat) : Bool := decide (
  0<D ∧ D≤A ∧ 3^A<2^(A+D) ∧ 2^(A+3+D)<3^(A+3) ∧
  1<slopeCap A D ∧
  (A<7 ∨ 3^(2*A)≤(14*betaCap A D)^5 ∨
    3^(6*A)≤(28*betaCap A D)^10*2^(3*A)))

def checkedPairs : Bool := (List.range 300).all fun A =>
  (List.range (A+1)).all fun D => !possible A D || (A==6 && D==5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem check_pairs : checkedPairs = true := by decide +kernel

theorem only_pair {A D : Nat} (hA : A<300) (hD : D≤A)
    (hp : possible A D = true) : A=6 ∧ D=5 := by
  have h := List.all_eq_true.mp check_pairs A (List.mem_range.mpr hA)
  have h' := List.all_eq_true.mp h D (List.mem_range.mpr (by omega))
  simpa [hp] using h'

/-- The negative-beta branch applies for total valuation A≥7. -/
theorem denominator_dominates (A : Nat) (hA : 7≤A) : 2*2^(A+3)≤3^A := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hA
  clear hA
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      2*2^(7+(k+1)+3) = 2*(2*2^(7+k+3)) := by
        rw [show 7+(k+1)+3=(7+k+3)+1 by omega,Nat.pow_succ]; ac_rfl
      _ ≤ 2*3^(7+k) := Nat.mul_le_mul_left _ ih
      _ ≤ 3*3^(7+k) := Nat.mul_le_mul_right _ (by decide)
      _ = 3^(7+(k+1)) := by rw [show 7+(k+1)=(7+k)+1 by omega,Nat.pow_succ,Nat.mul_comm]

/-- The slope product and first-difference identity yield the strict
    beta-denominator upper bound used in valuation_bound. -/
theorem beta_upper {A D r : Nat} (hD : 0<D) (hDA : D≤A)
    (hr : r≤D*(2^D-1)) (hs : 2^(A+3+D)<3^(A+3)) :
    8*2^A*r < 27*A*3^A := by
  have hp : 2^D-1<2^D := by have := Nat.two_pow_pos D; omega
  have hr' : r<A*2^D := Nat.lt_of_le_of_lt hr
    (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hp hD) (Nat.mul_le_mul_right _ hDA))
  calc
    _ < 8*2^A*(A*2^D) := Nat.mul_lt_mul_of_pos_left hr' (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
    _ = A*2^(A+3+D) := by rw [Nat.pow_add 2 (A+3) D,Nat.pow_add 2 A 3]; change _ = A*(2^A*8*2^D); ac_rfl
    _ < A*3^(A+3) := Nat.mul_lt_mul_of_pos_left hs (by omega)
    _ = _ := by rw [Nat.pow_add 3 A 3]; change A*(3^A*27) = 27*A*3^A; ac_rfl

/-- Conditional on the exact period's slope/beta denominator constraints,
    the only remaining aggregate parameter pair is A=6,D=5. -/
theorem aggregate_only {A D r : Nat} (hD : 0<D) (hDA : D≤A)
    (hs0 : 3^A<2^(A+D)) (hs1 : 2^(A+3+D)<3^(A+3))
    (hg : 1<slopeCap A D) (hr : r≤betaCap A D) (hrH : r≤D*(2^D-1))
    (hlow : A<7 ∨ 3^(2*A)≤(14*r)^5 ∨ 3^(6*A)≤(28*r)^10*2^(3*A)) :
    A=6 ∧ D=5 := by
  have hA : A<300 := by
    rcases hlow with h|h
    · omega
    · exact valuation_bound (beta_upper hD hDA hrH hs1) h
  apply only_pair hA hDA
  unfold possible
  apply decide_eq_true
  refine ⟨hD,hDA,hs0,hs1,hg,?_⟩
  rcases hlow with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Nat.le_trans h (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hr) _)))
  · exact Or.inr (Or.inr (Nat.le_trans h (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hr) _))))
def tokens : List (Nat × Nat) := (List.range 7).flatMap fun a =>
  (List.range (a+1)).map fun d => (a,d)

def candidate (t u v : Nat × Nat) : Bool :=
  let (a,d) := t
  let (b,e) := u
  let (c,f) := v
  let P1 := 2^(a+1+d)
  let P2 := 2^(b+1+e)
  let P3 := 2^(c+1+f)
  let R1 := 3^a
  let R2 := 3^b
  let R3 := 3^c
  let Q := P1*P2*P3-R1*R2*R3
  let n0 := R3*(R2*(R1+P1)+P1*P2)
  let n1 := R1*(R3*(R2+P2)+P2*P3)
  let n2 := R2*(R1*(R3+P3)+P3*P1)
  let q := Q/Q.gcd n0
  decide (a+b+c=6 ∧ d+e+f=5 ∧ 0<Q ∧
    Q<2*n0 ∧ n0<Q ∧ Q<2*n1 ∧ n1<Q ∧ Q<2*n2 ∧ n2<Q ∧
    1<q ∧ (31^2)%q=0)

def checkedTokens : Bool := tokens.all fun t => tokens.all fun u => tokens.all fun v => !candidate t u v

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem check_tokens : checkedTokens = true := by decide +kernel

theorem token_mem {a d : Nat} (ha : a≤6) (hd : d≤a) : (a,d)∈tokens := by
  unfold tokens
  apply List.mem_flatMap.mpr
  exact ⟨a,List.mem_range.mpr (by omega),List.mem_map.mpr ⟨d,List.mem_range.mpr (by omega),rfl⟩⟩

theorem no_tokens {a b c d e f : Nat} (hA : a+b+c=6)
    (hd : d≤a) (he : e≤b) (hf : f≤c) : candidate (a,d) (b,e) (c,f)=false := by
  have h := List.all_eq_true.mp check_tokens _ (token_mem (by omega : a≤6) hd)
  have h' := List.all_eq_true.mp h _ (token_mem (by omega : b≤6) he)
  have h'' := List.all_eq_true.mp h' _ (token_mem (by omega : c≤6) hf)
  exact (Bool.not_eq_true' _).mp h''

#print axioms large_valuation
#print axioms close_numerators
#print axioms valuation_bound
#print axioms check_pairs
#print axioms only_pair
#print axioms aggregate_only
#print axioms denominator_dominates
#print axioms check_tokens
#print axioms no_tokens

end BB6.Agent10ThreeTokenPeriod
