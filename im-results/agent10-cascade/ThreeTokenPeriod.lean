import Std
namespace BB6.Agent10ThreeTokenPeriod
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- Abstract integer consequence of the two independent beta lower bounds. -/
theorem beta_lower {a b c r : Nat} (hab : a ≤ b)
    (hc : 3^c ≤ 28*r) (hp : 3^(a+b) ≤ (28*r)*2^a) :
    3^(4*(a+b+c)) ≤ (28*r)^10 := by
  have h2 := Nat.pow_le_pow_left hp 2
  rw [← Nat.pow_mul 3 (a+b) 2, Nat.mul_pow (28*r) (2^a) 2, ← Nat.pow_mul 2 a 2] at h2
  have h2' : 3^((a+b)*2) ≤ (28*r)^2 * 2^(a+b) :=
    Nat.le_trans h2 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (show 0<2 by decide) (show a*2≤a+b by omega)))
  have h3 := Nat.pow_le_pow_left h2' 3
  rw [← Nat.pow_mul 3 ((a+b)*2) 3,Nat.mul_pow ((28*r)^2) (2^(a+b)) 3,← Nat.pow_mul (28*r) 2 3,← Nat.pow_mul 2 (a+b) 3] at h3
  have h9 : 2^((a+b)*3) ≤ 3^((a+b)*2) := by
    rw [Nat.mul_comm (a+b) 3,Nat.mul_comm (a+b) 2,Nat.pow_mul,Nat.pow_mul]
    exact Nat.pow_le_pow_left (by decide : 2^3 ≤ 3^2) _
  have h6 : 3^((a+b)*4) * 3^((a+b)*2) ≤ (28*r)^6 * 3^((a+b)*2) := by
    calc
      _ = 3^((a+b)*2*3) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ (28*r)^(2*3) * 2^((a+b)*3) := h3
      _ ≤ (28*r)^6 * 3^((a+b)*2) := Nat.mul_le_mul_left _ h9
  have h4 := Nat.le_of_mul_le_mul_right h6 (Nat.pow_pos (by decide))
  have hc4 := Nat.pow_le_pow_left hc 4
  rw [← Nat.pow_mul] at hc4
  calc
    _ = 3^((a+b)*4) * 3^(c*4) := by rw [← Nat.pow_add]; congr 1; omega
    _ ≤ (28*r)^6 * (28*r)^4 := Nat.mul_le_mul h4 hc4
    _ = _ := by rw [← Nat.pow_add]

/-- The exponential dominates the polynomial from A=303 onwards. -/
theorem tail_step (n : Nat) (hn : 303 ≤ n)
    (h : (95*n)^10*729^n ≤ 1024^n) : (95*(n+1))^10*729^(n+1) ≤ 1024^(n+1) := by
  have hlin : 30*(n+1) ≤ 31*n := by omega
  have hpow := Nat.pow_le_pow_left hlin 10
  rw [Nat.mul_pow 30 (n+1) 10, Nat.mul_pow 31 n 10] at hpow
  have hcoef : 729*31^10 ≤ 1024*30^10 := by decide +kernel
  have hcomp : 30^10*((95*(n+1))^10*729^(n+1)) ≤ 30^10*1024^(n+1) := by
    calc
      _ = (30^10*(n+1)^10)*(95^10*(729*729^n)) := by rw [Nat.mul_pow 95 (n+1) 10,Nat.pow_succ 729 n]; ac_rfl
      _ ≤ (31^10*n^10)*(95^10*(729*729^n)) := Nat.mul_le_mul_right _ hpow
      _ = (729*31^10)*((95*n)^10*729^n) := by rw [Nat.mul_pow 95 n 10]; ac_rfl
      _ ≤ (1024*30^10)*1024^n := Nat.mul_le_mul hcoef h
      _ = _ := by rw [Nat.pow_succ 1024 n]; ac_rfl
  exact Nat.le_of_mul_le_mul_left hcomp (by decide)

theorem tail_bound (A : Nat) (hA : 303 ≤ A) : (95*A)^10*729^A ≤ 1024^A := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hA
  clear hA
  induction k with
  | zero => decide +kernel
  | succ k ih => exact tail_step (303+k) (by omega) ih

theorem valuation_bound {A D r : Nat} (hD : 0<D) (hDA : D≤A)
    (hlo : 3^(4*A) ≤ (28*r)^10) (hhi : r≤D*(2^D-1))
    (hs : 2^(A+3+D)<3^(A+3)) : A<303 := by
  have hp : 2^D-1<2^D := by have := Nat.two_pow_pos D; omega
  have hr : r<A*2^D := Nat.lt_of_le_of_lt hhi (Nat.lt_of_lt_of_le
    (Nat.mul_lt_mul_of_pos_left hp hD) (Nat.mul_le_mul_right _ hDA))
  have hh : 8*(2^A*r)<27*A*3^A := by
    calc
      _ < 8*(2^A*(A*2^D)) := Nat.mul_lt_mul_of_pos_left
        (Nat.mul_lt_mul_of_pos_left hr (Nat.two_pow_pos _)) (by decide)
      _ = A*2^(A+3+D) := by rw [Nat.pow_add 2 (A+3) D,Nat.pow_add 2 A 3]; change _ = A*(2^A*8*2^D); ac_rfl
      _ < A*3^(A+3) := Nat.mul_lt_mul_of_pos_left hs (by omega)
      _ = _ := by rw [Nat.pow_add 3 A 3]; change A*(3^A*27) = _; ac_rfl
  have hh' : 2^A*(28*r) < 95*A*3^A := by
    have h : 8*(2^A*(28*r)) < 8*(95*A*3^A) := by
      calc
        _ = 28*(8*(2^A*r)) := by ac_rfl
        _ < 28*(27*A*3^A) := Nat.mul_lt_mul_of_pos_left hh (by decide)
        _ = (28*27)*(A*3^A) := by ac_rfl
        _ ≤ (8*95)*(A*3^A) := Nat.mul_le_mul_right _ (by decide)
        _ = _ := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_left h
  have h10 := Nat.pow_lt_pow_left hh' (show 10≠0 by decide)
  rw [Nat.mul_pow (2^A) (28*r) 10, Nat.mul_pow (95*A) (3^A) 10] at h10
  rw [← Nat.pow_mul 2 A 10,Nat.mul_comm A 10,Nat.pow_mul 2 10 A,
      ← Nat.pow_mul 3 A 10,Nat.mul_comm A 10,Nat.pow_mul 3 10 A] at h10
  change 1024^A*(28*r)^10 < (95*A)^10*59049^A at h10
  have hcancel : 1024^A*81^A < ((95*A)^10*729^A)*81^A := by
    calc
      _ = 1024^A*3^(4*A) := by rw [Nat.pow_mul]
      _ ≤ 1024^A*(28*r)^10 := Nat.mul_le_mul_left _ hlo
      _ < (95*A)^10*59049^A := h10
      _ = _ := by rw [show 59049=729*81 by decide,Nat.mul_pow 729 81 A]; ac_rfl
  have hlt := Nat.lt_of_mul_lt_mul_right hcancel
  by_cases hn : A<303
  · exact hn
  ·
    have ht := tail_bound A (by omega)
    omega

/-- For each possible total valuation and level increment, the rational
    beta denominator must divide this exact common cap. -/
def cap (A D : Nat) : Nat :=
  let P := 2^(A+3)
  let R := 3^A
  (P-R+(R-P)).gcd (D*(2^D-1))

def eligible (A D : Nat) : Bool := decide
  (0<D ∧ D≤A ∧ 3^A<2^(A+D) ∧ 2^(A+3+D)<3^(A+3) ∧ 3^(4*A)≤(28*cap A D)^10)

/-- Two possible increments suffice: 27<32 bounds the three-token band. -/
def dmin (A : Nat) : Nat := (3^A).log2+1-A

theorem D_choices {A D : Nat} (hlo : 3^A<2^(A+D)) (hhi : 2^(A+3+D)<3^(A+3)) :
    D=dmin A ∨ D=dmin A+1 := by
  have hpos : 3^A ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide))
  have hlog : A≤(3^A).log2 := (Nat.le_log2 hpos).2 (Nat.pow_le_pow_left (by decide) _)
  have hdlo := (Nat.log2_lt hpos).2 hlo
  have h27 : 3^(A+3)<2^((3^A).log2+6) := by
    calc
      _ = 27*3^A := by rw [Nat.pow_add 3 A 3]; change 3^A*27=27*3^A; ac_rfl
      _ < 27*2^((3^A).log2+1) := Nat.mul_lt_mul_of_pos_left (Nat.lt_log2_self) (by decide)
      _ ≤ 32*2^((3^A).log2+1) := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by
        let k := (3^A).log2+1
        change 32*2^k=2^(k+5)
        calc
          _ = 2^k*2^5 := by exact Nat.mul_comm _ _
          _ = _ := (Nat.pow_add 2 k 5).symm
  have hdhi := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).1 (Nat.lt_trans hhi h27)
  unfold dmin
  omega

def capCheck : Bool := (List.range 295).all fun i =>
  let A := i+8
  !eligible A (dmin A) && !eligible A (dmin A+1)

theorem cap_checked : capCheck=true := by decide +kernel

theorem no_large_cap {A D : Nat} (hA : 8≤A) (hA' : A<303)
    (hlo : 3^A<2^(A+D)) (hhi : 2^(A+3+D)<3^(A+3)) : eligible A D=false := by
  have hi : A-8 ∈ List.range 295 := List.mem_range.mpr (by omega)
  have h := List.all_eq_true.mp cap_checked _ hi
  have he : A-8+8=A := by omega
  simp only [he, Bool.and_eq_true] at h
  rcases D_choices hlo hhi with rfl | rfl
  · exact (Bool.not_eq_true' _).mp h.1
  · exact (Bool.not_eq_true' _).mp h.2

/-- Combining the tail and cap tests forces all candidate totals below 8. -/
theorem small_total {A D r : Nat} (hD : 0<D) (hDA : D≤A)
    (hlo : 3^(4*A) ≤ (28*r)^10) (hr : r∣D*(2^D-1))
    (hrV : r∣2^(A+3)-3^A+(3^A-2^(A+3)))
    (hbandLo : 3^A<2^(A+D)) (hbandHi : 2^(A+3+D)<3^(A+3)) : A<8 := by
  have hpow : 0<2^D := Nat.two_pow_pos D
  have hH : 0<2^D-1 := by
    have := Nat.pow_lt_pow_right (by decide : 1<2) hD
    simp only [Nat.pow_zero] at this
    omega
  have hhi : r≤D*(2^D-1) := Nat.le_of_dvd (Nat.mul_pos hD hH) hr
  have hA := valuation_bound hD hDA hlo hhi hbandHi
  by_cases h : A<8
  · exact h
  · have hrCap : r∣cap A D := Nat.dvd_gcd hrV hr
    have hcapPos : 0<cap A D := Nat.gcd_pos_of_pos_right _ (Nat.mul_pos hD hH)
    have hc := Nat.le_of_dvd hcapPos hrCap
    have hcPow := Nat.pow_le_pow_left (Nat.mul_le_mul_left 28 hc) 10
    have he : eligible A D=true := decide_eq_true ⟨hD,hDA,hbandLo,hbandHi,Nat.le_trans hlo hcPow⟩
    rw [no_large_cap (by omega) hA hbandLo hbandHi] at he
    contradiction

/-- Necessary strict band constraints, including zero-valuation tokens. -/
def admissible (a d : Nat) : Bool := decide (3*3^a<2^(a+2+d) ∧ 2^(a+d)<2*3^a)

def tokens : List (Nat × Nat) := (List.range 8).flatMap fun a =>
  ((List.range (a+1)).filter (admissible a)).map fun d => (a,d)

def candidate (t u v : Nat × Nat) : Bool :=
  let (a,d) := t
  let (b,e) := u
  let (c,f) := v
  let A := a+b+c
  let D := d+e+f
  let P1 := 2^(a+1+d)
  let P2 := 2^(b+1+e)
  let P3 := 2^(c+1+f)
  let R1 := 3^a
  let R2 := 3^b
  let R3 := 3^c
  let Q := P1*P2*P3-R1*R2*R3
  let n := R3*(R1*R2+P1*R2+P1*P2)
  let n1 := R1*(R2*R3+P2*R3+P2*P3)
  let n2 := R2*(R3*R1+P3*R1+P3*P1)
  let q := Q/Q.gcd n
  let P := 2^(A+3)
  let R := 3^A
  let V := P-R+(R-P)
  let U := R3*(R1*R2+2^(a+1)*R2+2^(a+b+2))
  let r := V/V.gcd U
  let H := 2^D-1
  decide (A<8 ∧ 0<D ∧ 0<Q ∧ Q<2*n ∧ n<Q ∧ Q<2*n1 ∧ n1<Q ∧ Q<2*n2 ∧ n2<Q ∧
    1<q ∧ q.gcd 6=1 ∧ H^2 % q=0 ∧ q/q.gcd H=r/r.gcd D)

def smallCheck : Bool := tokens.all fun t => tokens.all fun u => tokens.all fun v => !candidate t u v

theorem small_checked : smallCheck=true := by decide +kernel

theorem token_mem {a d : Nat} (ha : a<8) (hd : d≤a) (h : admissible a d=true) : (a,d)∈tokens := by
  unfold tokens
  exact List.mem_flatMap.mpr ⟨a,List.mem_range.mpr ha,
    List.mem_map.mpr ⟨d,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),h⟩,rfl⟩⟩

theorem no_small_candidate {a b c d e f : Nat} (hA : a+b+c<8)
    (hd : d≤a) (he : e≤b) (hf : f≤c)
    (ht : admissible a d=true) (hu : admissible b e=true) (hv : admissible c f=true) :
    candidate (a,d) (b,e) (c,f)=false := by
  have h1 := List.all_eq_true.mp small_checked _ (token_mem (by omega) hd ht)
  have h2 := List.all_eq_true.mp h1 _ (token_mem (by omega) he hu)
  have h3 := List.all_eq_true.mp h2 _ (token_mem (by omega) hf hv)
  exact (Bool.not_eq_true' _).mp h3

#print axioms beta_lower
#print axioms tail_bound
#print axioms valuation_bound
#print axioms cap_checked
#print axioms no_large_cap
#print axioms small_total
#print axioms small_checked
#print axioms no_small_candidate
end BB6.Agent10ThreeTokenPeriod
