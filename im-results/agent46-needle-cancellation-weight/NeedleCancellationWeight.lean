import Std

namespace NeedleCancellationWeight

/-- S is the sum of the previous inverse denominators' dyadic exponents. -/
structure Weight (K n S L : Nat) (d : Int) : Prop where
  exponent : n = K+1+S
  denominator : 2^S ≤ L
  upper : d < 2*(L:Int)
  lower : -2*(S:Int)*(L:Int) ≤ d

theorem root (K : Nat) : Weight K (K+1) 0 1 0 := by
  constructor <;> simp

theorem step (K n S L m : Nat) (d : Int) (hm : 0<m)
    (h : Weight K n S L d) :
    Weight K (n+m) (S+m) (L*(2^m+3))
      ((2:Int)^m*(d+(L:Int)*(5-2*(m:Int)))) := by
  have hL : 0<L := Nat.lt_of_lt_of_le (Nat.two_pow_pos S) h.denominator
  have hLi : 0<(L:Int) := by omega
  have hp : 0<(2:Int)^m := Int.pow_pos (by decide)
  constructor
  · have he := h.exponent; omega
  · rw [Nat.pow_add]
    exact Nat.mul_le_mul h.denominator (by omega)
  · have hsmall : (2:Int)^m*(5-2*(m:Int))≤6 := by
      by_cases h1 : m=1
      · subst m; decide
      by_cases h2 : m=2
      · subst m; decide
      exact Int.le_trans (Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hp) (by omega)) (by decide)
    have hmul := Int.mul_le_mul_of_nonneg_right hsmall (Int.le_of_lt hLi)
    have hstrict := Int.mul_lt_mul_of_pos_left h.upper hp
    push_cast
    grind
  · have hbase : -2*((S:Int)+(m:Int))*(L:Int) ≤ d+(L:Int)*(5-2*(m:Int)) := by
      have hh := h.lower
      grind
    have hscale := Int.mul_le_mul_of_nonneg_left hbase (Int.le_of_lt hp)
    have hneg : -2*((S:Int)+(m:Int))*(L:Int) ≤ 0 := by
      exact Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
    push_cast
    grind

/-- A cancellation at valuation parameter m≥4 consumes a limited portion
of the terminal exponent budget, regardless of the reverse history. -/
theorem cancellation_budget (K n S L m : Nat) (d : Int)
    (h : Weight K n S L d) (hm : 4≤m) (hdiv : n%m=0)
    (hc : d+(L:Int)*(5-2*(m:Int))= -(-3:Int)^(n/m)) :
    (5*m-8)*S < 8*(K+1) := by
  have hL : 0<L := Nat.lt_of_lt_of_le (Nat.two_pow_pos S) h.denominator
  have hLi : 0<(L:Int) := by omega
  have hC : d+(L:Int)*(5-2*(m:Int)) < -(L:Int) := by
    have hh := Int.mul_le_mul_of_nonneg_left (show 5-2*(m:Int)≤ -3 by omega) (Int.le_of_lt hLi)
    have hu := h.upper
    omega
  have hAbs : (d+(L:Int)*(5-2*(m:Int))).natAbs=3^(n/m) := by
    rw [hc,Int.natAbs_neg,Int.natAbs_pow]
    rfl
  have hlt : L<3^(n/m) := by omega
  have hP : 2^S < (3:Nat)^(n/m) := Nat.lt_of_le_of_lt h.denominator hlt
  have hk : 0<n/m := by
    by_cases hz : n/m=0
    · rw [hz,Nat.pow_zero] at hlt; omega
    · exact Nat.pos_of_ne_zero hz
  have h5 := Nat.pow_lt_pow_left hP (by decide : 5≠0)
  rw [←Nat.pow_mul,←Nat.pow_mul] at h5
  have h38 : (3:Nat)^(5*(n/m)) < 2^(8*(n/m)) := by
    rw [Nat.pow_mul,Nat.pow_mul]
    exact Nat.pow_lt_pow_left (by decide : (3:Nat)^5<2^8) (by omega)
  have hpow : (2:Nat)^(S*5)<2^(8*(n/m)) := Nat.lt_trans h5 (by simpa [Nat.mul_comm 5] using h38)
  have hlog : S*5<8*(n/m) := by
    by_cases hh : S*5<8*(n/m)
    · exact hh
    · have hbad := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show 8*(n/m)≤S*5 by omega)
      omega
  have hmul := Nat.mul_lt_mul_of_pos_right hlog (show 0<m by omega)
  have he : m*(n/m)=n := by have hh:=Nat.div_add_mod n m; omega
  have hleft : (5*m-8)*S+8*S = (S*5)*m := by
    have hms : 8≤5*m := by omega
    rw [←Nat.add_mul,Nat.sub_add_cancel hms]
    ac_rfl
  have hright : (8*(n/m))*m=8*n := by rw [Nat.mul_assoc,Nat.mul_comm (n/m) m,he]
  rw [←hleft,hright] at hmul
  have hexp := h.exponent; omega

theorem no_late_cancellation (K n S L m : Nat) (d : Int)
    (h : Weight K n S L d) (hm : 4≤m) (hdiv : n%m=0)
    (hLate : 2*(K+1)≤3*S) :
    d+(L:Int)*(5-2*(m:Int))≠ -(-3:Int)^(n/m) := by
  intro hc
  have hb := cancellation_budget K n S L m d h hm hdiv hc
  have hm12 : 12≤5*m-8 := by omega
  have hh := Nat.mul_le_mul_right S hm12
  omega

/-- Each history starts at a terminal power and follows the exact affine
update. This relation permits even nonlegal arithmetic histories, so any
legal source history is covered without further side conditions. -/
inductive History (K : Nat) : Nat → Nat → Nat → Int → Prop where
  | root : History K (K+1) 0 1 0
  | extend {n S L : Nat} {d : Int} (m : Nat) (hm : 0<m)
      (h : History K n S L d) :
      History K (n+m) (S+m) (L*(2^m+3))
        ((2:Int)^m*(d+(L:Int)*(5-2*(m:Int))))

theorem history_weight {K n S L : Nat} {d : Int}
    (h : History K n S L d) : Weight K n S L d := by
  induction h with
  | root => exact root K
  | extend m hm h ih => exact step K _ _ _ m _ hm ih

/-- Once cumulative prior weight reaches M, a further cancellation with
m≥M is impossible whenever the indicated quadratic threshold holds. -/
theorem no_second_large {K n S L m M : Nat} {d : Int}
    (h : History K n S L d) (hM : 4≤M) (hS : M≤S) (hm : M≤m)
    (hdiv : n%m=0) (hcut : 8*(K+1)≤(5*M-8)*M) :
    d+(L:Int)*(5-2*(m:Int))≠ -(-3:Int)^(n/m) := by
  intro hc
  have hb := cancellation_budget K n S L m d (history_weight h) (by omega) hdiv hc
  have hh : (5*M-8)*M≤(5*m-8)*S := Nat.mul_le_mul (by omega) hS
  omega

/-- All subsequent cancellation parameters are bounded by the same
monotone, cumulative-weight inequality, irrespective of depth. -/
theorem history_cancellation_budget {K n S L m : Nat} {d : Int}
    (h : History K n S L d) (hm : 4≤m) (hdiv : n%m=0)
    (hc : d+(L:Int)*(5-2*(m:Int))= -(-3:Int)^(n/m)) :
    (5*m-8)*S < 8*(K+1) :=
  cancellation_budget K n S L m d (history_weight h) hm hdiv hc

#print axioms root
#print axioms step
#print axioms cancellation_budget
#print axioms no_late_cancellation
#print axioms history_weight
#print axioms no_second_large
#print axioms history_cancellation_budget
end NeedleCancellationWeight
