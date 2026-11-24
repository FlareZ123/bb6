import Q0HalfStep

namespace BB429Q0Macro.HalfStep
set_option maxHeartbeats 10000000

/-- Base-four word: earliest digit is least significant. -/
def digits : List Bool → Int
  | [] => 0
  | d::w => (bit d : Int) + 4*digits w

def modulus (w : List Bool) : Int := 4^w.length

def lengthCost : Bool → List Bool → Nat
  | _, [] => 0
  | s,d::w => len s d + lengthCost (!s) w

def error : Bool → List Bool → Int
  | _, [] => 0
  | s,d::w => (off s d : Int) - (bit d : Int)*lengthCost s (d::w) + 4*error (!s) w

theorem modulus_pos (w : List Bool) : 0 < modulus w := by
  exact Int.pow_pos (by decide)

theorem modulus_cons (d : Bool) (w : List Bool) : modulus (d::w)=4*modulus w := by
  simp [modulus,List.length_cons,Int.pow_succ,Int.mul_comm]

theorem digits_bounds (w : List Bool) : 0≤digits w ∧ 3*digits w<modulus w := by
  induction w with
  | nil => decide
  | cons d w ih =>
    rw [modulus_cons,digits]
    cases d <;> simp [bit] <;> omega

theorem cost_append (s : Bool) (w v : List Bool) :
    lengthCost s (w++v)=lengthCost s w+lengthCost (phase s w) v := by
  induction w generalizing s with
  | nil => simp [phase,lengthCost]
  | cons d w ih => simp only [List.cons_append,lengthCost,phase_cons,ih]; omega

theorem digits_snoc (w : List Bool) (d : Bool) : digits (w++[d])=digits w+modulus w*bit d := by
  induction w with
  | nil => simp [digits,modulus]
  | cons x w ih => rw [List.cons_append,digits,ih,digits,modulus_cons]; grind

theorem modulus_snoc (w : List Bool) (d : Bool) : modulus (w++[d])=4*modulus w := by
  simp [modulus,List.length_append,Int.pow_succ,Int.mul_comm]

theorem error_snoc (s : Bool) (w : List Bool) (d : Bool) :
    error s (w++[d])=error s w-(len (phase s w) d : Int)*digits w+
      modulus w*((off (phase s w) d : Int)-(bit d : Int)*len (phase s w) d) := by
  induction w generalizing s with
  | nil => simp [error,phase,digits,modulus,lengthCost]
  | cons x w ih =>
    simp only [List.cons_append,error,ih,phase_cons,modulus_cons,digits,cost_append,lengthCost,Int.natCast_add]
    grind

/-- Alternating phases give tighter errors than a phase-independent estimate. -/
theorem error_bounds (s : Bool) (w : List Bool) :
    if phase s w then -7*modulus w < 15*error s w ∧ 15*error s w<13*modulus w
    else -3*modulus w < 15*error s w ∧ 15*error s w<7*modulus w := by
  let Q := fun w => if phase s w then -7*modulus w < 15*error s w ∧ 15*error s w<13*modulus w
    else -3*modulus w < 15*error s w ∧ 15*error s w<7*modulus w
  have step (w : List Bool) (d : Bool) (ih : Q w) : Q (w++[d]) := by
    dsimp [Q] at ih ⊢
    rw [error_snoc,modulus_snoc,phase_append]
    have hD := digits_bounds w
    have hM := modulus_pos w
    cases h : phase s w <;> simp only [h, Bool.false_eq_true, ite_false, ite_true] at ih <;> cases d <;> simp [phase,len,off,bit] <;> omega
  have all (v : List Bool) : Q v.reverse := by
    induction v with
    | nil => cases s <;> decide
    | cons d v ih => rw [List.reverse_cons]; exact step _ _ ih
  simpa only [List.reverse_reverse] using all w.reverse

/-- Exact integer identity, with no nonnegative-rank-offset assumption. -/
theorem trace_formula {s w p y P Y} (h : Trace s w p y P Y) :
    P=p+lengthCost s w ∧ modulus w * Y = (y:Int)+digits w*P+error s w := by
  induction h with
  | nil => simp [lengthCost,modulus,digits,error]
  | @cons s d w p y P Y hd ht ih =>
    rcases ih with ⟨hr,hy⟩
    constructor
    · simp [lengthCost]; omega
    · rw [modulus_cons,digits,error,lengthCost]
      have he : 4*((numerator s d p y/4 : Nat):Int)=(numerator s d p y : Int) := by omega
      have he' : 4*((numerator s d p y/4 : Nat):Int)=(y:Int)+(bit d:Int)*p+off s d := by
        rw [he]; simp [numerator]
      have hy' : 4*modulus w*(Y:Int)=4*((numerator s d p y/4 : Nat):Int)+4*(digits w*(P:Int))+4*error (!s) w := by
        rw [Int.mul_assoc,hy]; omega
      rw [he'] at hy'
      simp only [Int.natCast_add,Int.add_mul,Int.mul_assoc]
      cases d <;> simp [bit] at * <;> omega

/-- A near-power state with at least k past steps has a signed carry in a
    strip of width O(|q|+a), independently of 4^k. -/
theorem signed_strip {s w p y P Y : _} (h : Trace s w p y P Y) (hy : 0<y) (hc : 3*y<p)
    (a : Nat) (q : Int) (hr : (P:Int)=a*modulus w+q) (hqsize : 5*q≤2*modulus w) :
    let e : Int := (Y:Int)-a*digits w
    min q 0 - 2 ≤ 3*e ∧ 3*e ≤ max q 0 + a + 2 := by
  dsimp
  obtain ⟨hp,hf⟩ := trace_formula h
  have hD := digits_bounds w
  have hM := modulus_pos w
  have hE := error_bounds s w
  have hE' : -modulus w < error s w ∧ error s w<modulus w := by
    split at hE <;> omega
  have hEhi : 15*error s w<13*modulus w := by
    split at hE <;> omega
  have hc' : 3*(y:Int)<(P:Int) := by omega
  let e : Int := (Y:Int)-a*digits w
  have he : modulus w*e = (y:Int)+digits w*q+error s w := by dsimp [e]; grind
  change min q 0 - 2 ≤ 3*e ∧ 3*e ≤ max q 0 + (a:Int) + 2
  by_cases hq : 0≤q
  · rw [Int.min_eq_right hq,Int.max_eq_left hq]
    have hDQ := Int.mul_nonneg hD.1 hq
    have hDQ' := Int.mul_le_mul_of_nonneg_right (show 3*digits w≤modulus w by omega) hq
    have lo : -modulus w < modulus w*e := by omega
    have hi : modulus w*(3*e) < modulus w*(q+(a:Int)+3) := by
      rw [Int.mul_add,Int.mul_add,←Int.mul_assoc,Int.mul_comm (modulus w) 3,Int.mul_assoc,he,Int.mul_comm (modulus w) (a:Int)]
      rw [Int.mul_assoc] at hDQ'
      omega
    have h₁ : modulus w*(-1)<modulus w*e := by simpa using lo
    have h₂ := Int.lt_of_mul_lt_mul_left h₁ (show 0≤modulus w by omega)
    have h₃ := Int.lt_of_mul_lt_mul_left hi (show 0≤modulus w by omega)
    omega
  · have hq' : q≤0 := by omega
    rw [Int.min_eq_left hq',Int.max_eq_right hq']
    have hDQ := Int.mul_nonpos_of_nonneg_of_nonpos hD.1 hq'
    have hDQ' := Int.mul_le_mul_of_nonpos_right (show 3*digits w≤modulus w by omega) hq'
    have lo : modulus w*(q-3)<modulus w*(3*e) := by
      rw [Int.mul_sub,←Int.mul_assoc,Int.mul_comm (modulus w) 3,Int.mul_assoc,he]
      rw [Int.mul_assoc] at hDQ'
      omega
    have hi : modulus w*(3*e)<modulus w*((a:Int)+3) := by
      rw [Int.mul_add,←Int.mul_assoc,Int.mul_comm (modulus w) 3,Int.mul_assoc,he,Int.mul_comm (modulus w) (a:Int)]
      omega
    have h₁ := Int.lt_of_mul_lt_mul_left lo (show 0≤modulus w by omega)
    have h₂ := Int.lt_of_mul_lt_mul_left hi (show 0≤modulus w by omega)
    omega

/-- Rolling the past word forward gives an exact signed update. -/
theorem rolling {r d s : Bool} {w : List Bool} {a : Nat} {q e q' e' : Int}
    (h : 4*((a:Int)*digits (w++[d])+e') = (a:Int)*digits (r::w)+e +
      (bit d : Int)*((a:Int)*modulus (r::w)+q)+off s d)
    (hq : q'=q+len s d) :
    4*e'=e+(a:Int)*bit r+(bit d : Int)*q+off s d ∧ q'=q+len s d := by
  rw [digits_snoc,digits,modulus_cons] at h
  exact ⟨by grind,hq⟩

#print axioms trace_formula
#print axioms signed_strip
#print axioms rolling
end BB429Q0Macro.HalfStep
