import Std.Tactic

/-! Exact arithmetic adapter for the positive-budget drain. The abstract
recurrences below are the equations of Agent49CorrectionGrowth.excess and
.drift. No Turing-machine semantics or reachability are assumed here. -/
namespace BB6.Agent41FatalInverse

def base : Nat → Nat
  | 0 => 6
  | k+1 => 3 * base k + 1

theorem base_lower (k : Nat) : 3 * 3^k ≤ base k := by
  induction k with
  | zero => decide
  | succ k ih => rw [base, Nat.pow_succ]; omega

theorem base_power (k : Nat) : 2*base k+1 = 13*3^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [base, Nat.pow_succ]; omega

theorem pow_three_odd (k : Nat) : 3^k % 2 = 1 := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

/-- Number of ordinary ternary 1s and 2s among the first k digits. -/
def ordinary : Nat → Nat → Nat × Nat
  | 0, _ => (0,0)
  | k+1, t =>
    let c := ordinary k (t/3)
    (c.1 + (if t%3=1 then 1 else 0), c.2 + (if t%3=2 then 1 else 0))

/-- Counts of +1 and -1 in the first k balanced ternary digits. -/
def balanced : Nat → Nat → Nat × Nat
  | 0, _ => (0,0)
  | k+1, t =>
    let c := balanced k ((t+1)/3)
    (c.1 + (if t%3=1 then 1 else 0), c.2 + (if t%3=2 then 1 else 0))

structure DrainEquations (E J : Nat → Int) : Prop where
  E5 : E 5 = 8
  J5 : J 5 = -3
  E6 : E 6 = 4
  J6 : J 6 = 0
  E0 : ∀ q, 0<q → E (3*q) = E (q-1)
  E1 : ∀ q, E (3*q+1) = 4 + E q
  E2 : ∀ q, E (3*q+2) = 2 + E (q+1)
  J0 : ∀ q, 0<q → J (3*q) = 1 + J (q-1)
  J1 : ∀ q, J (3*q+1) = J q - 1
  J2 : ∀ q, J (3*q+2) = J (q+1) - 1

/-- Odd offsets strip ordinary ternary digits from the deviation. -/
theorem odd_offset (E J : Nat → Int) (h : DrainEquations E J) (k : Nat) :
    ∀ t, t < 3^k →
      E (base k - (2*t+1)) = 8 + 4*(ordinary k t).1 + 2*(ordinary k t).2 ∧
      J (base k - (2*t+1)) = (k:Int)-3-2*(ordinary k t).1-2*(ordinary k t).2 := by
  induction k with
  | zero =>
    intro t ht
    have ht0 : t=0 := by simpa using ht
    subst t
    simpa [base,ordinary] using And.intro h.E5 h.J5
  | succ k ih =>
    intro t ht
    let q := t/3
    let b := base k - (2*q+1)
    have hp : 3^(k+1)=3*3^k := by rw [Nat.pow_succ]; omega
    have hq : q < 3^k := by dsimp [q]; omega
    have hbase := base_lower k
    have hb : 0<b := by dsimp [b]; omega
    have hih := ih q hq
    change E b = _ ∧ J b = _ at hih
    have hr : t%3=0 ∨ t%3=1 ∨ t%3=2 := by omega
    rcases hr with hr | hr | hr
    · have he : base (k+1)-(2*t+1)=3*(b+1) := by simp only [base]; dsimp [b,q]; omega
      rw [he,h.E0 _ (by omega),h.J0 _ (by omega)]
      have hb' : b+1-1=b := by omega
      rw [hb', hih.1,hih.2]
      simp [ordinary,hr,q]
      <;> omega
    · have he : base (k+1)-(2*t+1)=3*b+1 := by simp only [base]; dsimp [b,q]; omega
      rw [he,h.E1,h.J1,hih.1,hih.2]
      simp [ordinary,hr,q]
      <;> omega
    · have he : base (k+1)-(2*t+1)=3*(b-1)+2 := by simp only [base]; dsimp [b,q]; omega
      rw [he,h.E2,h.J2]
      have hb' : b-1+1=b := by omega
      rw [hb',hih.1,hih.2]
      simp [ordinary,hr,q]
      <;> omega

/-- Even offsets strip balanced ternary digits from the deviation. -/
theorem even_offset (E J : Nat → Int) (h : DrainEquations E J) (k : Nat) :
    ∀ t, 2*t < 3^k →
      E (base k - 2*t) = 4*(k:Int)+4-2*(balanced k t).1-4*(balanced k t).2 ∧
      J (base k - 2*t) = -(k:Int)+2*(balanced k t).2 := by
  induction k with
  | zero =>
    intro t ht
    have ht0 : t=0 := by simp at ht; omega
    subst t
    simpa [base,balanced] using And.intro h.E6 h.J6
  | succ k ih =>
    intro t ht
    let q := (t+1)/3
    let b := base k - 2*q
    have hp : 3^(k+1)=3*3^k := by rw [Nat.pow_succ]; omega
    have hodd := pow_three_odd k
    have hq : 2*q < 3^k := by dsimp [q]; omega
    have hbase := base_lower k
    have hb : 0<b := by dsimp [b]; omega
    have hih := ih q hq
    change E b = _ ∧ J b = _ at hih
    have hr : t%3=0 ∨ t%3=1 ∨ t%3=2 := by omega
    rcases hr with hr | hr | hr
    · have he : base (k+1)-2*t=3*b+1 := by simp only [base]; dsimp [b,q]; omega
      rw [he,h.E1,h.J1,hih.1,hih.2]
      simp [balanced,hr,q]
      <;> omega
    · have he : base (k+1)-2*t=3*(b-1)+2 := by simp only [base]; dsimp [b,q]; omega
      rw [he,h.E2,h.J2]
      have hb' : b-1+1=b := by omega
      rw [hb',hih.1,hih.2]
      simp [balanced,hr,q]
      <;> omega
    · have he : base (k+1)-2*t=3*(b+1) := by simp only [base]; dsimp [b,q]; omega
      rw [he,h.E0 _ (by omega),h.J0 _ (by omega)]
      have hb' : b+1-1=b := by omega
      rw [hb',hih.1,hih.2]
      simp [balanced,hr,q]
      <;> omega

/-- Exact left-even third-coordinate image condition for the tuned family.
    The exponent p in the mathematical statement is k+1. -/
theorem left_image_iff (E J : Nat → Int) (h : DrainEquations E J)
    (k t : Nat) (ht : t < 3^k) :
    3*(base k-(2*t+1):Nat) + E (base k-(2*t+1)) + 2 =
      3*(base k:Int)-2*((k:Int)+1)+5 ↔
    (k:Int)+1 = 3*(t:Int)-1-2*(ordinary k t).1-(ordinary k t).2 := by
  have he := (odd_offset E J h k t ht).1
  have hb := base_lower k
  have hcast : (↑(base k-(2*t+1)) : Int) = (base k:Int)-2*(t:Int)-1 := by omega
  rw [he]
  omega

/-- Exact right-odd third-coordinate image condition for the tuned family. -/
theorem right_image_iff (E J : Nat → Int) (h : DrainEquations E J)
    (k t : Nat) (ht : 2*t < 3^k) :
    3*(base k-2*t:Nat) + E (base k-2*t) + 3 =
      3*(base k:Int)-2*((k:Int)+1)+5 ↔
    3*((k:Int)+1) = 3*(t:Int)+(balanced k t).1+2*(balanced k t).2+1 := by
  have he := (even_offset E J h k t ht).1
  have hb := base_lower k
  have hcast : (↑(base k-2*t) : Int) = (base k:Int)-2*(t:Int) := by omega
  rw [he]
  omega

/-- Ordinary ternary digit parity. -/
theorem ordinary_parity (k : Nat) : ∀ t, t < 3^k →
    t%2 = (ordinary k t).1%2 := by
  induction k with
  | zero =>
    intro t ht
    have hz : t=0 := by simpa using ht
    subst t
    decide
  | succ k ih =>
    intro t ht
    have hp : 3^(k+1)=3*3^k := by rw [Nat.pow_succ]; omega
    have hq : t/3 < 3^k := by omega
    have h := ih _ hq
    have hr : t%3=0 ∨ t%3=1 ∨ t%3=2 := by omega
    rcases hr with hr|hr|hr <;> simp [ordinary,hr] <;> omega

/-- Balanced ternary digit parity. -/
theorem balanced_parity (k : Nat) : ∀ t, 2*t < 3^k →
    t%2 = ((balanced k t).1+(balanced k t).2)%2 := by
  induction k with
  | zero =>
    intro t ht
    have hz : t=0 := by simp at ht; omega
    subst t
    decide
  | succ k ih =>
    intro t ht
    have hp : 3^(k+1)=3*3^k := by rw [Nat.pow_succ]; omega
    have hodd := pow_three_odd k
    have hq : 2*((t+1)/3)<3^k := by omega
    have h := ih _ hq
    have hr : t%3=0 ∨ t%3=1 ∨ t%3=2 := by omega
    rcases hr with hr|hr|hr <;> simp [balanced,hr] <;> omega

#print axioms base_power
#print axioms odd_offset
#print axioms even_offset
#print axioms left_image_iff
#print axioms right_image_iff
#print axioms ordinary_parity
#print axioms balanced_parity
end BB6.Agent41FatalInverse
