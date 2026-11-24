import Q0DigitConvolution
import Q0SignedCarry

namespace BB429Q0Macro.DigitConvolution
set_option maxHeartbeats 8000000

def fromList (w : List Bool) : History := fun i => w[i]?.getD false

theorem fromList_cons (d : Bool) (w : List Bool) : fromList (d::w)=push d (fromList w) := by
  funext i
  cases i <;> simp [fromList,push]

theorem fromList_snoc (d : Bool) (w : List Bool) : fromList (w++[d]).reverse=push d (fromList w.reverse) := by
  simp [List.reverse_append,fromList_cons]

theorem value_reverse (w : List Bool) : (value (fromList w) w.length:Int)=HalfStep.digits w.reverse := by
  induction w with
  | nil => simp [value,HalfStep.digits]
  | cons d w ih =>
    rw [List.length_cons,fromList_cons,value_push,List.reverse_cons,HalfStep.digits_snoc,HalfStep.modulus]
    simp only [List.length_reverse,Int.natCast_add,Int.natCast_mul,Int.natCast_pow,ih]
    cases d <;> simp [bit,HalfStep.bit] <;> omega

theorem value_chronological (w : List Bool) : (value (fromList w.reverse) w.length:Int)=HalfStep.digits w := by
  simpa using value_reverse w.reverse

/-- Every strict history of k half-steps ending at rank <=4^k has a
    nonnegative convolution residual bounded by its rank digit sum. -/
theorem residual_of_history {s w p y P Y} (h : HalfStep.Trace s w p y P Y)
    (hy : 0<y) (hc : 3*y<p) (hP : P≤4^w.length)
    {ds : List Nat} (hd : rankValue ds=P) (hl : ds.length≤w.length+1) :
    0≤(Y:Int)-conv (fromList w.reverse) ds ∧
    3*((Y:Int)-conv (fromList w.reverse) ds)≤(digitSum ds:Int)+3 := by
  obtain ⟨hr,hf⟩ := HalfStep.trace_formula h
  have he := HalfStep.error_bounds s w
  have hm := HalfStep.modulus_pos w
  have lo : -HalfStep.modulus w < HalfStep.error s w := by split at he <;> omega
  have hi : 15*HalfStep.error s w < 13*HalfStep.modulus w := by split at he <;> omega
  rw [HalfStep.modulus] at lo hi hf
  rw [←value_chronological] at hf
  have hf' : (4:Int)^w.length*(Y:Int)=(y:Int)+(rankValue ds:Int)*(value (fromList w.reverse) w.length:Int)+HalfStep.error s w := by rw [hd]; grind
  exact residual_bound _ _ _ _ _ _ hl (by omega) hy (by omega) lo hi hf'

/-- Exact forward and backward translation of a half-step's height equation
    using only the radix-four rank addition and the history convolution. -/
theorem step_iff_residual (s d : Bool) (w : List Bool) {ds es cs : List Nat}
    (ha : Addition (HalfStep.len s d) ds es cs) (y Y : Nat) :
    (4*Y=HalfStep.numerator s d (rankValue ds) y) ↔
    4*((Y:Int)-conv (fromList (w++[d]).reverse) es)+4*(bitDot (fromList (w++[d]).reverse) cs:Int)=
      ((y:Int)-conv (fromList w.reverse) ds)+(HalfStep.off s d:Int)+bitDot (fromList (w++[d]).reverse) ds := by
  rw [fromList_snoc]
  have hb : bit d=HalfStep.bit d := by cases d <;> rfl
  constructor
  · intro ht
    apply residual_roll _ _ ha
    simpa [HalfStep.numerator,hb] using ht
  · intro ht
    have hh := residual_reconstruct _ _ ha y Y (HalfStep.off s d) ht
    simpa [HalfStep.numerator,hb] using hh

#print axioms residual_of_history
#print axioms step_iff_residual
end BB429Q0Macro.DigitConvolution
