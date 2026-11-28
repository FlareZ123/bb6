import Lean
set_option maxHeartbeats 0
namespace BB6.Agent9AntiGeneral

/-- Chronological low-endian weighted sum of a finite binary window. -/
def wordSum (x : Nat → Int) (j : Nat) : Nat → Int
  | 0 => 0
  | k+1 => wordSum x j k+(2:Int)^k*x (j+k)

/-- Exact weighted unfolding of a general doubling carry. -/
theorem block_of_halves (y f : Nat→Int) (j K L : Nat)
    (hs : ∀ t<L, 2*y (t+1)=y t+f t)
    (hL : j+K≤L) :
    (2:Int)^K*y (j+K)=y j+wordSum f j K := by
  induction K with
  | zero => simp [wordSum]
  | succ K ih =>
    have hstep := hs (j+K) (by omega)
    have hprev := ih (by omega)
    rw [show j+(K+1)=j+K+1 by omega,Int.pow_succ,wordSum]
    calc
      (2:Int)^K*2*y (j+K+1) = (2:Int)^K*(2*y (j+K+1)) := by ac_rfl
      _ = (2:Int)^K*(y (j+K)+f (j+K)) := by rw [hstep]
      _ = (2:Int)^K*y (j+K)+(2:Int)^K*f (j+K) := by rw [Int.mul_add]
      _ = y j+(wordSum f j K+(2:Int)^K*f (j+K)) := by rw [hprev]; omega

/-- Word-sum respects scaling by a fixed integer. -/
theorem wordSum_scale (x : Nat→Int) (j K : Nat) (a : Int) :
    wordSum (fun t => a*x t) j K=a*wordSum x j K := by
  induction K with
  | zero => simp [wordSum]
  | succ K ih =>
    simp only [wordSum,ih,Int.mul_add]
    ac_rfl

/-- Complements sum to the all-ones word. -/
theorem wordSum_complement (x : Nat→Int) (j K : Nat) :
    wordSum (fun t => 1-x t) j K=(2:Int)^K-1-wordSum x j K := by
  induction K with
  | zero => simp [wordSum]
  | succ K ih =>
    rw [wordSum,ih,wordSum,Int.pow_succ]
    simp only [Int.mul_sub,Int.mul_one]
    omega

#print axioms block_of_halves
#print axioms wordSum_scale
#print axioms wordSum_complement
end BB6.Agent9AntiGeneral
