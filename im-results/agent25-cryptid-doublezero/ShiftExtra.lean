import Lean.Elab.Tactic.Omega
import ShiftCylinders
import ABridgeTwo
import EDouble
import EZeroPair
import ASixBoundary

set_option maxHeartbeats 6000000

namespace BB6.Agent25Shift

open CryptidBoundary

def costEdouble (k q : Nat) : Nat := 12*k*k+49*k+64+4*q
def costEzero (k : Nat) : Nat := 12*k*k+49*k+96
def costAdouble (k : Nat) (ws : List Bool) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+16))
def costAsix (k : Nat) (ws : List Bool) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+24))

theorem costEdouble_succ (k q : Nat) :
    costEdouble (k+1) q = costEdouble k q + (24*k+61) := by
  unfold costEdouble
  simp only [Nat.mul_add, Nat.add_mul]
  omega

theorem costEzero_succ (k : Nat) :
    costEzero (k+1) = costEzero k + (24*k+61) := by
  unfold costEzero
  simp only [Nat.mul_add, Nat.add_mul]
  omega

theorem costAdouble_succ (k : Nat) (ws : List Bool) :
    costAdouble (k+1) ws =
      costAdouble k ws + (24*k+61+24*BB6.Parikh.triplesN ws) := by
  unfold costAdouble
  rw [show 4*(k+1)+3 = (4*k+3)+4 by omega, wordCost_shift4]
  simp only [Nat.mul_add, Nat.add_mul]
  omega

theorem costAsix_succ (k : Nat) (ws : List Bool) :
    costAsix (k+1) ws =
      costAsix k ws + (24*k+61+24*BB6.Parikh.triplesN ws) := by
  unfold costAsix
  rw [show 4*(k+1)+3 = (4*k+3)+4 by omega, wordCost_shift4]
  simp only [Nat.mul_add, Nat.add_mul]
  omega

/-- All source-certified E alternating-pair/double-zero returns share the
    same three-to-eight exact endpoint shift and 24k+61 time increment. -/
theorem EDouble_shift (k q : Nat) (ys : List Bool) :
    run (costEdouble k q + (24*k+61))
      (init (List.replicate (3*(k+1)+2) true ++
        false :: (pairs (q+1) ++ ([true,true,false,false] ++ ys)))) =
    prependEight (run (costEdouble k q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs (q+1) ++ ([true,true,false,false] ++ ys))))) := by
  rw [←costEdouble_succ]
  simp only [costEdouble]
  rw [BB6.Agent35.full_E_double (k+1) q ys,
      BB6.Agent35.full_E_double k q ys, prependEight_finish]
  have hr : 8*(k+1)+5 = (8*k+5)+8 := by omega
  rw [hr]

/-- The q=0 exceptional E double-zero branch has the same shift. -/
theorem EZero_shift (k : Nat) (ys : List Bool) :
    run (costEzero k + (24*k+61))
      (init (List.replicate (3*(k+1)+2) true ++
        false :: ([true,true,false,false] ++ ys))) =
    prependEight (run (costEzero k)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,true,false,false] ++ ys)))) := by
  rw [←costEzero_succ]
  simp only [costEzero]
  rw [BB6.Agent32EZero.full_E_zero_pairs (k+1) ys,
      BB6.Agent32EZero.full_E_zero_pairs k ys, prependEight_finish]
  have hr : 8*(k+1)+3 = (8*k+3)+8 := by omega
  rw [hr]

/-- Every A coded-word branch that ends in 1100 has exactly the same
    parameter-shift cocycle as the ordinary coded close branch. -/
theorem ADouble_shift (k : Nat) (ws ys : List Bool) :
    run (costAdouble k ws +
       (24*k+61+24*BB6.Parikh.triplesN ws))
      (init (List.replicate (3*(k+1)+1) true ++
        false :: (CryptidA.wordCode ws ++
          ([true,true,false,false] ++ ys)))) =
    prependEight (run (costAdouble k ws)
      (init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++
          ([true,true,false,false] ++ ys))))) := by
  rw [←costAdouble_succ]
  simp only [costAdouble]
  rw [BB6.Agent35.full_A_code_double (k+1) ws ys,
      BB6.Agent35.full_A_code_double k ws ys, prependEight_finish]
  have hr : 2*(4*(k+1)+3+CryptidA.wordInc ws)+1 =
      (2*(4*k+3+CryptidA.wordInc ws)+1)+8 := by omega
  rw [hr]

/-- The A-coded 1101^6 0 branch has the same 3-adic shift on all k and
    all finite token words and arbitrary right suffixes. -/
theorem ASix_shift (k : Nat) (ws ys : List Bool) :
    run (costAsix k ws +
       (24*k+61+24*BB6.Parikh.triplesN ws))
      (init (List.replicate (3*(k+1)+1) true ++
        false :: (CryptidA.wordCode ws ++
          ([true,true,false] ++ (List.replicate 6 true ++ (false :: ys)))))) =
    prependEight (run (costAsix k ws)
      (init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++
          ([true,true,false] ++ (List.replicate 6 true ++ (false :: ys)))))) := by
  rw [←costAsix_succ]
  simp only [costAsix]
  rw [BB6.Agent36.full_A_code_six (k+1) ws ys,
      BB6.Agent36.full_A_code_six k ws ys, prependEight_finish]
  have hr : 2*(4*(k+1)+3+CryptidA.wordInc ws)+5 =
      (2*(4*k+3+CryptidA.wordInc ws)+5)+8 := by omega
  rw [hr]

#print axioms EDouble_shift
#print axioms EZero_shift
#print axioms ADouble_shift
#print axioms ASix_shift

end BB6.Agent25Shift
