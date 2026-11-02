import Lean.Elab.Tactic.Omega
import ABridgeCode
import TokenCostNormal
import CryptidPairs
import CryptidTriplePairs

set_option maxHeartbeats 5000000

namespace BB6.Agent25Shift

open CryptidBoundary

/-- Add exactly eight unary ones to the right tape of a raw configuration. -/
def prependEight (c : Cfg) : Cfg :=
  ⟨c.l,c.h,List.replicate 8 true ++ c.r,c.st⟩

private theorem prependEight_finish (n : Nat) (ys : List Bool) :
    prependEight (⟨[],false,List.replicate n true ++ ys,5⟩ : Cfg) =
      (⟨[],false,List.replicate (n+8) true ++ ys,5⟩ : Cfg) := by
  unfold prependEight
  congr 1
  rw [List.append_assoc, List.replicate_append_replicate]
  congr 1
  omega

def costB (k : Nat) : Nat := 12*k*k+49*k+40
def costEpair (k q : Nat) : Nat := 12*k*k+49*k+50+4*q
def costEtriple (k q : Nat) : Nat := 12*k*k+49*k+58+6*q
def costA (k : Nat) (ws : List Bool) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) ws +
     (2*((4*k+3)+CryptidA.wordInc ws)+6))

/-- Exact quadratic base-cost increment under a three-unary shift. -/
theorem costB_succ (k : Nat) :
    costB (k+1) = costB k + (24*k+61) := by
  unfold costB
  simp only [Nat.mul_add, Nat.add_mul]
  omega

theorem costEpair_succ (k q : Nat) :
    costEpair (k+1) q = costEpair k q + (24*k+61) := by
  unfold costEpair
  simp only [Nat.mul_add, Nat.add_mul]
  omega

theorem costEtriple_succ (k q : Nat) :
    costEtriple (k+1) q = costEtriple k q + (24*k+61) := by
  unfold costEtriple
  simp only [Nat.mul_add, Nat.add_mul]
  omega

/-- A-coded words are insensitive to +4 in the alternating-stack exponent
    except for exactly 24 extra raw steps per triple-ones packet. -/
theorem wordCost_shift4 (m : Nat) (ws : List Bool) :
    CryptidA.wordCost (m+4) ws =
      CryptidA.wordCost m ws + 24*BB6.Parikh.triplesN ws := by
  induction ws generalizing m with
  | nil => simp [CryptidA.wordCost, BB6.Parikh.triplesN]
  | cons b ws ih =>
    cases b with
    | false =>
      simp only [CryptidA.wordCost, BB6.Parikh.triplesN]
      rw [show m+4+1 = (m+1)+4 by omega, ih (m+1)]
      omega
    | true =>
      simp only [CryptidA.wordCost, BB6.Parikh.triplesN]
      rw [show m+4+4 = (m+4)+4 by omega, ih (m+4)]
      omega

/-- The cost shift on every finite 10/111 codeword is determined solely
    by the number of triple packets, regardless of packet ordering. -/
theorem costA_succ (k : Nat) (ws : List Bool) :
    costA (k+1) ws =
      costA k ws + (24*k+61+24*BB6.Parikh.triplesN ws) := by
  unfold costA
  rw [show 4*(k+1)+3 = (4*k+3)+4 by omega, wordCost_shift4]
  simp only [Nat.mul_add, Nat.add_mul]
  omega

/-- Genuine original-machine B-cylinder returns from n and n+3 inputs
    are separated by eight unary cells and exactly 24k+61 primitive steps. -/
theorem B_shift (k : Nat) (ys : List Bool) :
    run (costB k + (24*k+61))
      (init (List.replicate (3*(k+1)) true ++ false::ys)) =
    prependEight (run (costB k)
      (init (List.replicate (3*k) true ++ false::ys))) := by
  rw [←costB_succ, costB]
  rw [full_B (k+1) ys, full_B k ys, prependEight_finish]
  congr 1
  omega

theorem Epair_shift (k q : Nat) (ys : List Bool) :
    run (costEpair k q + (24*k+61))
      (init (List.replicate (3*(k+1)+2) true ++
        false :: (pairs q ++ (false::ys)))) =
    prependEight (run (costEpair k q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (false::ys))))) := by
  rw [←costEpair_succ, costEpair]
  rw [full_E_pairs (k+1) q ys, full_E_pairs k q ys, prependEight_finish]
  congr 1
  omega

theorem Etriple_shift (k q : Nat) (ys : List Bool) :
    run (costEtriple k q + (24*k+61))
      (init (List.replicate (3*(k+1)+2) true ++
        false :: (pairs q ++ ([true,true,true] ++ ys)))) =
    prependEight (run (costEtriple k q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ ([true,true,true] ++ ys))))) := by
  rw [←costEtriple_succ, costEtriple]
  rw [full_E_triple_pairs (k+1) q ys, full_E_triple_pairs k q ys,
    prependEight_finish]
  congr 1
  omega

theorem Acode_shift (k : Nat) (ws ys : List Bool) :
    run (costA k ws + (24*k+61+24*BB6.Parikh.triplesN ws))
      (init (List.replicate (3*(k+1)+1) true ++
        false :: (CryptidA.wordCode ws ++ (false::ys)))) =
    prependEight (run (costA k ws)
      (init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++ (false::ys))))) := by
  rw [←costA_succ, costA]
  rw [BB6.Agent35.full_A_code (k+1) ws ys,
      BB6.Agent35.full_A_code k ws ys, prependEight_finish]
  congr 1
  omega

#print axioms wordCost_shift4
#print axioms costA_succ
#print axioms B_shift
#print axioms Epair_shift
#print axioms Etriple_shift
#print axioms Acode_shift
end BB6.Agent25Shift
