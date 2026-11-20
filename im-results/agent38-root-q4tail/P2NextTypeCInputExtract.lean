import NextResidualBranchExtract
import Lean.Elab.Tactic.Omega

open NextResidualBranch

namespace P2NextTypeCInputExtract

/-- The P2 q4/S0 postlude frame, in the head-one coordinate convention.
    This is the exact source shape: the S0 left word is d1pow(n-1) ++
    p2ResidualLeft m tail, the left sweep is centered at cell 3, and the
    q4S0Final4 frame overwrites cells 0 through 3 with 1000. -/
def s0RightFacing (b : Nat) : List Bool :=
  [false,true,true,true,false,false] ++ d1pow (b+1)

def p2PostludeTape (m n : Nat) (tail : List Bool) : Int → Bool :=
  let H : Nat := m+2+3*n
  let a : Nat := n-1
  let left := d1pow a ++ p2ResidualLeft m tail
  let right := s0RightFacing (2^a-1)
  let S := s0Tape left right (H:Int)
  let U := s0LeftSweepShift S (H:Int)
  q4FinalFrame U

/-- Exact local input predicate used by PositiveZTypeCBridge.typeC_at. -/
def typeCInput (T : Int → Bool) (h : Int) : Prop :=
  T (h-10) = false ∧
  T (h-9) = false ∧
  T (h-8) = true ∧
  T (h-7) = true ∧
  T (h-6) = true ∧
  T (h-5) = true ∧
  T (h-4) = true ∧
  T (h-3) = true ∧
  T (h-2) = true ∧
  T (h-1) = true ∧
  T h = false ∧
  T (h+1) = false ∧
  T (h+2) = false

private theorem sideBit_append_right (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  induction xs generalizing i with
  | nil => simp
  | cons b xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by simp at hi; omega
          have hidx : i-xs.length = (i+1)-(xs.length+1) := by omega
          calc
            sideBit ((b::xs) ++ ys) (i+1)
                = sideBit (xs ++ ys) i := rfl
            _ = sideBit ys (i-xs.length) := ih i hi'
            _ = sideBit ys ((i+1)-(xs.length+1)) := by rw [hidx]

private theorem d1pow_length (n : Nat) : (d1pow n).length = 3*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [d1pow,d1,ih]; omega

private theorem p2Residual_tail_local (m : Nat) (tail : List Bool) (j : Nat) :
    sideBit (p2ResidualLeft m tail) (m+6+j) = sideBit tail j := by
  unfold p2ResidualLeft
  have hlen :
      (List.replicate (m+2) true ++ [false,true,false,false]).length = m+6 := by
    simp
  have h := sideBit_append_right
    (List.replicate (m+2) true ++ [false,true,false,false]) tail
    (m+6+j) (by rw [hlen]; omega)
  rw [hlen] at h
  have hidx : m+6+j-(m+6)=j := by omega
  rw [hidx] at h
  exact h

/-- On the whole left ray, the P2 postlude preserves the S0 residual tail. -/
theorem p2Postlude_left_tail (m n : Nat) (tail : List Bool) (hn : 2≤n) :
    ∀ j : Nat, p2PostludeTape m n tail (-1-(j:Int)) = sideBit tail j := by
  let H : Nat := m+2+3*n
  let a : Nat := n-1
  let left : List Bool := d1pow a ++ p2ResidualLeft m tail
  let right : List Bool := s0RightFacing (2^a-1)
  let S : Int → Bool := s0Tape left right (H:Int)
  let U : Int → Bool := s0LeftSweepShift S (H:Int)
  let P : Int → Bool := q4FinalFrame U
  have hlen : (d1pow a).length = 3*a := d1pow_length a
  have hindex (j : Nat) : H+1+j-3*a = m+6+j := by
    dsimp [H,a]
    omega
  have hS (j : Nat) :
      S (-1-(j:Int)) = sideBit (p2ResidualLeft m tail) (m+6+j) := by
    have hle : (-1-(j:Int)) ≤ (H:Int) := by dsimp [H]; omega
    have hcoord : (H:Int)-(-1-(j:Int)) = (H+1+j:Int) := by omega
    have hidx : Int.toNat ((H:Int)-(-1-(j:Int))) = H+1+j := by
      rw [hcoord]
      omega
    have hbound : (d1pow a).length ≤ H+1+j := by
      rw [hlen]
      dsimp [H,a]
      omega
    have hleft := sideBit_append_right (d1pow a)
      (p2ResidualLeft m tail) (H+1+j) hbound
    have hindex' : H+1+j-3*a = m+6+j := hindex j
    change (if -1-(j:Int) ≤ (H:Int)
      then sideBit left (Int.toNat ((H:Int)-(-1-(j:Int))))
      else sideBit right (Int.toNat (-1-(j:Int)-(H:Int)-1))) = _
    rw [if_pos hle, hidx]
    rw [hlen] at hleft
    rw [hindex'] at hleft
    exact hleft
  have hU (j : Nat) : U (-1-(j:Int)) = S (-1-(j:Int)) := by
    change (if -1-(j:Int) = 4 then false
      else if 5 ≤ -1-(j:Int) ∧ -1-(j:Int) ≤ (H:Int)+1
        then true else S (-1-(j:Int))) = S (-1-(j:Int))
    have hneq : (-1-(j:Int)) ≠ 4 := by omega
    have hnot : ¬ (5 ≤ -1-(j:Int) ∧ -1-(j:Int) ≤ (H:Int)+1) := by omega
    simp [hneq,hnot]
  have hP (j : Nat) : P (-1-(j:Int)) = U (-1-(j:Int)) := by
    change (if 0 ≤ -1-(j:Int) ∧ -1-(j:Int) ≤ 3
      then decide (-1-(j:Int) = 0) else U (-1-(j:Int))) = U (-1-(j:Int))
    have hx : ¬ (0 ≤ -1-(j:Int) ∧ -1-(j:Int) ≤ 3) := by omega
    rw [if_neg hx]
  have hT (j : Nat) : P (-1-(j:Int)) = sideBit tail j := by
    calc
      P (-1-(j:Int)) = U (-1-(j:Int)) := hP j
      _ = S (-1-(j:Int)) := hU j
      _ = sideBit (p2ResidualLeft m tail) (m+6+j) := hS j
      _ = sideBit tail j := p2Residual_tail_local m tail j
  intro j
  change P (-1-(j:Int)) = sideBit tail j
  exact hT j

/-- A residual with seven leading ones and two following zeroes makes the
P2 postlude exactly the 13-cell 00 11111111 000 Type-C input. -/
theorem p2Postlude_typeCInput
    (m n : Nat) (tail : List Bool) (hn : 2≤n)
    (ht0 : sideBit tail 0 = true)
    (ht1 : sideBit tail 1 = true)
    (ht2 : sideBit tail 2 = true)
    (ht3 : sideBit tail 3 = true)
    (ht4 : sideBit tail 4 = true)
    (ht5 : sideBit tail 5 = true)
    (ht6 : sideBit tail 6 = true)
    (ht7 : sideBit tail 7 = false)
    (ht8 : sideBit tail 8 = false) :
    typeCInput (p2PostludeTape m n tail) 1 := by
  have hleft := p2Postlude_left_tail m n tail hn
  unfold typeCInput
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · calc
      p2PostludeTape m n tail (-1-(8:Int)) = sideBit tail 8 := hleft 8
      _ = false := ht8
  · calc
      p2PostludeTape m n tail (-1-(7:Int)) = sideBit tail 7 := hleft 7
      _ = false := ht7
  · calc
      p2PostludeTape m n tail (-1-(6:Int)) = sideBit tail 6 := hleft 6
      _ = true := ht6
  · calc
      p2PostludeTape m n tail (-1-(5:Int)) = sideBit tail 5 := hleft 5
      _ = true := ht5
  · calc
      p2PostludeTape m n tail (-1-(4:Int)) = sideBit tail 4 := hleft 4
      _ = true := ht4
  · calc
      p2PostludeTape m n tail (-1-(3:Int)) = sideBit tail 3 := hleft 3
      _ = true := ht3
  · calc
      p2PostludeTape m n tail (-1-(2:Int)) = sideBit tail 2 := hleft 2
      _ = true := ht2
  · calc
      p2PostludeTape m n tail (-1-(1:Int)) = sideBit tail 1 := hleft 1
      _ = true := ht1
  · calc
      p2PostludeTape m n tail (-1-(0:Int)) = sideBit tail 0 := hleft 0
      _ = true := ht0
  · change q4FinalFrame
      (s0LeftSweepShift
        (s0Tape (d1pow (n-1) ++ p2ResidualLeft m tail)
          (s0RightFacing (2^(n-1)-1)) ((m+2+3*n):Int))
        ((m+2+3*n):Int)) 0 = true
    simp [q4FinalFrame]
  · change q4FinalFrame
      (s0LeftSweepShift
        (s0Tape (d1pow (n-1) ++ p2ResidualLeft m tail)
          (s0RightFacing (2^(n-1)-1)) ((m+2+3*n):Int))
        ((m+2+3*n):Int)) 1 = false
    simp [q4FinalFrame]
  · change q4FinalFrame
      (s0LeftSweepShift
        (s0Tape (d1pow (n-1) ++ p2ResidualLeft m tail)
          (s0RightFacing (2^(n-1)-1)) ((m+2+3*n):Int))
        ((m+2+3*n):Int)) 2 = false
    simp [q4FinalFrame]
  · change q4FinalFrame
      (s0LeftSweepShift
        (s0Tape (d1pow (n-1) ++ p2ResidualLeft m tail)
          (s0RightFacing (2^(n-1)-1)) ((m+2+3*n):Int))
        ((m+2+3*n):Int)) 3 = false
    simp [q4FinalFrame]

/-- The common authentic case: the old suffix after six cells begins 100. -/
theorem p2Postlude_typeCInput_of_sixOnes_then100
    (m n : Nat) (suffix : List Bool) (hn : 2≤n)
    (hs0 : sideBit suffix 0 = true)
    (hs1 : sideBit suffix 1 = false)
    (hs2 : sideBit suffix 2 = false) :
    typeCInput
      (p2PostludeTape m n (List.replicate 6 true ++ suffix)) 1 := by
  apply p2Postlude_typeCInput m n (List.replicate 6 true ++ suffix) hn
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simpa using hs0
  · simpa using hs1
  · simpa using hs2

#print axioms p2Postlude_typeCInput
#print axioms p2Postlude_typeCInput_of_sixOnes_then100

end P2NextTypeCInputExtract
