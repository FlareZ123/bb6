/-!
# Exact next-tail coordinate extract

This standalone extract was compiled with Lean 4.36.0-rc2. It formalizes
only the left-ray coordinate transformation; it is not a full import-closure
compilation of the repository's machine-run theorem.

The definitions are normalized copies of the current source:
* sideBit and d1pow from Agent8S1Encoder/S1Encoder.lean;
* p2ResidualLeft and p2PostludeFrame's S0 left context from
  Agent44P2Postlude/S0DrainQ4Postlude.lean;
* s0Tape from Agent8S1Encoder's s0Config/s0Tape and s0LeftFacing, using
  binDec_zero = d1pow;
* s0LeftSweepShift is s0LeftSweep_shift specialized to H-K=3;
* q4FinalFrame is q4FrameAt with q4S0Final4Inside/End at origin 3;
* prefix22Frame is frameAt with firstCyclePrefix22Inside/End at origin 1.

The scan and two-zero setup are omitted from nextInputTape because they
leave all cells at and left of coordinate 4 unchanged. The theorem gives
the exact pointwise residual tail after the P2 postlude and prefix22 frame.
-/

import Lean.Elab.Tactic.Omega

namespace NextResidualBranch

def sideBit : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: xs, i+1 => sideBit xs i

def d1 : List Bool := [true,true,true]
def d1pow : Nat → List Bool
  | 0 => []
  | n+1 => d1 ++ d1pow n

def p2ResidualLeft (m : Nat) (tail : List Bool) : List Bool :=
  (List.replicate (m+2) true ++ [false,true,false,false]) ++ tail

def s0Tape (left right : List Bool) (H : Int) : Int → Bool := fun x =>
  if x ≤ H then sideBit left (Int.toNat (H-x))
  else sideBit right (Int.toNat (x-H-1))

def s0LeftSweepShift (T : Int → Bool) (H : Int) : Int → Bool := fun x =>
  if x = 4 then false else if 5 ≤ x ∧ x ≤ H+1 then true else T x

def q4FinalFrame (T : Int → Bool) : Int → Bool := fun x =>
  if 0 ≤ x ∧ x ≤ 3 then decide (x = 0) else T x

def prefix22Frame (T : Int → Bool) : Int → Bool := fun x =>
  if -3 ≤ x ∧ x ≤ 4 then
    decide (x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 2 ∨ x = 4)
  else T x

def nextInputTape (m n : Nat) (tail : List Bool) : Int → Bool :=
  let H : Nat := m+2+3*n
  let a : Nat := n-1
  let left := d1pow a ++ p2ResidualLeft m tail
  let S := s0Tape left [] (H:Int)
  let U := s0LeftSweepShift S (H:Int)
  let P := q4FinalFrame U
  prefix22Frame P

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

private theorem sideBit_p2_tail (m : Nat) (tail : List Bool) (j : Nat) :
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

/-- The next q4Tail adapter's left tail after the P2 S0 drain and
firstCyclePrefix22 has six ones followed by the old tail after six cells. -/
theorem next_tail_cells
    (m n : Nat) (tail : List Bool) (hn : 2≤n)
    (ht3 : sideBit tail 3 = true)
    (ht4 : sideBit tail 4 = true)
    (ht5 : sideBit tail 5 = true) :
    ∀ j : Nat, nextInputTape m n tail (-1-(j:Int)) =
      if j<6 then true else sideBit tail j := by
  let H : Nat := m+2+3*n
  let a : Nat := n-1
  let left : List Bool := d1pow a ++ p2ResidualLeft m tail
  let S : Int → Bool := s0Tape left [] (H:Int)
  let U : Int → Bool := s0LeftSweepShift S (H:Int)
  let P : Int → Bool := q4FinalFrame U
  let T : Int → Bool := prefix22Frame P
  have hTdef : T = nextInputTape m n tail := by rfl
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
      else false) = _
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
  have hTsmall (j : Nat) (hj : j<3) : T (-1-(j:Int)) = true := by
    have hjcases : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hjcases with h0|h1|h2 <;> subst j <;>
      simp [T,prefix22Frame]
  have hTlarge (j : Nat) (hj : 3≤j) :
      T (-1-(j:Int)) = sideBit tail j := by
    have hframe : T (-1-(j:Int)) = P (-1-(j:Int)) := by
      change (if -3 ≤ -1-(j:Int) ∧ -1-(j:Int) ≤ 4
        then decide (-1-(j:Int) = -3 ∨ -1-(j:Int) = -2 ∨
          -1-(j:Int) = -1 ∨ -1-(j:Int) = 2 ∨ -1-(j:Int) = 4)
        else P (-1-(j:Int))) = P (-1-(j:Int))
      have hx : ¬ (-3 ≤ -1-(j:Int) ∧ -1-(j:Int) ≤ 4) := by omega
      rw [if_neg hx]
    calc
      T (-1-(j:Int)) = P (-1-(j:Int)) := hframe
      _ = U (-1-(j:Int)) := hP j
      _ = S (-1-(j:Int)) := hU j
      _ = sideBit (p2ResidualLeft m tail) (m+6+j) := hS j
      _ = sideBit tail j := sideBit_p2_tail m tail j
  intro j
  rw [← hTdef]
  by_cases hj6 : j<6
  · by_cases hj3 : j<3
    · rw [hTsmall j hj3]
      simp [hj6]
    · have hj35 : j=3 ∨ j=4 ∨ j=5 := by omega
      rcases hj35 with h3|h4|h5 <;> subst j
      · rw [hTlarge 3 (by omega),ht3]
        simp
      · rw [hTlarge 4 (by omega),ht4]
        simp
      · rw [hTlarge 5 (by omega),ht5]
        simp
  · rw [hTlarge j (by omega)]
    simp [hj6]

#print axioms next_tail_cells

end NextResidualBranch
