import P2NextTypeCInputExtract
import Lean.Elab.Tactic.Omega

open NextResidualBranch P2NextTypeCInputExtract

namespace P2NextTypeCCheckpointExtract

def linearRightOnes (T : Int → Bool) (h : Int) (m : Nat) : Prop :=
  ∀ i : Nat, i<m → T (h+(i:Int)) = true

def d1BlocksOn (T : Int → Bool) (h : Int) (n : Nat) : Prop :=
  ∀ i : Nat, i<n →
    T (h+3*(i:Int)) = true ∧
    T (h+3*(i:Int)+1) = true ∧
    T (h+3*(i:Int)+2) = true

theorem p2Postlude_right_cell
    (m n : Nat) (tail : List Bool) (hn : 2≤n)
    (x : Int) (hx : 5≤x) :
    p2PostludeTape m n tail x =
      if x≤(m+2+3*n:Int)+1 then true else
        sideBit (s0RightFacing (2^(n-1)-1)) (Int.toNat (x-(m+2+3*n:Int)-1)) := by
  let H : Nat := m+2+3*n
  let a : Nat := n-1
  change q4FinalFrame
    (s0LeftSweepShift
      (s0Tape (d1pow a ++ p2ResidualLeft m tail)
        (s0RightFacing (2^a-1)) (H:Int)) (H:Int)) x =
    (if x≤(H:Int)+1 then true else
      sideBit (s0RightFacing (2^(n-1)-1)) (Int.toNat (x-(H:Int)-1)))
  have hq4 : ¬ (0≤x ∧ x≤3) := by omega
  have h4 : x≠4 := by omega
  by_cases hle : x≤(H:Int)+1
  · have hs : 5≤x ∧ x≤(H:Int)+1 := ⟨hx,hle⟩
    rw [if_pos hle]
    simp [q4FinalFrame,hq4,s0LeftSweepShift,h4,hs]
  · have hs : ¬ (5≤x ∧ x≤(H:Int)+1) := by omega
    have hgt : ¬ x≤(H:Int) := by omega
    rw [if_neg hle]
    simp [q4FinalFrame,hq4,s0LeftSweepShift,h4,hs,s0Tape,hgt,a]

private theorem sideBit_append_right_local (xs ys : List Bool) (i : Nat)
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
            sideBit ((b::xs) ++ ys) (i+1) = sideBit (xs ++ ys) i := rfl
            _ = sideBit ys (i-xs.length) := ih i hi'
            _ = sideBit ys ((i+1)-(xs.length+1)) := by rw [hidx]

private theorem s0RightFacing_tail (b k : Nat) (hk : 6≤k) :
    sideBit (s0RightFacing b) k = sideBit (d1pow (b+1)) (k-6) := by
  change sideBit ([false,true,true,true,false,false] ++ d1pow (b+1)) k = _
  have h := sideBit_append_right_local
    ([false,true,true,true,false,false] : List Bool) (d1pow (b+1)) k
    (by simpa using hk)
  simpa using h

private theorem d1pow_length (n : Nat) : (d1pow n).length=3*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [d1pow,d1,ih]; omega

private theorem sideBit_d1pow_true (n i : Nat) (hi : i<3*n) :
    sideBit (d1pow n) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [d1pow,d1,sideBit]
      | succ i =>
          cases i with
          | zero => simp [d1pow,d1,sideBit]
          | succ i =>
              cases i with
              | zero => simp [d1pow,d1,sideBit]
              | succ i =>
                  have hi' : i<3*n := by omega
                  simpa [d1pow,d1,sideBit] using ih i hi'

private theorem sideBit_d1pow_false (n i : Nat) (hi : 3*n≤i) :
    sideBit (d1pow n) i = false := by
  have h := sideBit_append_right_local (d1pow n) [] i (by rw [d1pow_length]; exact hi)
  simpa [sideBit] using h

private theorem s0RightFacing_bit123 (b : Nat) :
    sideBit (s0RightFacing b) 1 = true ∧
    sideBit (s0RightFacing b) 2 = true ∧
    sideBit (s0RightFacing b) 3 = true := by
  simp [s0RightFacing,sideBit]

private theorem s0RightFacing_bit45 (b : Nat) :
    sideBit (s0RightFacing b) 4 = false ∧
    sideBit (s0RightFacing b) 5 = false := by
  simp [s0RightFacing,sideBit]

theorem p2Postlude_typeC_rightGuards
    (m n : Nat) (tail : List Bool) (hn : 2≤n)
    (hr : 2≤2^(n-1)) :
    let H : Nat := m+2+3*n
    let r : Nat := 2^(n-1)
    let P := p2PostludeTape m n tail
    P 4 = false ∧
    linearRightOnes P 5 H ∧
    P ((H:Int)+5) = false ∧
    P ((H:Int)+6) = false ∧
    d1BlocksOn P ((H:Int)+7) r ∧
    (∀ i : Nat, i≤4 → P ((H:Int)+7+3*(r:Int)+(i:Int)) = false) := by
  let H : Nat := m+2+3*n
  let r : Nat := 2^(n-1)
  let P := p2PostludeTape m n tail
  have h3 : P 4 = false := by
    change q4FinalFrame
      (s0LeftSweepShift
        (s0Tape (d1pow (n-1) ++ p2ResidualLeft m tail)
          (s0RightFacing (2^(n-1)-1)) ((m+2+3*n):Int))
        ((m+2+3*n):Int)) 4 = false
    simp [q4FinalFrame,s0LeftSweepShift]
  have hfirst : linearRightOnes P 5 H := by
    intro i hi
    have hcell := p2Postlude_right_cell m n tail hn (5+(i:Int)) (by omega)
    have hcell' : P (5+(i:Int)) =
        (if 5+(i:Int)≤(H:Int)+1 then true else
          sideBit (s0RightFacing (2^(n-1)-1))
            (Int.toNat (5+(i:Int)-(H:Int)-1))) := by
      simpa [P,H] using hcell
    by_cases hle : 5+(i:Int)≤(H:Int)+1
    · rw [hcell', if_pos hle]
    · have hcases : 5+(i:Int)=(H:Int)+2 ∨
          5+(i:Int)=(H:Int)+3 ∨ 5+(i:Int)=(H:Int)+4 := by
        have hupper : 5+(i:Int)≤(H:Int)+4 := by omega
        omega
      rcases hcases with h2|h3|h4
      · rw [hcell', if_neg hle]
        have hidx : Int.toNat (5+(i:Int)-(H:Int)-1)=1 := by omega
        rw [hidx]
        exact (s0RightFacing_bit123 (2^(n-1)-1)).1
      · rw [hcell', if_neg hle]
        have hidx : Int.toNat (5+(i:Int)-(H:Int)-1)=2 := by omega
        rw [hidx]
        exact (s0RightFacing_bit123 (2^(n-1)-1)).2.1
      · rw [hcell', if_neg hle]
        have hidx : Int.toNat (5+(i:Int)-(H:Int)-1)=3 := by omega
        rw [hidx]
        exact (s0RightFacing_bit123 (2^(n-1)-1)).2.2
  have hsep0 : P ((H:Int)+5) = false := by
    have hcell := p2Postlude_right_cell m n tail hn ((H:Int)+5) (by omega)
    have hcell' : P ((H:Int)+5) =
        (if (H:Int)+5≤(H:Int)+1 then true else
          sideBit (s0RightFacing (2^(n-1)-1))
            (Int.toNat ((H:Int)+5-(H:Int)-1))) := by
      simpa [P,H] using hcell
    rw [hcell', if_neg (by omega)]
    have hidx : Int.toNat ((H:Int)+5-(H:Int)-1)=4 := by omega
    rw [hidx]
    exact (s0RightFacing_bit45 (2^(n-1)-1)).1
  have hsep1 : P ((H:Int)+6) = false := by
    have hcell := p2Postlude_right_cell m n tail hn ((H:Int)+6) (by omega)
    have hcell' : P ((H:Int)+6) =
        (if (H:Int)+6≤(H:Int)+1 then true else
          sideBit (s0RightFacing (2^(n-1)-1))
            (Int.toNat ((H:Int)+6-(H:Int)-1))) := by
      simpa [P,H] using hcell
    rw [hcell', if_neg (by omega)]
    have hidx : Int.toNat ((H:Int)+6-(H:Int)-1)=5 := by omega
    rw [hidx]
    exact (s0RightFacing_bit45 (2^(n-1)-1)).2
  have hbn : (2^(n-1)-1)+1 = r := by dsimp [r]; omega
  have hblocks : d1BlocksOn P ((H:Int)+7) r := by
    intro i hi
    have h0 := p2Postlude_right_cell m n tail hn ((H:Int)+7+3*(i:Int)) (by omega)
    have h1 := p2Postlude_right_cell m n tail hn ((H:Int)+7+3*(i:Int)+1) (by omega)
    have h2 := p2Postlude_right_cell m n tail hn ((H:Int)+7+3*(i:Int)+2) (by omega)
    have hc0 : P ((H:Int)+7+3*(i:Int)) =
        sideBit (s0RightFacing (2^(n-1)-1)) (6+3*i) := by
      have hc : P ((H:Int)+7+3*(i:Int)) =
          (if (H:Int)+7+3*(i:Int)≤(H:Int)+1 then true else
            sideBit (s0RightFacing (2^(n-1)-1))
              (Int.toNat ((H:Int)+7+3*(i:Int)-(H:Int)-1))) := by
        simpa [P,H] using h0
      rw [hc, if_neg (by omega)]
      have hidx : Int.toNat ((H:Int)+7+3*(i:Int)-(H:Int)-1)=6+3*i := by omega
      rw [hidx]
    have hc1 : P ((H:Int)+7+3*(i:Int)+1) =
        sideBit (s0RightFacing (2^(n-1)-1)) (6+3*i+1) := by
      have hc : P ((H:Int)+7+3*(i:Int)+1) =
          (if (H:Int)+7+3*(i:Int)+1≤(H:Int)+1 then true else
            sideBit (s0RightFacing (2^(n-1)-1))
              (Int.toNat ((H:Int)+7+3*(i:Int)+1-(H:Int)-1))) := by
        simpa [P,H] using h1
      rw [hc, if_neg (by omega)]
      have hidx : Int.toNat ((H:Int)+7+3*(i:Int)+1-(H:Int)-1)=6+3*i+1 := by omega
      rw [hidx]
    have hc2 : P ((H:Int)+7+3*(i:Int)+2) =
        sideBit (s0RightFacing (2^(n-1)-1)) (6+3*i+2) := by
      have hc : P ((H:Int)+7+3*(i:Int)+2) =
          (if (H:Int)+7+3*(i:Int)+2≤(H:Int)+1 then true else
            sideBit (s0RightFacing (2^(n-1)-1))
              (Int.toNat ((H:Int)+7+3*(i:Int)+2-(H:Int)-1))) := by
        simpa [P,H] using h2
      rw [hc, if_neg (by omega)]
      have hidx : Int.toNat ((H:Int)+7+3*(i:Int)+2-(H:Int)-1)=6+3*i+2 := by omega
      rw [hidx]
    have hb0 := s0RightFacing_tail (2^(n-1)-1) (6+3*i) (by omega)
    have hb1 := s0RightFacing_tail (2^(n-1)-1) (6+3*i+1) (by omega)
    have hb2 := s0RightFacing_tail (2^(n-1)-1) (6+3*i+2) (by omega)
    rw [show 6+3*i-6=3*i by omega, hbn] at hb0
    rw [show 6+3*i+1-6=3*i+1 by omega, hbn] at hb1
    rw [show 6+3*i+2-6=3*i+2 by omega, hbn] at hb2
    exact ⟨hc0.trans (hb0.trans (sideBit_d1pow_true r (3*i) (by omega))),
      hc1.trans (hb1.trans (sideBit_d1pow_true r (3*i+1) (by omega))),
      hc2.trans (hb2.trans (sideBit_d1pow_true r (3*i+2) (by omega)))⟩
  have hzeros : ∀ i : Nat, i≤4 → P ((H:Int)+7+3*(r:Int)+(i:Int)) = false := by
    intro i hi
    have hcell := p2Postlude_right_cell m n tail hn
      ((H:Int)+7+3*(r:Int)+(i:Int)) (by omega)
    have hc : P ((H:Int)+7+3*(r:Int)+(i:Int)) =
        sideBit (s0RightFacing (2^(n-1)-1)) (6+3*r+i) := by
      have hc' : P ((H:Int)+7+3*(r:Int)+(i:Int)) =
          (if (H:Int)+7+3*(r:Int)+(i:Int)≤(H:Int)+1 then true else
            sideBit (s0RightFacing (2^(n-1)-1))
              (Int.toNat ((H:Int)+7+3*(r:Int)+(i:Int)-(H:Int)-1))) := by
        simpa [P,H] using hcell
      rw [hc', if_neg (by omega)]
      have hidx : Int.toNat ((H:Int)+7+3*(r:Int)+(i:Int)-(H:Int)-1)=6+3*r+i := by omega
      rw [hidx]
    have hb := s0RightFacing_tail (2^(n-1)-1) (6+3*r+i) (by omega)
    rw [show 6+3*r+i-6=3*r+i by omega, hbn] at hb
    exact hc.trans (hb.trans (sideBit_d1pow_false r (3*r+i) (by omega)))

  exact ⟨h3,hfirst,hsep0,hsep1,hblocks,hzeros⟩

/-- This package is exactly the input contract of Agent24TypeCPrefix:
Type-C's 13-cell window, the following E-run, two separators, the counted
D1 blocks, and the four-zero right terminator. -/
theorem p2Postlude_typeCCheckpoint_of_sixOnes_then100
    (m n : Nat) (suffix : List Bool) (hn : 2≤n)
    (hr : 2≤2^(n-1))
    (hs0 : sideBit suffix 0 = true)
    (hs1 : sideBit suffix 1 = false)
    (hs2 : sideBit suffix 2 = false) :
    let tail := List.replicate 6 true ++ suffix
    let H : Nat := m+2+3*n
    let r : Nat := 2^(n-1)
    let P := p2PostludeTape m n tail
    typeCInput P 1 ∧
    P 4 = false ∧
    linearRightOnes P 5 H ∧
    P ((H:Int)+5) = false ∧
    P ((H:Int)+6) = false ∧
    d1BlocksOn P ((H:Int)+7) r ∧
    (∀ i : Nat, i≤4 → P ((H:Int)+7+3*(r:Int)+(i:Int)) = false) ∧
    2≤r := by
  let tail : List Bool := List.replicate 6 true ++ suffix
  let H : Nat := m+2+3*n
  let r : Nat := 2^(n-1)
  let P : Int → Bool := p2PostludeTape m n tail
  have hin : typeCInput P 1 := by
    exact p2Postlude_typeCInput_of_sixOnes_then100 m n suffix hn hs0 hs1 hs2
  have hright := p2Postlude_typeC_rightGuards m n tail hn hr
  have hr' : 2≤r := by exact hr
  exact ⟨hin, hright.1, hright.2.1, hright.2.2.1,
    hright.2.2.2.1, hright.2.2.2.2.1, hright.2.2.2.2.2, hr'⟩

/-- Agent42's P2-to-next-q4Tail residual map, normalized locally. -/
def p2NextQ4TailResidualTail (tail : List Bool) : List Bool :=
  [true,true,true] ++ tail.drop 3

theorem p2NextQ4Tail_authenticResidualTail (suffix : List Bool) :
    p2NextQ4TailResidualTail ([true,false,false,true,true,true] ++ suffix) =
      List.replicate 6 true ++ suffix := by
  simp [p2NextQ4TailResidualTail]

/-- The authentic 100111-to-111111 residual is a Type-C checkpoint whenever
its untouched suffix begins 100. The 100 prefix is supplied by the outer
width recurrence for A≥3. -/
theorem p2NextQ4Tail_to_typeCCheckpoint
    (m n : Nat) (suffix : List Bool) (hn : 2≤n)
    (hr : 2≤2^(n-1))
    (hs0 : sideBit suffix 0 = true)
    (hs1 : sideBit suffix 1 = false)
    (hs2 : sideBit suffix 2 = false) :
    let tail := p2NextQ4TailResidualTail
      ([true,false,false,true,true,true] ++ suffix)
    let H : Nat := m+2+3*n
    let r : Nat := 2^(n-1)
    let P := p2PostludeTape m n tail
    typeCInput P 1 ∧
    P 4 = false ∧
    linearRightOnes P 5 H ∧
    P ((H:Int)+5) = false ∧
    P ((H:Int)+6) = false ∧
    d1BlocksOn P ((H:Int)+7) r ∧
    (∀ i : Nat, i≤4 → P ((H:Int)+7+3*(r:Int)+(i:Int)) = false) ∧
    2≤r := by
  rw [p2NextQ4Tail_authenticResidualTail]
  exact p2Postlude_typeCCheckpoint_of_sixOnes_then100
    m n suffix hn hr hs0 hs1 hs2

#print axioms p2NextQ4Tail_to_typeCCheckpoint

end P2NextTypeCCheckpointExtract
