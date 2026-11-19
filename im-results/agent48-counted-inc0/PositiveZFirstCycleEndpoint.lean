import PositiveZFirstCyclePrefix
import PositiveZSecondCycleBridge
import D0SweepLeftFacing
import S0CountedDrain
import PositiveZFirstCycleS0Input
import Agent6Q4Prefix
import Lean.Elab.Tactic.Omega

/-!
# Exact S0 endpoint of the positive-z first q4 cycle prefix

This module identifies the 22-step / E-scan / two-zero / state-1 block
scan / q4-tail composition with an arbitrary-left-context S0 source
configuration.  It is the missing pointwise endpoint between the P(z)
prefix and the already isolated all-ones S0 drain plus Q(z) postlude.

The result is source-only until the complete Lean 4.36.0-rc2 import
closure is compiled and its transitive axiom profile is audited.
-/

namespace BB6Coverage.Agent48PositiveZFirstCycleEndpoint

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent48PositiveZFirstCycle
open BB6Coverage.Agent48PositiveZFirstCyclePrefix
open BB6Coverage.Agent48PositiveZSecondCycle
open BB6Coverage.Agent48D0SweepLeftFacing
open BB6Coverage.Agent42PositiveZFirstCycleS0Input
open BB6Coverage.Agent42Q4S0Drain

set_option maxHeartbeats 4000000

/-- The head-facing left side at q4 checkpoint 1.  The first six cells
are 011001; the remainder is an arbitrary encoded counter and history. -/
def firstCycleCheckpointLeft (w q : Nat) : List Bool :=
  [false,true,true] ++ d0 ++ binDec w q ++ lh

/-- The right side at q4 checkpoint 1: three zeroes, the E-scan run,
two separators, n three-one blocks, and four explicit trailing zeroes. -/
def firstCycleCheckpointRight (z : Nat) : List Bool :=
  [false,false,false] ++ List.replicate (3*z+5) true ++
    [false,false] ++ d1pow (2^z) ++ [false,false,false,false]

/-- The exact infinite tape represented by the two checkpoint sides. -/
def firstCycleCheckpointTape (z w q : Nat) : Int → Bool :=
  q4TapeFromSides (firstCycleCheckpointLeft w q)
    (firstCycleCheckpointRight z) 1

/-- The arbitrary residual left context after the P(z) prefix. -/
def firstCycleEndpointLeft (z w q : Nat) : List Bool :=
  List.replicate (3*z+7) true ++ [false,true,false,false] ++
    List.replicate 4 true ++ binDec w q ++ lh

/-- The framed endpoint of the P(z) prefix, before identifying it as S0. -/
def firstCyclePrefixTailFrame (z w q : Nat) : Config :=
  let T := firstCycleCheckpointTape z w q
  let T1 := (frameAt T 1 firstCyclePrefix22Inside
    firstCyclePrefix22End).tape
  let T2 := afterFirstCycleTwoZero T1 (3*z+10)
  let T3 := d0Sweep (2^z) T2 (3*z+12)
  frameAt T3 (3*z+12+3*(2^z)) q4TailInside q4TailEnd

/-- Absolute head coordinate at the end of P(z), after q4Tail moves
five cells left from the end of the state-1 block scan. -/
def firstCycleEndpointHead (z : Nat) : Int :=
  (3*2^z+3*z+7)

/-! ## Small list and side-lookup facts -/

private theorem sideBit_replicate_true (n i : Nat) (hi : i<n) :
    sideBit (List.replicate n true) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [sideBit]
      | succ i =>
          have hi' : i<n := by omega
          simpa [sideBit] using ih i hi'

private theorem sideBit_replicate_false (n i : Nat) (hi : i<n) :
    sideBit (List.replicate n false) i = false := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [sideBit]
      | succ i =>
          have hi' : i<n := by omega
          simpa [sideBit] using ih i hi'

/-- Lookup in the middle list of a three-way append. -/
private theorem sideBit_middle (xs ys zs : List Bool) (i : Nat)
    (hi : i < ys.length) :
    sideBit (xs ++ ys ++ zs) (xs.length+i) = sideBit ys i := by
  rw [Agent6Q4Prefix.sideBit_append_right xs (ys ++ zs)
    (xs.length+i) (by omega)]
  have hidx : xs.length+i-xs.length=i := by omega
  rw [hidx]
  exact Agent6Q4Prefix.sideBit_append_left ys zs i hi

private theorem d1pow_length_local (n : Nat) : (d1pow n).length=3*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [d1pow,d1,ih,Nat.mul_succ]

private theorem d0pow_length_local (n : Nat) : (d0pow n).length=3*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [d0pow,d0,ih,Nat.mul_succ]

/-- The all-one binary value has the all-zero-digit BinDec word. -/
private theorem binDec_allOnes (k : Nat) :
    binDec k (2^k-1) = d0pow k := by
  induction k with
  | zero => simp [binDec,d0pow]
  | succ k ih =>
      have hpow : 2^(k+1)-1 = 2*(2^k-1)+1 := by
        rw [Nat.pow_succ]
        omega
      have hlt : 2^k-1 < 2^k := by
        exact Nat.sub_lt (Nat.pow_pos (by decide)) (by decide)
      rw [hpow, binDec_odd k (2^k-1) hlt]
      simp [d0pow,ih]

private theorem firstCycleCheckpointRight_length (z : Nat) :
    (firstCycleCheckpointRight z).length =
      3+(3*z+5)+2+3*(2^z)+4 := by
  simp [firstCycleCheckpointRight,d1pow_length_local,List.length_replicate]
  omega

private theorem firstCycleCheckpointRight_ones (z i : Nat)
    (hi : i < 3*z+5) :
    sideBit (firstCycleCheckpointRight z) (3+i) = true := by
  have h := sideBit_middle
    ([false,false,false] : List Bool)
    (List.replicate (3*z+5) true)
    ([false,false] ++ d1pow (2^z) ++ [false,false,false,false])
    i hi
  exact h.trans (sideBit_replicate_true (3*z+5) i hi)

private theorem firstCycleCheckpointRight_sep0 (z : Nat) :
    sideBit (firstCycleCheckpointRight z) (3+(3*z+5)) = false := by
  have h := sideBit_middle
    ([false,false,false] ++ List.replicate (3*z+5) true)
    ([false,false] : List Bool)
    (d1pow (2^z) ++ [false,false,false,false]) 0 (by decide)
  simpa [firstCycleCheckpointRight] using h

private theorem firstCycleCheckpointRight_sep1 (z : Nat) :
    sideBit (firstCycleCheckpointRight z) (3+(3*z+5)+1) = false := by
  have h := sideBit_middle
    ([false,false,false] ++ List.replicate (3*z+5) true)
    ([false,false] : List Bool)
    (d1pow (2^z) ++ [false,false,false,false]) 1 (by decide)
  simpa [firstCycleCheckpointRight] using h

private theorem firstCycleCheckpointRight_block (z i j : Nat)
    (hi : i < 2^z) (hj : j<3) :
    sideBit (firstCycleCheckpointRight z)
      (3+(3*z+5)+2+3*i+j) = true := by
  let xs := [false,false,false] ++
    List.replicate (3*z+5) true ++ [false,false]
  have hlen : xs.length = 3+(3*z+5)+2 := by
    simp [xs,List.length_replicate]
    omega
  have h := sideBit_middle xs (d1pow (2^z))
    [false,false,false,false] (3*i+j) (by
      rw [d1pow_length_local]
      omega)
  have hbit := Agent6Q4Prefix.sideBit_d1pow_true
    (2^z) (3*i+j) (by omega)
  have hidx : xs.length+(3*i+j) =
      3+(3*z+5)+2+3*i+j := by rw [hlen]
  rw [← hidx]
  simpa [firstCycleCheckpointRight,xs] using h.trans hbit

private theorem firstCycleCheckpointRight_zeroAfter (z i : Nat)
    (hi : i≤4) :
    sideBit (firstCycleCheckpointRight z)
      (3+(3*z+5)+2+3*(2^z)+i) = false := by
  let xs := [false,false,false] ++
    List.replicate (3*z+5) true ++ [false,false] ++ d1pow (2^z)
  have hlen : xs.length = 3+(3*z+5)+2+3*(2^z) := by
    simp [xs,List.length_replicate,d1pow_length_local]
    omega
  by_cases hi4 : i<4
  · have h := sideBit_middle xs
      ([false,false,false,false] : List Bool) ([] : List Bool) i hi4
    have hidx : xs.length+i =
        3+(3*z+5)+2+3*(2^z)+i := by rw [hlen]
    rw [← hidx]
    simpa [firstCycleCheckpointRight,xs] using
      h.trans (sideBit_replicate_false 4 i hi4)
  · have hieq : i=4 := by omega
    subst i
    have hlenAll := firstCycleCheckpointRight_length z
    exact Agent6Q4Prefix.sideBit_ge_length
      (firstCycleCheckpointRight z)
      (3+(3*z+5)+2+3*(2^z)+4)
      (by rw [hlenAll]; omega)

/-- The two-sided q4 tape has the expected head-facing left lookup. -/
private theorem checkpointTape_left_cell (z w q : Nat) (i : Nat) :
    firstCycleCheckpointTape z w q (1-(i:Int)) =
      sideBit (firstCycleCheckpointLeft w q) i := by
  unfold firstCycleCheckpointTape q4TapeFromSides
  have hle : 1-(i:Int) ≤ (1:Int) := by omega
  have hcoord : 1-(1-(i:Int)) = (i:Int) := by omega
  simp [hle,hcoord]

/-- The two-sided q4 tape has the expected right-facing lookup. -/
private theorem checkpointTape_right_cell (z w q : Nat) (i : Nat) :
    firstCycleCheckpointTape z w q (1+1+(i:Int)) =
      sideBit (firstCycleCheckpointRight z) i := by
  unfold firstCycleCheckpointTape q4TapeFromSides
  have hgt : ¬ 1+1+(i:Int) ≤ (1:Int) := by omega
  have hcoord : 1+1+(i:Int)-1-1 = (i:Int) := by omega
  simp [hgt,hcoord]

/-! ## The prefix endpoint is stable to the left of its moving head -/

/-- At every cell at or left of the two-zero setup head, the composed
P(z) frame is just the setup's written one at h1, or the 22-step frame,
or the original checkpoint tape. -/
private theorem firstCyclePrefixTailFrame_tape_before_h1
    (z w q : Nat) (hz : 1≤z) (y : Int) (hy : y≤3*z+10) :
    (firstCyclePrefixTailFrame z w q).tape y =
      if y=3*z+10 then true else
        if firstCyclePrefix22Inside (y-1) then
          decide (y-1 ∈ firstCyclePrefix22End.marked)
        else firstCycleCheckpointTape z w q y := by
  let T := firstCycleCheckpointTape z w q
  let T1 := (frameAt T 1 firstCyclePrefix22Inside
    firstCyclePrefix22End).tape
  let T2 := afterFirstCycleTwoZero T1 (3*z+10)
  let T3 := d0Sweep (2^z) T2 (3*z+12)
  let g : Int := 3*z+12+3*(2^z)
  have hn : 2≤2^z := by
    have hpow := Nat.pow_le_pow_right (by decide : 0<2)
      (show 1≤z by omega)
    simpa using hpow
  have hq4 : q4TailInside (y-g) = false := by
    simp [q4TailInside,g]
    omega
  have hbefore : y < 3*z+12 := by omega
  change (frameAt T3 g q4TailInside q4TailEnd).tape y = _
  rw [frameAt_tape]
  simp [hq4]
  rw [d0Sweep_before (2^z) T2 (3*z+12) y hbefore]
  by_cases hy0 : y=3*z+10
  · simp [T2,afterFirstCycleTwoZero,hy0]
  · have hy1 : y≠3*z+11 := by omega
    simp [T2,afterFirstCycleTwoZero,hy0,hy1,T1,frameAt_tape]

/-! ## Pointwise identification of the P(z) output with S0 -/

/-- The left-facing tape of the P(z) endpoint is exactly d0^(2^z-1)
followed by the residual context. -/
private theorem firstCyclePrefixTailFrame_leftFacing
    (z w q : Nat) (hz : 1≤z) (i : Nat) :
    (firstCyclePrefixTailFrame z w q).tape
        (firstCycleEndpointHead z-(i:Int)) =
      sideBit (d0pow (2^z-1) ++ firstCycleEndpointLeft z w q) i := by
  let n := 2^z
  let k := n-1
  let T := firstCycleCheckpointTape z w q
  let T1 := (frameAt T 1 firstCyclePrefix22Inside
    firstCyclePrefix22End).tape
  let T2 := afterFirstCycleTwoZero T1 (3*z+10)
  let T3 := d0Sweep n T2 (3*z+12)
  let g : Int := 3*z+12+3*n
  let H : Int := firstCycleEndpointHead z
  have hn : 2≤n := by
    dsimp [n]
    have hpow := Nat.pow_le_pow_right (by decide : 0<2)
      (show 1≤z by omega)
    simpa using hpow
  have hleft : T2 ((3*z+12:Int)-1) = true := by
    have heq : (3*z+12:Int)-1 = (3*z+10:Int)+1 := by omega
    rw [heq]
    simp [T2,afterFirstCycleTwoZero]
  by_cases hi : i < 3*k
  · have hscan := q4Tail_output_leftCounter n T2 (3*z+12) hn hleft i
      (by dsimp [k,n]; exact hi)
    have hscan' :
        (firstCyclePrefixTailFrame z w q).tape
            (firstCycleEndpointHead z-(i:Int)) =
          sideBit (d0pow k) i := by
      change (frameAt T3 g q4TailInside q4TailEnd).tape
        (H-(i:Int)) = sideBit (d0pow k) i
      have hcoord : H-(i:Int) = g-5-(i:Int) := by
        dsimp [H,g,firstCycleEndpointHead,n]
        omega
      rw [hcoord]
      simpa [T3,n,k,g] using hscan
    have hlen : (d0pow k).length=3*k := d0pow_length_local k
    have htarget : sideBit (d0pow k ++ firstCycleEndpointLeft z w q) i =
        sideBit (d0pow k) i := by
      exact Agent6Q4Prefix.sideBit_append_left
        (d0pow k) (firstCycleEndpointLeft z w q) i (by
          rw [hlen]
          exact hi)
    exact hscan'.trans htarget.symm
  · let j := i-3*k
    have hij : i=3*k+j := by dsimp [j]; omega
    have hcoord : H-(i:Int) = (3*z+10:Int)-(j:Int) := by
      dsimp [H,k,n,firstCycleEndpointHead,j]
      omega
    have hy : (3*z+10:Int)-(j:Int) ≤ 3*z+10 := by omega
    have hlocal := firstCyclePrefixTailFrame_tape_before_h1
      z w q hz (3*z+10-(j:Int)) hy
    rw [hcoord]
    by_cases hj0 : j=0
    · subst j
      simpa [firstCycleEndpointLeft,sideBit] using hlocal
    · have hjpos : 0<j := by omega
      by_cases hjrun : j<3*z+7
      · by_cases hjlast : j=3*z+6
        · have houtside : firstCyclePrefix22Inside
              ((3*z+10:Int)-(j:Int)-1) = true := by
            rw [hjlast]
            simp [firstCyclePrefix22Inside]
          have hmarked :
              decide (((3*z+10:Int)-(j:Int)-1) ∈
                firstCyclePrefix22End.marked) = true := by
            rw [hjlast]
            simp [firstCyclePrefix22End]
          have hnothead : (3*z+10:Int)-(j:Int) ≠ 3*z+10 := by omega
          have htarget : sideBit
              (firstCycleEndpointLeft z w q) j = true := by
            rw [hjlast]
            simp [firstCycleEndpointLeft,sideBit]
          have hvalue :
              (firstCyclePrefixTailFrame z w q).tape
                ((3*z+10:Int)-(j:Int)) = true := by
            rw [hlocal]
            simp [hnothead,houtside,hmarked]
          rw [hvalue]
          exact htarget.symm
        · have hjle : j≤3*z+5 := by omega
          have hi' : 3*z+5-j < 3*z+5 := by omega
          have hsource :
              firstCycleCheckpointTape z w q
                ((3*z+10:Int)-(j:Int)) = true := by
            have hcoord' :
                (3*z+10:Int)-(j:Int) =
                  1+1+(3+(3*z+5-j:Int)) := by omega
            rw [hcoord']
            rw [checkpointTape_right_cell]
            exact firstCycleCheckpointRight_ones z (3*z+5-j) hi'
          have houtside : firstCyclePrefix22Inside
              ((3*z+10:Int)-(j:Int)-1) = false := by
            simp [firstCyclePrefix22Inside]
            omega
          have hnothead : (3*z+10:Int)-(j:Int) ≠ 3*z+10 := by omega
          have hvalue :
              (firstCyclePrefixTailFrame z w q).tape
                ((3*z+10:Int)-(j:Int)) = true := by
            rw [hlocal]
            simp [hnothead,houtside,hsource]
          have htarget :
              sideBit (firstCycleEndpointLeft z w q) j = true := by
            exact sideBit_replicate_true (3*z+7) j (by omega)
          rw [hvalue]
          exact htarget.symm
      · have hjge : 3*z+7≤j := by omega
        by_cases hjtail : 3*z+15≤j
        · let t := j-(3*z+15)
          have htailcoord : (3*z+10:Int)-(j:Int) = -5-(t:Int) := by
            dsimp [t]
            omega
          have hsource :
              firstCycleCheckpointTape z w q (-5-(t:Int)) =
                sideBit (binDec w q ++ lh) t := by
            have hcell := checkpointTape_left_cell z w q (6+t)
            have hcoord' : 1-(6+t:Int) = -5-(t:Int) := by omega
            rw [hcoord'] at hcell
            have hprefix :
                firstCycleCheckpointLeft w q =
                  ([false,true,true] ++ d0) ++ (binDec w q ++ lh) := by
              simp [firstCycleCheckpointLeft,List.append_assoc]
            rw [hprefix] at hcell
            have hlen : ([false,true,true] ++ d0).length=6 := by rfl
            rw [Agent6Q4Prefix.sideBit_append_right
              ([false,true,true] ++ d0) (binDec w q ++ lh)
              (6+t) (by rw [hlen]; omega)] at hcell
            simpa using hcell
          have houtside : firstCyclePrefix22Inside
              ((3*z+10:Int)-(j:Int)-1) = false := by
            simp [firstCyclePrefix22Inside]
            omega
          have hnothead : (3*z+10:Int)-(j:Int) ≠ 3*z+10 := by omega
          have hvalue :
              (firstCyclePrefixTailFrame z w q).tape
                ((3*z+10:Int)-(j:Int)) =
                  sideBit (binDec w q ++ lh) t := by
            rw [hlocal]
            rw [htailcoord]
            simp [hnothead,houtside,hsource]
          have htarget :
              sideBit (firstCycleEndpointLeft z w q) j =
                sideBit (binDec w q ++ lh) t := by
            change sideBit
              ((List.replicate (3*z+7) true ++
                [false,true,false,false] ++ List.replicate 4 true) ++
                (binDec w q ++ lh)) j = _
            have hlen :
                (List.replicate (3*z+7) true ++
                  [false,true,false,false] ++ List.replicate 4 true).length =
                    3*z+15 := by simp
            rw [Agent6Q4Prefix.sideBit_append_right _ _
              j (by rw [hlen]; omega)]
            simp [t]
          rw [hvalue]
          exact htarget.symm
        · have hjlt : j<3*z+15 := by omega
          have hcases :
              j=3*z+7 ∨ j=3*z+8 ∨ j=3*z+9 ∨ j=3*z+10 ∨
              j=3*z+11 ∨ j=3*z+12 ∨ j=3*z+13 ∨ j=3*z+14 := by omega
          rcases hcases with h7|h8|h9|h10|h11|h12|h13|h14
          · subst j
            have hlocal7 := hlocal
            have hcoord7 : (3*z+10:Int)-(3*z+7:Int)=3 := by omega
            rw [hcoord7] at hlocal7
            have hnothead : (3:Int) ≠ 3*z+10 := by omega
            have hvalue :
                (firstCyclePrefixTailFrame z w q).tape 3 = false := by
              simpa [hnothead,firstCyclePrefix22Inside,
                firstCyclePrefix22End] using hlocal7
            have htarget :
                sideBit (firstCycleEndpointLeft z w q) (3*z+7) = false := by
              simp [firstCycleEndpointLeft,sideBit]
            exact hvalue.trans htarget.symm
          · subst j
            have hlocal8 := hlocal
            have hcoord8 : (3*z+10:Int)-(3*z+8:Int)=2 := by omega
            rw [hcoord8] at hlocal8
            have hnothead : (2:Int) ≠ 3*z+10 := by omega
            have hvalue :
                (firstCyclePrefixTailFrame z w q).tape 2 = true := by
              simpa [hnothead,firstCyclePrefix22Inside,
                firstCyclePrefix22End] using hlocal8
            have htarget :
                sideBit (firstCycleEndpointLeft z w q) (3*z+8) = true := by
              simp [firstCycleEndpointLeft,sideBit]
            exact hvalue.trans htarget.symm
          · subst j
            have hlocal9 := hlocal
            have hcoord9 : (3*z+10:Int)-(3*z+9:Int)=1 := by omega
            rw [hcoord9] at hlocal9
            have hnothead : (1:Int) ≠ 3*z+10 := by omega
            have hvalue :
                (firstCyclePrefixTailFrame z w q).tape 1 = false := by
              simpa [hnothead,firstCyclePrefix22Inside,
                firstCyclePrefix22End] using hlocal9
            have htarget :
                sideBit (firstCycleEndpointLeft z w q) (3*z+9) = false := by
              simp [firstCycleEndpointLeft,sideBit]
            exact hvalue.trans htarget.symm
          · subst j
            have hlocal10 := hlocal
            have hcoord10 : (3*z+10:Int)-(3*z+10:Int)=0 := by omega
            rw [hcoord10] at hlocal10
            have hnothead : (0:Int) ≠ 3*z+10 := by omega
            have hvalue :
                (firstCyclePrefixTailFrame z w q).tape 0 = false := by
              simpa [hnothead,firstCyclePrefix22Inside,
                firstCyclePrefix22End] using hlocal10
            have htarget :
                sideBit (firstCycleEndpointLeft z w q) (3*z+10) = false := by
              simp [firstCycleEndpointLeft,sideBit]
            exact hvalue.trans htarget.symm
          · subst j
            have hlocal11 := hlocal
            have hcoord11 : (3*z+10:Int)-(3*z+11:Int) = -1 := by omega
            rw [hcoord11] at hlocal11
            have hnothead : (-1:Int) ≠ 3*z+10 := by omega
            have hvalue :
                (firstCyclePrefixTailFrame z w q).tape (-1) = true := by
              simpa [hnothead,firstCyclePrefix22Inside,
                firstCyclePrefix22End] using hlocal11
            have htarget :
                sideBit (firstCycleEndpointLeft z w q) (3*z+11) = true := by
              simp [firstCycleEndpointLeft,sideBit]
            exact hvalue.trans htarget.symm
          · subst j
            have hlocal12 := hlocal
            have hcoord12 : (3*z+10:Int)-(3*z+12:Int) = -2 := by omega
            rw [hcoord12] at hlocal12
            have hnothead : (-2:Int) ≠ 3*z+10 := by omega
            have hvalue :
                (firstCyclePrefixTailFrame z w q).tape (-2) = true := by
              simpa [hnothead,firstCyclePrefix22Inside,
                firstCyclePrefix22End] using hlocal12
            have htarget :
                sideBit (firstCycleEndpointLeft z w q) (3*z+12) = true := by
              simp [firstCycleEndpointLeft,sideBit]
            exact hvalue.trans htarget.symm
          · subst j
            have hlocal13 := hlocal
            have hcoord13 : (3*z+10:Int)-(3*z+13:Int) = -3 := by omega
            rw [hcoord13] at hlocal13
            have hnothead : (-3:Int) ≠ 3*z+10 := by omega
            have hvalue :
                (firstCyclePrefixTailFrame z w q).tape (-3) = true := by
              simpa [hnothead,firstCyclePrefix22Inside,
                firstCyclePrefix22End] using hlocal13
            have htarget :
                sideBit (firstCycleEndpointLeft z w q) (3*z+13) = true := by
              simp [firstCycleEndpointLeft,sideBit]
            exact hvalue.trans htarget.symm
          · subst j
            have hlocal14 := hlocal
            have hcoord14 : (3*z+10:Int)-(3*z+14:Int) = -4 := by omega
            rw [hcoord14] at hlocal14
            have hnothead : (-4:Int) ≠ 3*z+10 := by omega
            have hsrc : firstCycleCheckpointTape z w q (-4) = true := by
              have hcell := checkpointTape_left_cell z w q 5
              simpa [firstCycleCheckpointLeft,d0,sideBit] using hcell
            have hvalue :
                (firstCyclePrefixTailFrame z w q).tape (-4) = true := by
              simpa [hnothead,firstCyclePrefix22Inside,hsrc] using hlocal14
            have htarget :
                sideBit (firstCycleEndpointLeft z w q) (3*z+14) = true := by
              simp [firstCycleEndpointLeft,sideBit]
            exact hvalue.trans htarget.symm

/-- The right-facing tape of the P(z) endpoint is exactly s0RightFacing 0. -/
private theorem firstCyclePrefixTailFrame_rightFacing
    (z w q : Nat) (hz : 1≤z) (i : Nat) :
    (firstCyclePrefixTailFrame z w q).tape
        (firstCycleEndpointHead z+1+(i:Int)) =
      sideBit (s0RightFacing 0) i := by
  let T := firstCycleCheckpointTape z w q
  let T1 := (frameAt T 1 firstCyclePrefix22Inside
    firstCyclePrefix22End).tape
  let T2 := afterFirstCycleTwoZero T1 (3*z+10)
  let T3 := d0Sweep (2^z) T2 (3*z+12)
  let g : Int := 3*z+12+3*(2^z)
  let H : Int := firstCycleEndpointHead z
  change (frameAt T3 g q4TailInside q4TailEnd).tape
    (H+1+(i:Int)) = sideBit (s0RightFacing 0) i
  by_cases hi : i<9
  · have hinside : q4TailInside (H+1+(i:Int)-g) = true := by
      simp [q4TailInside,H,g,firstCycleEndpointHead]
      omega
    have hbit :
        decide ((H+1+(i:Int)-g) ∈ q4TailEnd.marked) =
          sideBit (s0RightFacing 0) i := by
      have hcases :
          i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨
          i=6 ∨ i=7 ∨ i=8 := by omega
      rcases hcases with h0|h1|h2|h3|h4|h5|h6|h7|h8
      all_goals subst i <;>
        simp [H,firstCycleEndpointHead,g,q4TailEnd,
          s0RightFacing,d1pow,d1,sideBit]
    rw [frameAt_tape]
    simp [hinside,hbit]
  · let x := H+1+(i:Int)
    have hge : g+5≤x := by
      dsimp [x,H,firstCycleEndpointHead,g]
      omega
    have hframe :
        (frameAt T3 g q4TailInside q4TailEnd).tape x = T3 x := by
      rw [frameAt_tape]
      have hnot : q4TailInside (x-g)=false := by
        simp [q4TailInside]
        omega
      simp [hnot]
    have hsw : T3 x=T2 x := by
      change d0Sweep (2^z) T2 (3*z+12) x = T2 x
      exact d0Sweep_after (2^z) T2 (3*z+12) x (by omega)
    have htwo : T2 x=T1 x := by
      simp [T2,afterFirstCycleTwoZero]
      omega
    have h22 : T1 x=T x := by
      simp [T1,frameAt_tape,firstCyclePrefix22Inside]
      omega
    let r := Int.toNat (x-2)
    have hr : (r:Int)=x-2 := by
      dsimp [r]
      exact Int.toNat_of_nonneg (by omega)
    have hidx : (firstCycleCheckpointRight z).length ≤ r := by
      rw [firstCycleCheckpointRight_length]
      have hr' : (r:Int)=x-2 := hr
      dsimp [x,H,firstCycleEndpointHead,g] at hr'
      omega
    have hsource : T x=false := by
      have hcell := checkpointTape_right_cell z w q r
      have hcoord : 1+1+(r:Int)=x := by
        dsimp [x]
        omega
      rw [hcoord] at hcell
      rw [hcell]
      exact Agent6Q4Prefix.sideBit_ge_length
        (firstCycleCheckpointRight z) r hidx
    have htarget : sideBit (s0RightFacing 0) i=false := by
      have hlen : (s0RightFacing 0).length=9 := by
        simp [s0RightFacing,d1pow_length_local]
      exact Agent6Q4Prefix.sideBit_ge_length
        (s0RightFacing 0) i (by omega)
    rw [hframe,hsw,htwo,h22,hsource,htarget]

/-- The P(z) prefix endpoint is an exact arbitrary-left S0 configuration.
The source checkpoint has left side 011001 ++ BinDec(w+1,2q+1) ++ lh,
equivalently 011 ++ d0 ++ BinDec(w,q) ++ lh, and the right side is the
observed first-q4 nested-counter suffix. -/
theorem firstCyclePrefix_to_s0DrainInput
    (z w q : Nat) (hz : 1≤z) (hq : q<2^w) :
    run tm2 (3*2^z+3*z+58)
      ⟨4,1,firstCycleCheckpointTape z w q⟩ =
    some (s0Config (firstCycleEndpointLeft z w q)
      (2^z-1) (2^(2^z-1)-1) 0 (firstCycleEndpointHead z)) := by
  let T := firstCycleCheckpointTape z w q
  let m := 3*z+5
  let n := 2^z
  have hleftBits :
      sideBit (firstCycleCheckpointLeft w q) 0 = false ∧
      sideBit (firstCycleCheckpointLeft w q) 1 = true ∧
      sideBit (firstCycleCheckpointLeft w q) 2 = true ∧
      sideBit (firstCycleCheckpointLeft w q) 3 = false ∧
      sideBit (firstCycleCheckpointLeft w q) 4 = false := by
    simp [firstCycleCheckpointLeft,d0,sideBit]
  have hinput22 :
      T (1-4) = false ∧
      T (1-3) = false ∧
      T (1-2) = true ∧
      T (1-1) = true ∧
      T 1 = false ∧
      T (1+1) = false ∧
      T (1+2) = false ∧
      T (1+3) = false := by
    have hL0 := checkpointTape_left_cell z w q 0
    have hL1 := checkpointTape_left_cell z w q 1
    have hL2 := checkpointTape_left_cell z w q 2
    have hL3 := checkpointTape_left_cell z w q 3
    have hL4 := checkpointTape_left_cell z w q 4
    have hR0 := checkpointTape_right_cell z w q 0
    have hR1 := checkpointTape_right_cell z w q 1
    have hR2 := checkpointTape_right_cell z w q 2
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa using hL4.trans hleftBits.2.2.2.2
    · simpa using hL3.trans hleftBits.2.2.2.1
    · simpa using hL2.trans hleftBits.2.2.1
    · simpa using hL1.trans hleftBits.2.1
    · simpa using hL0.trans hleftBits.1
    · simpa [firstCycleCheckpointRight] using hR0
    · simpa [firstCycleCheckpointRight] using hR1
    · simpa [firstCycleCheckpointRight] using hR2
  have hfirst : linearRightOnes T (1+4) m := by
    intro i hi
    have hcoord : 1+4+(i:Int) = 1+1+(3+i:Int) := by omega
    rw [hcoord,checkpointTape_right_cell]
    exact firstCycleCheckpointRight_ones z i hi
  have hsep0 : T (1+4+(m:Int)) = false := by
    have hcoord : 1+4+(m:Int) = 1+1+(3+m:Int) := by omega
    rw [hcoord,checkpointTape_right_cell]
    exact firstCycleCheckpointRight_sep0 z
  have hsep1 : T (1+4+(m:Int)+1) = false := by
    have hcoord : 1+4+(m:Int)+1 = 1+1+(3+m+1:Int) := by omega
    rw [hcoord,checkpointTape_right_cell]
    exact firstCycleCheckpointRight_sep1 z
  have hblocks : d1BlocksOn T (1+4+(m:Int)+2) n := by
    intro i hi
    refine ⟨?_,?_,?_⟩
    · have hcoord : 1+4+(m:Int)+2+3*(i:Int) =
          1+1+(3+m+2+3*i:Int) := by omega
      rw [hcoord,checkpointTape_right_cell]
      exact firstCycleCheckpointRight_block z i 0 hi (by omega)
    · have hcoord : 1+4+(m:Int)+2+3*(i:Int)+1 =
          1+1+(3+m+2+3*i+1:Int) := by omega
      rw [hcoord,checkpointTape_right_cell]
      exact firstCycleCheckpointRight_block z i 1 hi (by omega)
    · have hcoord : 1+4+(m:Int)+2+3*(i:Int)+2 =
          1+1+(3+m+2+3*i+2:Int) := by omega
      rw [hcoord,checkpointTape_right_cell]
      exact firstCycleCheckpointRight_block z i 2 hi (by omega)
  have hzeros : ∀ i : Nat, i≤4 →
      T (1+4+(m:Int)+2+3*(n:Int)+(i:Int)) = false := by
    intro i hi
    have hcoord : 1+4+(m:Int)+2+3*(n:Int)+(i:Int) =
        1+1+(3+m+2+3*n+i:Int) := by omega
    rw [hcoord,checkpointTape_right_cell]
    exact firstCycleCheckpointRight_zeroAfter z i hi
  have hn : 2≤n := by
    dsimp [n]
    have hpow := Nat.pow_le_pow_right (by decide : 0<2)
      (show 1≤z by omega)
    simpa using hpow
  have hprefix := firstCyclePrefix_from_checkpoint
    m n T 1 hinput22 hfirst hsep0 hsep1 hblocks hzeros hn
  have hframe :
      firstCyclePrefixTailFrame z w q =
        s0Config (firstCycleEndpointLeft z w q)
          (2^z-1) (2^(2^z-1)-1) 0 (firstCycleEndpointHead z) := by
    apply config_ext
    · simp [firstCyclePrefixTailFrame,frameAt_state,q4TailEnd,
        s0Config_state]
    · simp [firstCyclePrefixTailFrame,frameAt_head,q4TailEnd,
        firstCycleEndpointHead] <;> omega
    · funext x
      by_cases hx : x≤firstCycleEndpointHead z
      · let i := Int.toNat (firstCycleEndpointHead z-x)
        have hnat : (i:Int)=firstCycleEndpointHead z-x := by
          dsimp [i]
          exact Int.toNat_of_nonneg (by omega)
        have hcoord : x=firstCycleEndpointHead z-(i:Int) := by omega
        rw [hcoord]
        have hcell := s0Config_left_cell
          (firstCycleEndpointLeft z w q) (2^z-1)
          (2^(2^z-1)-1) 0 (firstCycleEndpointHead z) i
        rw [hcell,binDec_allOnes]
        exact firstCyclePrefixTailFrame_leftFacing z w q hz i
      · let i := Int.toNat (x-firstCycleEndpointHead z-1)
        have hnat : (i:Int)=x-firstCycleEndpointHead z-1 := by
          dsimp [i]
          exact Int.toNat_of_nonneg (by omega)
        have hcoord : x=firstCycleEndpointHead z+1+(i:Int) := by omega
        rw [hcoord]
        have hcell := s0Config_right_cell
          (firstCycleEndpointLeft z w q) (2^z-1)
          (2^(2^z-1)-1) 0 (firstCycleEndpointHead z) i
        rw [hcell]
        exact firstCyclePrefixTailFrame_rightFacing z w q hz i
  have hrun0 := hprefix
  have hrun :
      run tm2 (3*2^z+3*z+58) ⟨4,1,T⟩ =
        some (firstCyclePrefixTailFrame z w q) := by
    have hrun' :
        run tm2 (22+(3*z+5)+2+3*(2^z)+29) ⟨4,1,T⟩ =
          some (firstCyclePrefixTailFrame z w q) := by
      simpa [m,n,firstCyclePrefixTailFrame,T] using hrun0
    rw [firstCyclePrefix_cost z] at hrun'
    exact hrun'
  rw [hrun,hframe]

#print axioms firstCyclePrefix_to_s0DrainInput
#print axioms firstCyclePrefixTailFrame_leftFacing
#print axioms firstCyclePrefixTailFrame_rightFacing

end BB6Coverage.Agent48PositiveZFirstCycleEndpoint
