import PositiveZFirstCycleEndpoint
import PositiveZSecondCyclePrefix
import Q4S0FirstCycleMacros
import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# Compose the positive-z first cycle into the second q4 prefix

Under the odd-q source condition, the exact Q-postlude output of the
first q4 cycle supplies every hypothesis of the second checkpoint's
34-step/E-scan/two-zero/d1-block/q4Tail composition. This is an
intermediate source draft; it has not yet passed the exact local
Lean 4.36.0-rc2 dependency-closure preflight.
-/

namespace BB6Coverage.Agent24PositiveZSecondPrefix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48PositiveZFirstCycle
open BB6Coverage.Agent42PositiveZFirstCycleS0Input
open BB6Coverage.Agent48PositiveZFirstCycleEndpoint
open BB6Coverage.Agent48PositiveZSecondCycle
open BB6Coverage.Agent48PositiveZSecondCyclePrefix
open BB6Coverage.Agent48Q4S0Macros

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

private theorem sideBit_false_of_ge_length
    (xs : List Bool) (i : Nat) (hi : xs.length≤i) :
    sideBit xs i = false := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons b xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          simp only [sideBit]
          apply ih
          simp at hi
          omega

private theorem s0RightFacing_after_six (b i : Nat) (hi : 6≤i) :
    sideBit (s0RightFacing b) i =
      sideBit (d1pow (b+1)) (i-6) := by
  unfold s0RightFacing
  rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
    [false,true,true,true,false,false] (d1pow (b+1)) i (by simp; omega)]
  simp

private theorem s0RightFacing_firstThree (b i : Nat)
    (hi : i=1 ∨ i=2 ∨ i=3) :
    sideBit (s0RightFacing b) i = true := by
  rcases hi with h|h|h <;> subst i <;>
    simp [s0RightFacing,sideBit]

private theorem s0RightFacing_sep4 (b : Nat) :
    sideBit (s0RightFacing b) 4 = false := by
  simp [s0RightFacing,sideBit]

private theorem s0RightFacing_sep5 (b : Nat) :
    sideBit (s0RightFacing b) 5 = false := by
  simp [s0RightFacing,sideBit]

private theorem residualLeft_fourOnes (z w q : Nat) :
    ∀ j : Nat, j<4 →
      sideBit
        (firstCycleResidualLeft z
          (List.replicate 4 true ++ binDec w q ++ lh))
        (3*z+11+j) = true := by
  intro j hj
  let m : Nat := 3*z+7
  have hidx : 3*z+11+j = m+4+j := by dsimp [m]; omega
  rw [hidx]
  unfold firstCycleResidualLeft
  rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
    (List.replicate m true)
    ([false,true,false,false] ++ List.replicate 4 true ++ binDec w q ++ lh)
    (m+4+j) (by simp [List.length_replicate])]
  have hidx1 : m+4+j-(List.replicate m true).length = 4+j := by
    simp [List.length_replicate]
    omega
  rw [hidx1]
  rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
    [false,true,false,false]
    (List.replicate 4 true ++ binDec w q ++ lh)
    (4+j) (by simp)]
  have hidx2 : 4+j-[false,true,false,false].length = j := by
    simp
  rw [hidx2]
  exact sideBit_replicate_true 4 j hj

private theorem residualLeft_d0FirstTwo (z w q : Nat)
    (hq : q<2^w) (hqOdd : q%2=1) :
    let l := firstCycleResidualLeft z
      (List.replicate 4 true ++ binDec w q ++ lh)
    sideBit l (3*z+15) = false ∧
    sideBit l (3*z+16) = false := by
  let r : Nat := q/2
  have hw : 1≤w := by
    by_contra hn
    have hw0 : w=0 := by omega
    subst w
    simp at hq
    omega
  have hpow : 2^w = 2*2^(w-1) := by
    rw [show w=(w-1)+1 by omega, Nat.pow_succ]
    omega
  have hr : r<2^(w-1) := by
    dsimp [r]
    rw [hpow] at hq
    omega
  have hqeq : q=2*r+1 := by dsimp [r]; omega
  have hbin : binDec w q = d0 ++ binDec (w-1) r := by
    rw [show w=(w-1)+1 by omega, hqeq]
    exact binDec_odd (w-1) r hr
  let m : Nat := 3*z+7
  have hbit (j : Nat) (hj : j<2) :
      sideBit
        (firstCycleResidualLeft z
          (List.replicate 4 true ++ binDec w q ++ lh))
        (m+8+j) = false := by
    unfold firstCycleResidualLeft
    rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
      (List.replicate m true)
      ([false,true,false,false] ++ List.replicate 4 true ++ binDec w q ++ lh)
      (m+8+j) (by simp [List.length_replicate])]
    have hidx1 : m+8+j-(List.replicate m true).length = 8+j := by
      simp [List.length_replicate]
      omega
    rw [hidx1]
    rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
      [false,true,false,false]
      (List.replicate 4 true ++ binDec w q ++ lh)
      (8+j) (by simp)]
    have hidx2 : 8+j-[false,true,false,false].length = 4+j := by
      simp
    rw [hidx2]
    rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
      (List.replicate 4 true) (binDec w q ++ lh)
      (4+j) (by simp [List.length_replicate])]
    have hidx3 : 4+j-(List.replicate 4 true).length = j := by
      simp [List.length_replicate]
    rw [hidx3,hbin]
    cases j with
    | zero => simp [d0,sideBit]
    | succ j =>
        have hj0 : j=0 := by omega
        subst j
        simp [d0,sideBit]
  refine ⟨?_,?_⟩
  · simpa [m] using hbit 0 (by omega)
  · simpa [m] using hbit 1 (by omega)

/-- The old state-3 sweep and the first-cycle counted sweep are the same
infinite-tape update, cell for cell. -/
private theorem s0LeftSweep_eq_sweptLeft
    (n : Nat) (T : Int → Bool) (h : Int) :
    s0LeftSweep n T h = sweptLeft n T h := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
      have hmicro : afterS0LeftOne T h = holeThree T h := by
        funext x
        by_cases hx0 : x=h
        · subst x
          simp [afterS0LeftOne,holeThree]
        · by_cases hx1 : x=h+1
          · subst x
            simp [afterS0LeftOne,holeThree]
          · simp [afterS0LeftOne,holeThree,hx0,hx1]
      simpa [s0LeftSweep,sweptLeft,hmicro] using
        ih (afterS0LeftOne T h) (h-1)

/-- The first-cycle Q output supplies the complete second-checkpoint
source window and all right-stream hypotheses. The theorem composes the
first q4 cycle with the existing second-cycle prefix through q4Tail. -/
theorem positiveZFirstCycle_then_secondCyclePrefix
    (z w q : Nat) (hz : 1≤z) (hq : q<2^w) (hqOdd : q%2=1) :
    let a : Nat := 2^z-1
    let m : Nat := 3*2^z+3*z+7
    let n : Nat := 2^a
    let tail := List.replicate 4 true ++ binDec w q ++ lh
    let S := firstCycleS0DrainOutput z tail
    let H : Int := m
    let k : Nat := 3*a+(3*z+7)
    let U := sweptLeft k S.tape H
    let V := (frameAt U 3 firstCyclePostludeInside firstCyclePostludeEnd).tape
    let C1 :=
      (3*2^z+3*z+58) +
        ((6*4^a+42*2^a-12*a-48)+(9*2^z+9*z+16))
    let C2 := 34+m+2+3*n+29
    let T1 := (frameAt V 1
      secondCyclePrefix34Inside secondCyclePrefix34End).tape
    let h1 : Int := 1+4+(m:Int)
    let T2 := afterFirstCycleTwoZero T1 h1
    let h2 : Int := h1+2
    let T3 := d0Sweep n T2 h2
    let g : Int := h2+3*(n:Int)
    run tm2 (C1+C2) ⟨4,1,firstCycleCheckpointTape z w q⟩ =
      some (frameAt T3 g q4TailInside q4TailEnd) := by
  let a : Nat := 2^z-1
  let m : Nat := 3*2^z+3*z+7
  let n : Nat := 2^a
  let tail := List.replicate 4 true ++ binDec w q ++ lh
  let S := firstCycleS0DrainOutput z tail
  let H : Int := m
  let k : Nat := 3*a+(3*z+7)
  let U := sweptLeft k S.tape H
  let V := (frameAt U 3 firstCyclePostludeInside firstCyclePostludeEnd).tape
  let C1 :=
    (3*2^z+3*z+58) +
      ((6*4^a+42*2^a-12*a-48)+(9*2^z+9*z+16))
  let C2 := 34+m+2+3*n+29
  let T1 := (frameAt V 1
    secondCyclePrefix34Inside secondCyclePrefix34End).tape
  let h1 : Int := 1+4+(m:Int)
  let T2 := afterFirstCycleTwoZero T1 h1
  let h2 : Int := h1+2
  let T3 : Int := d0Sweep n T2 h2
  let g : Int := h2+3*(n:Int)

  have hM : (m:Int)=H := by rfl
  have hHk : H-(k:Int)=3 := by
    dsimp [H,k,m,a]
    omega
  have hkpos : 0<k := by
    dsimp [k,a]
    have hpow : 1≤2^z := by positivity
    omega
  have hones : leftOnes S.tape H k := by
    simpa [S,H,k,m,a,tail,firstCycleS0DrainOutput] using
      firstCycleS0DrainOutput_leftOnes z tail
  have hright : S.tape (H+1)=false := by
    simpa [S,H,m,firstCycleS0DrainOutput] using
      firstCycleS0DrainOutput_rightZero z tail

  have hshift0 := s0LeftSweep_shift k S.tape H hkpos
  have hshift : ∀ x : Int,
      U x =
        (if x=H-(k:Int)+1 then false
         else if H-(k:Int)+2≤x ∧ x≤H+1 then true
         else S.tape x) := by
    intro x
    have h := hshift0 x
    simpa [U,s0LeftSweep_eq_sweptLeft] using h

  have hleftFacing :
      s0LeftFacing (firstCycleResidualLeft z tail) a 0 =
        d1pow a ++ firstCycleResidualLeft z tail := by
    simp [s0LeftFacing,binDec_zero]

  have hSleft (i : Nat) :
      S.tape (H-(i:Int)) =
        sideBit (d1pow a ++ firstCycleResidualLeft z tail) i := by
    have hcell := s0Config_left_cell
      (firstCycleResidualLeft z tail) a 0 (2^a-1) H i
    rw [hleftFacing] at hcell
    simpa [S,firstCycleS0DrainOutput,tail,H,a] using hcell

  have hSright (i : Nat) :
      S.tape (H+1+(i:Int)) =
        sideBit (s0RightFacing (2^a-1)) i := by
    have hcell := s0Config_right_cell
      (firstCycleResidualLeft z tail) a 0 (2^a-1) H i
    simpa [S,firstCycleS0DrainOutput,tail,H,a] using hcell

  have hVoutside (x : Int)
      (hout : firstCyclePostludeInside (x-3)=false) :
      V x = U x := by
    simp [V,frameAt_tape,hout]

  have hVleft (x : Int) (hx : x≤-1) :
      V x = S.tape x := by
    have hout : firstCyclePostludeInside (x-3)=false := by
      simp [firstCyclePostludeInside]
      omega
    rw [hVoutside x hout]
    have hs := hshift x
    have hbefore : x < H-(k:Int)+1 := by
      rw [hHk]
      omega
    rw [hs]
    simp [hbefore]

  have hV0 : V 0 = true := by
    simp [V,frameAt_tape,firstCyclePostludeInside,firstCyclePostludeEnd]
  have hV1 : V 1 = false := by
    simp [V,frameAt_tape,firstCyclePostludeInside,firstCyclePostludeEnd]
  have hV2 : V 2 = false := by
    simp [V,frameAt_tape,firstCyclePostludeInside,firstCyclePostludeEnd]
  have hV3 : V 3 = false := by
    simp [V,frameAt_tape,firstCyclePostludeInside,firstCyclePostludeEnd]

  have hV4 : V 4 = false := by
    have hout : firstCyclePostludeInside ((4:Int)-3)=false := by
      simp [firstCyclePostludeInside]
    rw [hVoutside 4 hout]
    have hs := hshift 4
    rw [hHk] at hs
    simpa using hs

  have hM_a : m = 3*a+(3*z+7)+3 := by
    dsimp [m,a]
    omega
  have hrep (j : Nat) (hj : j<4) :
      sideBit (firstCycleResidualLeft z tail) (3*z+11+j) = true :=
    residualLeft_fourOnes z w q j hj
  have hbinbits := residualLeft_d0FirstTwo z w q hq hqOdd

  have hVminus4 : V (-4) = true := by
    rw [hVleft (-4) (by omega)]
    have hcell := hSleft (m+4)
    have hcoord : H-((m+4:Int)) = -4 := by dsimp [H,m]; omega
    rw [hcoord] at hcell
    have hidx : m+4-(d1pow a).length = 3*z+11+3 := by
      rw [d1pow_length]
      dsimp [m,a]
      omega
    rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
      (d1pow a) (firstCycleResidualLeft z tail) (m+4)
      (by rw [d1pow_length]; dsimp [m,a]; omega),hidx] at hcell
    simpa [tail] using hcell.trans (hrep 3 (by omega))

  have hVminus3 : V (-3) = true := by
    rw [hVleft (-3) (by omega)]
    have hcell := hSleft (m+3)
    have hcoord : H-((m+3:Int)) = -3 := by dsimp [H,m]; omega
    rw [hcoord] at hcell
    have hidx : m+3-(d1pow a).length = 3*z+11+2 := by
      rw [d1pow_length]
      dsimp [m,a]
      omega
    rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
      (d1pow a) (firstCycleResidualLeft z tail) (m+3)
      (by rw [d1pow_length]; dsimp [m,a]; omega),hidx] at hcell
    simpa [tail] using hcell.trans (hrep 2 (by omega))

  have hVminus2 : V (-2) = true := by
    rw [hVleft (-2) (by omega)]
    have hcell := hSleft (m+2)
    have hcoord : H-((m+2:Int)) = -2 := by dsimp [H,m]; omega
    rw [hcoord] at hcell
    have hidx : m+2-(d1pow a).length = 3*z+11+1 := by
      rw [d1pow_length]
      dsimp [m,a]
      omega
    rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
      (d1pow a) (firstCycleResidualLeft z tail) (m+2)
      (by rw [d1pow_length]; dsimp [m,a]; omega),hidx] at hcell
    simpa [tail] using hcell.trans (hrep 1 (by omega))

  have hVminus1 : V (-1) = true := by
    rw [hVleft (-1) (by omega)]
    have hcell := hSleft (m+1)
    have hcoord : H-((m+1:Int)) = -1 := by dsimp [H,m]; omega
    rw [hcoord] at hcell
    have hidx : m+1-(d1pow a).length = 3*z+11 := by
      rw [d1pow_length]
      dsimp [m,a]
      omega
    rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
      (d1pow a) (firstCycleResidualLeft z tail) (m+1)
      (by rw [d1pow_length]; dsimp [m,a]; omega),hidx] at hcell
    simpa [tail] using hcell.trans (hrep 0 (by omega))

  have hVminus5 : V (-5) = false := by
    rw [hVleft (-5) (by omega)]
    have hcell := hSleft (m+5)
    have hcoord : H-((m+5:Int)) = -5 := by dsimp [H,m]; omega
    rw [hcoord] at hcell
    have hidx : m+5-(d1pow a).length = 3*z+15 := by
      rw [d1pow_length]
      dsimp [m,a]
      omega
    rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
      (d1pow a) (firstCycleResidualLeft z tail) (m+5)
      (by rw [d1pow_length]; dsimp [m,a]; omega),hidx] at hcell
    exact hcell.trans hbinbits.1

  have hVminus6 : V (-6) = false := by
    rw [hVleft (-6) (by omega)]
    have hcell := hSleft (m+6)
    have hcoord : H-((m+6:Int)) = -6 := by dsimp [H,m]; omega
    rw [hcoord] at hcell
    have hidx : m+6-(d1pow a).length = 3*z+16 := by
      rw [d1pow_length]
      dsimp [m,a]
      omega
    rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
      (d1pow a) (firstCycleResidualLeft z tail) (m+6)
      (by rw [d1pow_length]; dsimp [m,a]; omega),hidx] at hcell
    exact hcell.trans hbinbits.2

  have hinput34 :
      V (1-7) = false ∧
      V (1-6) = false ∧
      V (1-5) = true ∧
      V (1-4) = true ∧
      V (1-3) = true ∧
      V (1-2) = true ∧
      V (1-1) = true ∧
      V 1 = false ∧
      V 2 = false ∧
      V 3 = false ∧
      V 4 = false := by
    norm_num at *
    exact ⟨hVminus6,hVminus5,hVminus4,hVminus3,hVminus2,
      hVminus1,hV0,hV1,hV2,hV3,hV4⟩

  have hfirst : linearRightOnes V 5 m := by
    intro i hi
    let x : Int := 5+(i:Int)
    have hout : firstCyclePostludeInside (x-3)=false := by
      simp [firstCyclePostludeInside,x]
      omega
    have hVx : V x = U x := hVoutside x hout
    by_cases hx : x≤H+1
    · have hshiftx := hshift x
      have hlow : H-(k:Int)+2≤x := by
        rw [hHk]
        dsimp [x,m]
        omega
      have hneq : x≠H-(k:Int)+1 := by
        rw [hHk]
        dsimp [x,m]
        omega
      have hcond : H-(k:Int)+2≤x ∧ x≤H+1 := ⟨hlow,hx⟩
      rw [hVx,hshiftx]
      simp [hneq,hcond]
    · have hx2 : H+2≤x := by omega
      have hx3 : x≤H+4 := by
        dsimp [x,H,m]
        omega
      let j : Nat := Int.toNat (x-H-1)
      have hj : (j:Int)=x-H-1 := by
        dsimp [j]
        exact Int.toNat_of_nonneg (by omega)
      have hjrange : j=1 ∨ j=2 ∨ j=3 := by
        dsimp [j]
        omega
      have hsource : S.tape x = sideBit (s0RightFacing (2^a-1)) j := by
        have hcell := hSright j
        have hcoord : H+1+(j:Int)=x := by omega
        simpa [hcoord] using hcell
      have hsrc : sideBit (s0RightFacing (2^a-1)) j = true :=
        s0RightFacing_firstThree (2^a-1) j hjrange
      have hU : U x = true := by
        have hs := hshift x
        have hneq : x≠H-(k:Int)+1 := by
          rw [hHk]
          omega
        have hnot : ¬(H-(k:Int)+2≤x ∧ x≤H+1) := by omega
        rw [hs]
        simp [hneq,hnot,hsource,hsrc]
      rw [hVx,hU]

  have hVafter (x : Int) (hx : H+1<x) :
      V x = S.tape x := by
    have hout : firstCyclePostludeInside (x-3)=false := by
      simp [firstCyclePostludeInside]
      omega
    rw [hVoutside x hout]
    have hs := hshift x
    have hneq : x≠H-(k:Int)+1 := by
      rw [hHk]
      omega
    have hnot : ¬(H-(k:Int)+2≤x ∧ x≤H+1) := by omega
    rw [hs]
    simp [hneq,hnot]

  have hsep0 : V (1+4+(m:Int)) = false := by
    have hcoord : 1+4+(m:Int)=H+5 := by dsimp [H]; omega
    rw [hcoord,hVafter (H+5) (by omega)]
    have hcell := hSright 4
    have hcoord' : H+1+(4:Int)=H+5 := by omega
    rw [hcoord'] at hcell
    exact hcell.trans (s0RightFacing_sep4 (2^a-1))

  have hsep1 : V (1+4+(m:Int)+1) = false := by
    have hcoord : 1+4+(m:Int)+1=H+6 := by dsimp [H]; omega
    rw [hcoord,hVafter (H+6) (by omega)]
    have hcell := hSright 5
    have hcoord' : H+1+(5:Int)=H+6 := by omega
    rw [hcoord'] at hcell
    exact hcell.trans (s0RightFacing_sep5 (2^a-1))

  have hblocks : d1BlocksOn V (1+4+(m:Int)+2) n := by
    intro i hi
    refine ⟨?_,?_,?_⟩
    · have hcoord : 1+4+(m:Int)+2+3*(i:Int) =
          H+1+(6+3*i:Int) := by dsimp [H]; omega
      rw [hcoord,hVafter (H+1+(6+3*(i:Int))) (by omega)]
      have hcell := hSright (6+3*i)
      rw [show H+1+(6+3*(i:Int))=H+1+(6+3*i:Int) by norm_num] at hcell
      rw [hcell,s0RightFacing_after_six (2^a-1) (6+3*i) (by omega)]
      have hval := sideBit_d1pow_true (2^a) (3*i) (by omega)
      simpa [show (2^a-1)+1=2^a by omega] using hval
    · have hcoord : 1+4+(m:Int)+2+3*(i:Int)+1 =
          H+1+(6+3*i+1:Int) := by dsimp [H]; omega
      rw [hcoord,hVafter (H+1+(6+3*i+1:Int)) (by omega)]
      have hcell := hSright (6+3*i+1)
      rw [hcell,s0RightFacing_after_six (2^a-1) (6+3*i+1) (by omega)]
      have hval := sideBit_d1pow_true (2^a) (3*i+1) (by omega)
      simpa [show (2^a-1)+1=2^a by omega] using hval
    · have hcoord : 1+4+(m:Int)+2+3*(i:Int)+2 =
          H+1+(6+3*i+2:Int) := by dsimp [H]; omega
      rw [hcoord,hVafter (H+1+(6+3*i+2:Int)) (by omega)]
      have hcell := hSright (6+3*i+2)
      rw [hcell,s0RightFacing_after_six (2^a-1) (6+3*i+2) (by omega)]
      have hval := sideBit_d1pow_true (2^a) (3*i+2) (by omega)
      simpa [show (2^a-1)+1=2^a by omega] using hval

  have hzeros : ∀ i : Nat, i≤4 →
      V (1+4+(m:Int)+2+3*(n:Int)+(i:Int)) = false := by
    intro i hi
    have hcoord :
        1+4+(m:Int)+2+3*(n:Int)+(i:Int) =
          H+1+(6+3*n+i:Int) := by dsimp [H]; omega
    rw [hcoord,hVafter (H+1+(6+3*n+i:Int)) (by omega)]
    have hcell := hSright (6+3*n+i)
    rw [hcell,s0RightFacing_after_six (2^a-1) (6+3*n+i) (by omega)]
    have hval :
        sideBit (d1pow (2^a)) (3*n+i) = false := by
      apply sideBit_false_of_ge_length
      rw [d1pow_length]
      omega
    simpa [show (2^a-1)+1=2^a by omega] using hval

  have hn : 2≤n := by
    dsimp [n,a]
    have hzpow : 1≤z := hz
    have hpow : 2≤2^z := by
      have := Nat.pow_le_pow_right (by decide : 0<2) hzpow
      simpa using this
    omega

  have hcycle0 := positiveZFirstCycle_from_checkpoint z w q hz hq
  have hcycle :
      run tm2 C1 ⟨4,1,firstCycleCheckpointTape z w q⟩ =
        some ⟨4,1,V⟩ := by
    have hframe :
        frameAt U 3 firstCyclePostludeInside firstCyclePostludeEnd =
          (⟨4,1,V⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,firstCyclePostludeEnd]
      · simp [frameAt_head,firstCyclePostludeEnd] <;> omega
      · rfl
    simpa [C1,U,S,V,tail,a,m,k,H] using
      hcycle0.trans (congrArg some hframe)

  have hsecond := secondCyclePrefix_from_checkpoint
    m n V 1 hinput34 hfirst hsep0 hsep1 hblocks hzeros hn

  calc
    run tm2 (C1+C2) ⟨4,1,firstCycleCheckpointTape z w q⟩ =
        (run tm2 C1 ⟨4,1,firstCycleCheckpointTape z w q⟩).bind
          (fun c => run tm2 C2 c) := by
            rw [run_append]
    _ = run tm2 C2 ⟨4,1,V⟩ := by rw [hcycle]
    _ = some (frameAt T3 g q4TailInside q4TailEnd) := by
          simpa [C2,T1,h1,T2,h2,T3,g] using hsecond

#print axioms positiveZFirstCycle_then_secondCyclePrefix

end BB6Coverage.Agent24PositiveZSecondPrefix
