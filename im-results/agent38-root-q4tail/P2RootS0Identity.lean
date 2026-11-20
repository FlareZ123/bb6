import TM63RootQ4Tail
import Q4TailToNextQ4Tail
import Lean.Elab.Tactic.Omega

/-!
# Authentic second-q4-tail to S0 interface and one further q4Tail cycle

The generic q4Tail-to-S0 adapter is already isolated in Agent 42's
Q4TailToS0Frame.lean.  This file supplies its three source-side ray
conditions for the authentic positive-z second-cycle construction.

The key residual is
  1^(m+2) ++ 0100 ++ 100111 ++ (tail0.drop 6),
where tail0 = 1111 ++ binDec w q ++ lh.
The 34-step frameAt semantics are used pointwise: unmarked cells in its
window are blank, not preserved.  The proof below is source-only until
the complete import closure is compiled and axiom-audited.
-/

namespace BB6Coverage.Agent38RootQ4TailS0

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent48PositiveZFirstCycle
open BB6Coverage.Agent48PositiveZSecondCyclePrefix
open BB6Coverage.Agent42PositiveZFirstCycleS0Input
open BB6Coverage.Agent42Q4S0Drain
open BB6Coverage.Agent42Q4TailToS0Frame
open BB6Coverage.Agent42Q4TailToNextQ4Tail
open BB6Coverage.Agent44P2Postlude
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent48RootSecondQ4Frame
open BB6Coverage.Agent38RootQ4Tail

set_option maxHeartbeats 5000000

/-- The authentic tail after the fixed six-cell P2 boundary. -/
def q4TailS0Tail (w q : Nat) : List Bool :=
  [true,false,false,true,true,true] ++
    (List.replicate 4 true ++ binDec w q ++ lh).drop 6

/-- The tape immediately after the two-zero setup preceding the second
state-1 block scan. -/
def q4TailS0InputTape (z w q : Nat) : Int → Bool :=
  let a := 2^z-1
  let m := 3*2^z+3*z+7
  let tail0 := List.replicate 4 true ++ binDec w q ++ lh
  let S := firstCycleS0DrainOutput z tail0
  let k := 3*a+(3*z+7)
  let U := sweptLeft k S.tape (m:Int)
  let V := (frameAt U 3 firstCyclePostludeInside
    firstCyclePostludeEnd).tape
  let T1 := (frameAt V 1 secondCyclePrefix34Inside
    secondCyclePrefix34End).tape
  afterFirstCycleTwoZero T1 (m+5)

/-- The q4Tail frame from the authentic second-cycle construction. -/
def q4TailS0Frame (z w q : Nat) : Config :=
  let a := 2^z-1
  let n := 2^a
  let m := 3*2^z+3*z+7
  let h : Int := m+7
  frameAt (d0Sweep n (q4TailS0InputTape z w q) h)
    (h+3*(n:Int)) q4TailInside q4TailEnd

/-- The next q4Tail frame obtained by the generic S0 postlude and first
positive-z prefix. -/
def q4TailS0NextFrame (z w q : Nat) : Config :=
  let a := 2^z-1
  let n := 2^a
  let m := 3*2^z+3*z+7
  let H := m+2+3*n
  let tail := q4TailS0Tail w q
  let P := p2PostludeFrame m n tail
  let T1 := (frameAt P.tape 1
    firstCyclePrefix22Inside firstCyclePrefix22End).tape
  let h1 : Int := 1+4+(H:Int)
  let T2 := afterFirstCycleTwoZero T1 h1
  let h2 : Int := h1+2
  let nNext := 2^(n-1)
  let T3 := d0Sweep nNext T2 h2
  let g : Int := h2+3*(nNext:Int)
  frameAt T3 g q4TailInside q4TailEnd

/-- Exact cost of one generic q4Tail-to-q4Tail recurrence after the
authentic second-cycle residual has been identified. -/
def q4TailS0NextCost (z : Nat) : Nat :=
  let a := 2^z-1
  let n := 2^a
  let m := 3*2^z+3*z+7
  let H := m+2+3*n
  let nNext := 2^(n-1)
  (6*4^(n-1)+42*2^(n-1)-12*(n-1)-48) +
    (3*H-5) + (22+H+2+3*nNext+29)

private theorem sideBit_replicate_true_local
    (n i : Nat) (hi : i<n) :
    sideBit (List.replicate n true) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [sideBit]
      | succ i =>
          have hi' : i<n := by omega
          simpa [sideBit] using ih i hi'

private theorem sideBit_false_ge_length_local
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

private theorem sideBit_drop_local
    (xs : List Bool) (k i : Nat) :
    sideBit (xs.drop k) i = sideBit xs (k+i) := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
      cases xs with
      | nil => simp [sideBit]
      | cons b xs =>
          simpa [List.drop,sideBit] using ih xs

private theorem p2ResidualLeft_ones_local
    (m : Nat) (tail : List Bool) (i : Nat) (hi : i<m+2) :
    sideBit (p2ResidualLeft m tail) i = true := by
  unfold p2ResidualLeft
  rw [Agent6Q4Prefix.sideBit_append_left
    (List.replicate (m+2) true)
    ([false,true,false,false] ++ tail) i (by simp)]
  exact sideBit_replicate_true_local (m+2) i hi

private theorem p2ResidualLeft_boundary_local
    (m : Nat) (tail : List Bool) (j : Nat) (hj : j<4) :
    sideBit (p2ResidualLeft m tail) (m+2+j) =
      sideBit [false,true,false,false] j := by
  unfold p2ResidualLeft
  rw [Agent6Q4Prefix.sideBit_append_right
    (List.replicate (m+2) true)
    ([false,true,false,false] ++ tail) (m+2+j) (by simp; omega)]
  have hidx : m+2+j-(m+2)=j := by omega
  rw [hidx]
  exact Agent6Q4Prefix.sideBit_append_left
    [false,true,false,false] tail j (by simpa using hj)

private theorem p2ResidualLeft_tail_local
    (m : Nat) (tail : List Bool) (j : Nat) :
    sideBit (p2ResidualLeft m tail) (m+6+j) =
      sideBit tail j := by
  unfold p2ResidualLeft
  rw [Agent6Q4Prefix.sideBit_append_right
    (List.replicate (m+2) true)
    ([false,true,false,false] ++ tail) (m+6+j) (by simp; omega)]
  have hidx : m+6+j-(m+2)=4+j := by omega
  rw [hidx]
  rw [Agent6Q4Prefix.sideBit_append_right
    ([false,true,false,false] : List Bool) tail (4+j)
    (by simp; omega)]
  have hidx' : 4+j-4=j := by omega
  rw [hidx']

/-- The state-3 and state-1 versions of the same left sweep are
pointwise identical. -/
private theorem s0LeftSweep_eq_sweptLeft_local
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

/-- All three source-side obligations of Agent 42's generic q4Tail
adapter, plus the authentic 100 tail guard. -/
theorem q4TailS0SourceGuards
    (z w q : Nat) (hz : 1≤z) :
    let a : Nat := 2^z-1
    let n : Nat := 2^a
    let m : Nat := 3*2^z+3*z+7
    let h : Int := m+7
    let tail := q4TailS0Tail w q
    let T := q4TailS0InputTape z w q
    T (h-1) = true ∧
    (∀ i : Nat, T (h-2-(i:Int)) =
      sideBit (p2ResidualLeft m tail) i) ∧
    (∀ i : Nat, T (h+(3*n:Int)+5+(i:Int)) = false) ∧
    sideBit tail 0 = true ∧
    sideBit tail 1 = false ∧
    sideBit tail 2 = false := by
  dsimp
  let a : Nat := 2^z-1
  let n : Nat := 2^a
  let m : Nat := 3*2^z+3*z+7
  let tail0 : List Bool := List.replicate 4 true ++ binDec w q ++ lh
  let tail : List Bool := q4TailS0Tail w q
  let ell : List Bool := p2ResidualLeft m tail
  let S : Config := firstCycleS0DrainOutput z tail0
  let k : Nat := 3*a+(3*z+7)
  let U : Int → Bool := sweptLeft k S.tape (m:Int)
  let V : Int → Bool :=
    (frameAt U 3 firstCyclePostludeInside firstCyclePostludeEnd).tape
  let T1 : Int → Bool :=
    (frameAt V 1 secondCyclePrefix34Inside secondCyclePrefix34End).tape
  let h1 : Int := m+5
  let T2 : Int → Bool := afterFirstCycleTwoZero T1 h1
  let h : Int := m+7

  have hpow : 2 ≤ 2^z := by
    have hp := Nat.pow_le_pow_right (by decide : 0<2) hz
    simpa using hp
  have ha : 1≤a := by dsimp [a]; omega
  have hn : 2≤n := by
    have hp := Nat.pow_le_pow_right (by decide : 0<2) ha
    simpa [n] using hp
  have hm : 16≤m := by dsimp [m]; omega
  have hkpos : 0<k := by dsimp [k,a]; omega
  have hcenter : (m:Int)-(k:Int)=3 := by
    dsimp [m,k,a]
    omega

  have hleftFacing :
      s0LeftFacing (firstCycleResidualLeft z tail0) a 0 =
        d1pow a ++ firstCycleResidualLeft z tail0 := by
    simp [s0LeftFacing,binDec_zero]

  have hSleft (i : Nat) :
      S.tape ((m:Int)-(i:Int)) =
        sideBit (d1pow a ++ firstCycleResidualLeft z tail0) i := by
    have hc := s0Config_left_cell
      (firstCycleResidualLeft z tail0) a 0 (2^a-1) (m:Int) i
    rw [hleftFacing] at hc
    simpa [S,firstCycleS0DrainOutput,m,a] using hc

  have hSright (i : Nat) :
      S.tape ((m:Int)+1+(i:Int)) =
        sideBit (s0RightFacing (2^a-1)) i := by
    have hc := s0Config_right_cell
      (firstCycleResidualLeft z tail0) a 0 (2^a-1) (m:Int) i
    simpa [S,firstCycleS0DrainOutput,m,a] using hc

  have hSrightOne (i : Nat)
      (hi : i=1 ∨ i=2 ∨ i=3) :
      S.tape ((m:Int)+1+(i:Int)) = true := by
    have hc := hSright i
    have hb : sideBit (s0RightFacing (2^a-1)) i = true := by
      rcases hi with h0|h1|h2 <;> subst i <;>
        simp [s0RightFacing,sideBit]
    exact hc.trans hb

  have hshift0 := s0LeftSweep_shift k S.tape (m:Int) hkpos
  have hshift : ∀ x : Int,
      U x =
        (if x=4 then false
         else if 5≤x ∧ x≤(m:Int)+1 then true
         else S.tape x) := by
    intro x
    have hc := hshift0 x
    simpa [U,s0LeftSweep_eq_sweptLeft_local,hcenter] using hc

  have hVrightOnes : ∀ j : Nat, j<m →
      V (5+(j:Int)) = true := by
    intro j hj
    let x : Int := 5+(j:Int)
    have hx : 5≤x := by dsimp [x]; omega
    have hVx : V x = U x := by
      rw [frameAt_tape]
      have hnot : firstCyclePostludeInside (x-3)=false := by
        simp [firstCyclePostludeInside]
        omega
      simp [hnot]
    by_cases hmid : x≤(m:Int)+1
    · have hneq : x≠4 := by omega
      have hcond : 5≤x ∧ x≤(m:Int)+1 := ⟨hx,hmid⟩
      rw [hVx,hshift x]
      simp [hneq,hcond]
    · have hxupper : x≤(m:Int)+4 := by dsimp [x]; omega
      have hcases :
          x=(m:Int)+2 ∨ x=(m:Int)+3 ∨ x=(m:Int)+4 := by omega
      rcases hcases with h2|h3|h4
      · rw [h2]
        have hu : U ((m:Int)+2) = S.tape ((m:Int)+2) := by
          rw [hshift]
          have hneq : (m:Int)+2≠4 := by omega
          have hnot : ¬(5≤(m:Int)+2 ∧ (m:Int)+2≤(m:Int)+1) := by omega
          simp [hneq,hnot]
        calc
          V ((m:Int)+2) = U ((m:Int)+2) := hVx
          _ = S.tape ((m:Int)+2) := hu
          _ = true := hSrightOne 1 (by omega)
      · rw [h3]
        have hu : U ((m:Int)+3) = S.tape ((m:Int)+3) := by
          rw [hshift]
          have hneq : (m:Int)+3≠4 := by omega
          have hnot : ¬(5≤(m:Int)+3 ∧ (m:Int)+3≤(m:Int)+1) := by omega
          simp [hneq,hnot]
        calc
          V ((m:Int)+3) = U ((m:Int)+3) := hVx
          _ = S.tape ((m:Int)+3) := hu
          _ = true := hSrightOne 2 (by omega)
      · rw [h4]
        have hu : U ((m:Int)+4) = S.tape ((m:Int)+4) := by
          rw [hshift]
          have hneq : (m:Int)+4≠4 := by omega
          have hnot : ¬(5≤(m:Int)+4 ∧ (m:Int)+4≤(m:Int)+1) := by omega
          simp [hneq,hnot]
        calc
          V ((m:Int)+4) = U ((m:Int)+4) := hVx
          _ = S.tape ((m:Int)+4) := hu
          _ = true := hSrightOne 3 (by omega)

  have hT1outside (x : Int) (hx : 5≤x) : T1 x = V x := by
    rw [frameAt_tape]
    have hnot : secondCyclePrefix34Inside (x-1)=false := by
      simp [secondCyclePrefix34Inside]
      omega
    simp [hnot]

  have hT1leftOutside (x : Int) (hx : x≤-7) : T1 x = V x := by
    rw [frameAt_tape]
    have hnot : secondCyclePrefix34Inside (x-1)=false := by
      simp [secondCyclePrefix34Inside]
      omega
    simp [hnot]

  have hVleftOutside (x : Int) (hx : x≤-7) : V x = U x := by
    rw [frameAt_tape]
    have hnot : firstCyclePostludeInside (x-3)=false := by
      simp [firstCyclePostludeInside]
      omega
    simp [hnot]

  have hT2outside (x : Int) (hx0 : x≠h1) (hx1 : x≠h1+1) :
      T2 x = T1 x := by
    simp [T2,afterFirstCycleTwoZero,hx0,hx1]

  have hT1_4 : T1 4 = true := by
    simp [T1,frameAt_tape,secondCyclePrefix34Inside,
      secondCyclePrefix34End]

  have hT1boundary (j : Nat) (hj : j<4) :
      T1 (3-(j:Int)) = sideBit [false,true,false,false] j := by
    have hcases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hcases with h0|h1|h2|h3 <;> subst j <;>
      simp [T1,frameAt_tape,secondCyclePrefix34Inside,
        secondCyclePrefix34End,sideBit]

  have hT1tail (j : Nat) (hj : j<6) :
      T1 (-1-(j:Int)) =
        sideBit [true,false,false,true,true,true] j := by
    have hcases :
        j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
    rcases hcases with h0|h1|h2|h3|h4|h5 <;> subst j <;>
      simp [T1,frameAt_tape,secondCyclePrefix34Inside,
        secondCyclePrefix34End,sideBit]

  have hT2left (j : Nat) :
      T2 (-7-(j:Int)) = S.tape (-7-(j:Int)) := by
    let x : Int := -7-(j:Int)
    have htwo : T2 x = T1 x :=
      hT2outside x (by dsimp [x,h1]; omega)
        (by dsimp [x,h1]; omega)
    have hframe2 : T1 x = V x := hT1leftOutside x (by dsimp [x]; omega)
    have hframe1 : V x = U x := hVleftOutside x (by dsimp [x]; omega)
    have hsweep : U x = S.tape x := by
      rw [hshift x]
      have hneq : x≠4 := by dsimp [x]; omega
      have hnot : ¬(5≤x ∧ x≤(m:Int)+1) := by dsimp [x]; omega
      simp [hneq,hnot]
    calc
      T2 (-7-(j:Int)) = T2 x := by rfl
      _ = T1 x := htwo
      _ = V x := hframe2
      _ = U x := hframe1
      _ = S.tape x := hsweep

  have hSreduce (j : Nat) :
      sideBit (d1pow a ++ firstCycleResidualLeft z tail0)
        (m+7+j) = sideBit tail0 (6+j) := by
    rw [Agent6Q4Prefix.sideBit_append_right
      (d1pow a) (firstCycleResidualLeft z tail0) (m+7+j)
      (by rw [d1pow_length]; dsimp [m,a]; omega)]
    rw [d1pow_length]
    have hidx1 : m+7+j-3*a=3*z+17+j := by
      dsimp [m,a]
      omega
    rw [hidx1]
    unfold firstCycleResidualLeft
    rw [Agent6Q4Prefix.sideBit_append_right
      (List.replicate (3*z+7) true)
      ([false,true,false,false] ++ tail0) (3*z+17+j)
      (by simp; omega)]
    have hidx2 :
        3*z+17+j-(List.replicate (3*z+7) true).length=10+j := by
      simp
      omega
    rw [hidx2]
    rw [Agent6Q4Prefix.sideBit_append_right
      ([false,true,false,false] : List Bool) tail0 (10+j)
      (by simp; omega)]
    have hidx3 : 10+j-4=6+j := by omega
    rw [hidx3]

  have htailEq (j : Nat) :
      sideBit tail (6+j) = sideBit tail0 (6+j) := by
    unfold tail q4TailS0Tail
    rw [Agent6Q4Prefix.sideBit_append_right
      [true,false,false,true,true,true] (tail0.drop 6) (6+j)
      (by simp)]
    have hidx : 6+j-[true,false,false,true,true,true].length=j := by
      simp
    rw [hidx,sideBit_drop_local]

  have hleft : T2 (h-1)=true := by
    have hc : h-1=h1+1 := by dsimp [h,h1]; omega
    rw [hc]
    simp [T2,afterFirstCycleTwoZero]

  have hres : ∀ i : Nat,
      T2 (h-2-(i:Int)) = sideBit ell i := by
    intro i
    by_cases hi0 : i=0
    · subst i
      have hc : h-2=h1 := by dsimp [h,h1]; omega
      rw [hc]
      have hT : T2 h1=true := by simp [T2,afterFirstCycleTwoZero]
      have hs : sideBit ell 0=true :=
        p2ResidualLeft_ones_local m tail 0 (by omega)
      exact hT.trans hs.symm
    · by_cases hlead : i<m+2
      · let x : Int := h-2-(i:Int)
        have hxupper : x≤(m:Int)+4 := by dsimp [x,h]; omega
        have hxcases : x=4 ∨ 5≤x := by dsimp [x,h]; omega
        rcases hxcases with hx4|hx5
        · have hT2x : T2 x=T1 x :=
            hT2outside x (by dsimp [x,h1]; omega)
              (by dsimp [x,h1]; omega)
          have hT1x : T1 x=true := by rw [hx4]; exact hT1_4
          have hT : T2 x=true := hT2x.trans hT1x
          have hs : sideBit ell i=true :=
            p2ResidualLeft_ones_local m tail i (by omega)
          simpa [x] using hT.trans hs.symm
        · let j : Nat := m-i
          have hj : j<m := by dsimp [j]; omega
          have hcoord : x=5+(j:Int) := by dsimp [x,j,h]; omega
          have hT2x : T2 x=T1 x :=
            hT2outside x (by dsimp [x,h1]; omega)
              (by dsimp [x,h1]; omega)
          have hT1x : T1 x=V x := hT1outside x hx5
          have hVx : V x=V (5+(j:Int)) := by rw [hcoord]
          have hVtrue := hVrightOnes j hj
          have hT : T2 x=true := by
            calc
              T2 x = T1 x := hT2x
              _ = V x := hT1x
              _ = V (5+(j:Int)) := hVx
              _ = true := hVtrue
          have hs : sideBit ell i=true :=
            p2ResidualLeft_ones_local m tail i (by omega)
          simpa [x] using hT.trans hs.symm
      · by_cases hboundary : i<m+6
        · let j : Nat := i-(m+2)
          have hj : j<4 := by dsimp [j]; omega
          have hi : i=m+2+j := by dsimp [j]; omega
          let x : Int := 3-(j:Int)
          have hcoord : h-2-(i:Int)=x := by
            rw [hi]
            dsimp [h,x]
            omega
          have hT2x : T2 x=T1 x :=
            hT2outside x (by dsimp [x,h1]; omega)
              (by dsimp [x,h1]; omega)
          have hT1x := hT1boundary j hj
          have hs := p2ResidualLeft_boundary_local m tail j hj
          calc
            T2 (h-2-(i:Int)) = T2 x := by rw [hcoord]
            _ = T1 x := hT2x
            _ = sideBit [false,true,false,false] j := hT1x
            _ = sideBit ell i := by
              rw [hi]
              exact hs.symm
        · by_cases htail : i<m+12
          · let j : Nat := i-(m+6)
            have hj : j<6 := by dsimp [j]; omega
            have hi : i=m+6+j := by dsimp [j]; omega
            let x : Int := -1-(j:Int)
            have hcoord : h-2-(i:Int)=x := by
              rw [hi]
              dsimp [h,x]
              omega
            have hT2x : T2 x=T1 x :=
              hT2outside x (by dsimp [x,h1]; omega)
                (by dsimp [x,h1]; omega)
            have hT1x := hT1tail j hj
            have hprefix : sideBit tail j =
                sideBit [true,false,false,true,true,true] j := by
              have hcases :
                  j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
              rcases hcases with h0|h1|h2|h3|h4|h5 <;>
                subst j <;> simp [tail,q4TailS0Tail,sideBit]
            have hs := p2ResidualLeft_tail_local m tail j
            calc
              T2 (h-2-(i:Int)) = T2 x := by rw [hcoord]
              _ = T1 x := hT2x
              _ = sideBit [true,false,false,true,true,true] j := hT1x
              _ = sideBit tail j := hprefix.symm
              _ = sideBit ell i := by
                rw [hi]
                exact hs.symm
          · let j : Nat := i-(m+12)
            have hi : i=m+12+j := by dsimp [j]; omega
            let x : Int := -7-(j:Int)
            have hcoord : h-2-(i:Int)=x := by
              rw [hi]
              dsimp [h,x]
              omega
            have hT2x : T2 x=S.tape x := hT2left j
            have hSx : S.tape x =
                sideBit (d1pow a ++ firstCycleResidualLeft z tail0)
                  (m+7+j) := by
              have hc := hSleft (m+7+j)
              have hcoordS :
                  (m:Int)-((m+7+j:Int)) = x := by
                dsimp [x]
                omega
              rw [hcoordS] at hc
              exact hc
            have hreduce := hSreduce j
            have htail := htailEq j
            have hs := p2ResidualLeft_tail_local m tail (6+j)
            calc
              T2 (h-2-(i:Int)) = T2 x := by rw [hcoord]
              _ = S.tape x := hT2x
              _ = sideBit (d1pow a ++ firstCycleResidualLeft z tail0)
                    (m+7+j) := hSx
              _ = sideBit tail0 (6+j) := hreduce
              _ = sideBit tail (6+j) := htail.symm
              _ = sideBit ell (m+6+(6+j)) := hs.symm
              _ = sideBit ell i := by rw [hi]; congr 1 <;> omega

  have hT2right (x : Int)
      (hx : (m:Int)+12+3*(n:Int)≤x) :
      T2 x=S.tape x := by
    have htwo : T2 x=T1 x :=
      hT2outside x (by dsimp [h1]; omega)
        (by dsimp [h1]; omega)
    have hframe2 : T1 x=V x := hT1outside x (by omega)
    have hframe1 : V x=U x := by
      rw [frameAt_tape]
      have hnot : firstCyclePostludeInside (x-3)=false := by
        simp [firstCyclePostludeInside]
        omega
      simp [hnot]
    have hsweep : U x=S.tape x := by
      rw [hshift x]
      have hneq : x≠4 := by omega
      have hnot : ¬(5≤x ∧ x≤(m:Int)+1) := by omega
      simp [hneq,hnot]
    exact htwo.trans (hframe2.trans (hframe1.trans hsweep))

  have hright : ∀ i : Nat,
      T2 (h+(3*n:Int)+5+(i:Int))=false := by
    intro i
    let x : Int := h+(3*n:Int)+5+(i:Int)
    have hx : (m:Int)+12+3*(n:Int)+(i:Int)=x := by
      dsimp [x,h]
      omega
    have hsource := hT2right x (by rw [hx]; omega)
    have hcell := hSright (3*n+11+i)
    have hcoord :
        (m:Int)+1+((3*n+11+i:Int))=x := by
      rw [hx]
      dsimp [x]
      omega
    rw [hcoord] at hcell
    have hlen :
        (s0RightFacing (2^a-1)).length=6+3*n := by
      simp [s0RightFacing,d1pow_length]
      dsimp [n]
      omega
    have hbit :
        sideBit (s0RightFacing (2^a-1)) (3*n+11+i)=false := by
      apply sideBit_false_ge_length_local
      rw [hlen]
      omega
    exact hsource.trans (hcell.trans hbit)

  have ht0 : sideBit tail 0=true := by
    simp [tail,q4TailS0Tail,sideBit]
  have ht1 : sideBit tail 1=false := by
    simp [tail,q4TailS0Tail,sideBit]
  have ht2 : sideBit tail 2=false := by
    simp [tail,q4TailS0Tail,sideBit]

  exact ⟨hleft,hres,hright,ht0,ht1,ht2⟩

/-- The authentic second q4Tail frame is exactly the S0 encoder input
required by Agent 42's generic q4Tail adapter. -/
theorem q4TailS0Frame_eq_s0Config
    (z w q : Nat) (hz : 1≤z) :
    q4TailS0Frame z w q =
      let a : Nat := 2^z-1
      let n : Nat := 2^a
      let m : Nat := 3*2^z+3*z+7
      s0Config (p2ResidualLeft m (q4TailS0Tail w q))
        (n-1) (2^(n-1)-1) 0 (m+2+3*n) := by
  let a : Nat := 2^z-1
  let n : Nat := 2^a
  let m : Nat := 3*2^z+3*z+7
  let h : Int := m+7
  let tail := q4TailS0Tail w q
  let ell := p2ResidualLeft m tail
  let T := q4TailS0InputTape z w q
  have hg := q4TailS0SourceGuards z w q hz
  have hn : 2≤n := by
    have hp := Nat.pow_le_pow_right (by decide : 0<2)
      (show 1≤a by dsimp [a]; omega)
    simpa [n] using hp
  have hhead : h=(m:Int)+7 := by rfl
  have hframe := q4Tail_frame_eq_s0Config
    n ell T h hn hg.1 hg.2.1 hg.2.2.1
  have hcoord : h+(3*n:Int)-5=(m+2+3*n:Int) := by
    dsimp [h]
    omega
  simpa [q4TailS0Frame,q4TailS0InputTape,a,n,m,h,T,tail,ell,
    hcoord] using hframe

/-- The authentic blank-root q4Tail frame is the generic source frame
with the root's exact positive-z parameters. -/
theorem tm63_root_second_q4Tail_eq_s0Config :
    rootSecondQ4TailFrame =
      q4TailS0Frame rootMarker1Z
        (firstQ4P1Width tm63Length1 rootMarker1A)
        (firstQ4P1Value tm63Length1 rootMarker1A) := by
  rfl

/-- One full source-level q4Tail-to-q4Tail recurrence from the authentic
second q4Tail frame. -/
theorem q4TailS0Frame_to_nextQ4Tail
    (z w q : Nat) (hz : 1≤z) :
    run tm2 (q4TailS0NextCost z) (q4TailS0Frame z w q) =
      some (q4TailS0NextFrame z w q) := by
  let a : Nat := 2^z-1
  let n : Nat := 2^a
  let m : Nat := 3*2^z+3*z+7
  let h : Int := m+7
  let tail := q4TailS0Tail w q
  let T := q4TailS0InputTape z w q
  have hg := q4TailS0SourceGuards z w q hz
  have hn : 2≤n := by
    have hp := Nat.pow_le_pow_right (by decide : 0<2)
      (show 1≤a by dsimp [a]; omega)
    simpa [n] using hp
  have hhead : h=(m:Int)+7 := by rfl
  have hstep := q4Tail_to_next_q4Tail m n tail T h
    hn hg.1 hg.2.1 hg.2.2.1 hhead
    hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2
  simpa [q4TailS0NextCost,q4TailS0Frame,q4TailS0NextFrame,
    q4TailS0InputTape,a,n,m,h,tail,T] using hstep

/-- The authentic blank-root TM63 trajectory reaches one further q4Tail
frame after the generic S0 drain/postlude and next prefix. -/
theorem tm63_blank_reaches_next_q4Tail :
    let w := firstQ4P1Width tm63Length1 rootMarker1A
    let q := firstQ4P1Value tm63Length1 rootMarker1A
    run tm2
      (rootToSecondQ4Cost + rootSecondQ4TailPrefixCost +
        q4TailS0NextCost rootMarker1Z) blank =
      some (shiftConfig rootMarker1Head
        (q4TailS0NextFrame rootMarker1Z w q)) := by
  let w := firstQ4P1Width tm63Length1 rootMarker1A
  let q := firstQ4P1Value tm63Length1 rootMarker1A
  have hz : 1≤rootMarker1Z :=
    le_trans (by decide) rootMarker1Z_ge_three
  have hroot := tm63_blank_reaches_second_q4_tail
  have hframe := tm63_root_second_q4Tail_eq_s0Config
  have hstep := q4TailS0Frame_to_nextQ4Tail rootMarker1Z w q hz
  have hstepRoot :
      run tm2 (q4TailS0NextCost rootMarker1Z) rootSecondQ4TailFrame =
        some (q4TailS0NextFrame rootMarker1Z w q) := by
    simpa [w,q,← hframe] using hstep
  have hstepShift :
      run tm2 (q4TailS0NextCost rootMarker1Z)
        (shiftConfig rootMarker1Head rootSecondQ4TailFrame) =
      some (shiftConfig rootMarker1Head
        (q4TailS0NextFrame rootMarker1Z w q)) := by
    calc
      run tm2 (q4TailS0NextCost rootMarker1Z)
          (shiftConfig rootMarker1Head rootSecondQ4TailFrame) =
        (run tm2 (q4TailS0NextCost rootMarker1Z)
          rootSecondQ4TailFrame).map (shiftConfig rootMarker1Head) := by
            exact shift_run rootMarker1Head tm2 rootSecondQ4TailFrame
              (q4TailS0NextCost rootMarker1Z)
      _ = some (shiftConfig rootMarker1Head
          (q4TailS0NextFrame rootMarker1Z w q)) := by
            rw [hstepRoot]
  have htotal :
      rootToSecondQ4Cost + rootSecondQ4TailPrefixCost +
        q4TailS0NextCost rootMarker1Z =
      (rootToSecondQ4Cost + rootSecondQ4TailPrefixCost) +
        q4TailS0NextCost rootMarker1Z := by omega
  rw [htotal,run_append]
  rw [hroot]
  simp only [Option.bind_some]
  exact hstepShift

#print axioms q4TailS0SourceGuards
#print axioms q4TailS0Frame_eq_s0Config
#print axioms q4TailS0Frame_to_nextQ4Tail
#print axioms tm63_blank_reaches_next_q4Tail

end BB6Coverage.Agent38RootQ4TailS0
