import Q4RightEndpoint
import M1EvenQ4Prefix
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Source composition of the m=1,n=6 even q4 branch

The finite bridge in Agent 48's m=1,n=6 prefix ends four E-on-one
moves into the ordinary q4 suffix.  This module composes the remaining
35+3*b suffix moves, transports an arbitrary left stream through that
suffix, identifies the exact marker-0 S1 endpoint, and then attaches
the already-proved all-ones counted drain.
-/

namespace BB6Coverage.Agent42M1EvenSuffix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6.ChampionTerminal
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent48CountedInc0

private theorem d0pow_length (b : Nat) : (d0pow b).length = 3*b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      simp [d0pow, d0, ih]
      omega

private theorem sideBit_d0pow_mod (b i : Nat) (hi : i < 3*b) :
    sideBit (d0pow b) i = decide (i % 3 = 2) := by
  induction b generalizing i with
  | zero => omega
  | succ b ih =>
      change sideBit (d0 ++ d0pow b) i = decide (i % 3 = 2)
      by_cases hi0 : i < 3
      · have hc : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hc with h0 | h1 | h2
        · subst i
          simp [d0, sideBit]
        · subst i
          simp [d0, sideBit]
        · subst i
          simp [d0, sideBit]
      · have hi3 : 3 ≤ i := by omega
        have hi' : i-3 < 3*b := by omega
        rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
          d0 (d0pow b) i (by simp [d0]; omega)]
        have hm : i % 3 = (i-3) % 3 := by omega
        simpa [d0, hm] using ih (i-3) hi'

private theorem sideBit_drop_one (xs : List Bool) (i : Nat) :
    sideBit (xs.drop 1) i = sideBit xs (i+1) := by
  cases xs with
  | nil => simp [sideBit]
  | cons x xs => simp [sideBit]

private theorem first10_six (T : Int → Bool) (h : Int)
    (i : Nat) (hi : i < 6) :
    (frameAt T h q4First10Inside q4First10End).tape
      (h+(i:Int)) = true := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rw [frameAt_tape]
  have hcoord : (h+(i:Int))-h = (i:Int) := by omega
  rw [hcoord]
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 <;>
    subst i <;>
    simp [q4First10Inside, q4First10End]

/-- Generic left-stream transport through the q4 suffix.  No particular
S1 marker or encoder is assumed: the suffix preserves the input stream
with its consumed head cell removed, after its d0 and six-one prefixes. -/
theorem q4_suffix_left_word_of_stream
    (T : Int → Bool) (h : Int) (b : Nat) (Q : List Bool)
    (hleft : ∀ i : Nat, T (h-(i:Int)) =
      sideBit Q i) :
    ∀ i : Nat,
      (frameAt
        (d0Sweep b
          (frameAt T h q4First10Inside q4First10End).tape
          (h+10))
        (h+10+(3*b:Int)) q4TailInside q4TailEnd).tape
          (h+5+(3*b:Int)-(i:Int)) =
      BB6Coverage.Agent6Q4Prefix.sideBit
        (d0pow b ++ d1pow 2 ++ Q.drop 1) i := by
  intro i
  let T1 := (frameAt T h q4First10Inside q4First10End).tape
  let T2 := d0Sweep b T1 (h+10)
  let g : Int := h+10+(3*b:Int)
  let U := frameAt T2 g q4TailInside q4TailEnd
  let x : Int := h+5+(3*b:Int)-(i:Int)
  have hxFrame : x < g-4 := by
    dsimp [x,g]
    omega
  have hU : U.tape x = T2 x := by
    dsimp [U]
    rw [frameAt_tape]
    have hnot : q4TailInside (x-g) = false := by
      simp [q4TailInside]
      omega
    simp [hnot]
  have hlen0 : (d0pow b).length = 3*b := d0pow_length b
  have hlen1 : (d1pow 2).length = 6 := by
    simp [d1pow, d1]
  let tail := Q.drop 1
  by_cases hi0 : i < 3*b
  · have hside :
        BB6Coverage.Agent6Q4Prefix.sideBit
            (d0pow b ++ d1pow 2 ++ tail) i =
          sideBit (d0pow b) i := by
      rw [List.append_assoc]
      rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_left
        (d0pow b) (d1pow 2 ++ tail) i (by rw [hlen0]; omega)]
    have hcell : T2 x =
        sideBit (d0pow b) i := by
      have hperiod : T2 x = decide (i % 3 = 2) := by
        by_cases hscan : h+10 ≤ x
        · let d : Nat := 3*b-5-i
          have hdi : i ≤ 3*b-5 := by
            dsimp [x] at hscan
            omega
          have hxcoord : x = h+10+(d:Int) := by
            dsimp [x,d]
            omega
          let j : Nat := d/3
          let r : Nat := d%3
          have hdiv : d = 3*j+r := by
            dsimp [j,r,d]
            omega
          have hj : j < b := by
            dsimp [j,d]
            omega
          have hrcases : r=0 ∨ r=1 ∨ r=2 := by
            dsimp [r,d]
            omega
          obtain ⟨hb0,hb1,hb2⟩ :=
            d0Sweep_block b T1 (h+10) j hj
          rcases hrcases with hr0 | hr1 | hr2
          · have hx0 : x = h+10+(3*(j:Int)) := by
              rw [hxcoord]
              have hdEq : d = 3*j := by
                rw [hdiv,hr0]
                omega
              omega
            have hiMod : i%3=1 := by
              dsimp [r,d] at hr0
              omega
            rw [hx0]
            simpa [T2,hiMod] using hb0
          · have hx1 : x = h+10+(3*(j:Int))+1 := by
              rw [hxcoord]
              have hdEq : d = 3*j+1 := by
                rw [hdiv,hr1] <;> omega
              omega
            have hiMod : i%3=0 := by
              dsimp [r,d] at hr1
              omega
            rw [hx1]
            simpa [T2,hiMod] using hb1
          · have hx2 : x = h+10+(3*(j:Int))+2 := by
              rw [hxcoord]
              have hdEq : d = 3*j+2 := by
                rw [hdiv,hr2] <;> omega
              omega
            have hiMod : i%3=2 := by
              dsimp [r,d] at hr2
              omega
            rw [hx2]
            simpa [T2,hiMod] using hb2
        · have hlow : x < h+10 := by omega
          let j : Nat := 3*b-i
          have hjrange : 1 ≤ j ∧ j ≤ 4 := by
            dsimp [j]
            dsimp [x] at hlow
            omega
          let hcells := q4First10_cells T h
          have hcases : j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
          rcases hcases with hj1 | hj2 | hj3 | hj4
          · have hx9 : x=h+9 := by
              dsimp [x,j]
              omega
            have hiMod : i%3=2 := by
              dsimp [j] at hj1
              omega
            have hT1 : T1 (h+9)=true := by
              simpa [T1] using hcells.2.2.2.2
            have hbefore : T2 (h+9)=T1 (h+9) := by
              dsimp [T2]
              exact d0Sweep_before b T1 (h+10) (h+9) (by omega)
            rw [hx9,hbefore,hT1]
            simp [hiMod]
          · have hx8 : x=h+8 := by
              dsimp [x,j]
              omega
            have hiMod : i%3=1 := by
              dsimp [j] at hj2
              omega
            have hT1 : T1 (h+8)=false := by
              simpa [T1] using hcells.2.2.2.1
            have hbefore : T2 (h+8)=T1 (h+8) := by
              dsimp [T2]
              exact d0Sweep_before b T1 (h+10) (h+8) (by omega)
            rw [hx8,hbefore,hT1]
            simp [hiMod]
          · have hx7 : x=h+7 := by
              dsimp [x,j]
              omega
            have hiMod : i%3=0 := by
              dsimp [j] at hj3
              omega
            have hT1 : T1 (h+7)=false := by
              simpa [T1] using hcells.2.2.1
            have hbefore : T2 (h+7)=T1 (h+7) := by
              dsimp [T2]
              exact d0Sweep_before b T1 (h+10) (h+7) (by omega)
            rw [hx7,hbefore,hT1]
            simp [hiMod]
          · have hx6 : x=h+6 := by
              dsimp [x,j]
              omega
            have hiMod : i%3=2 := by
              dsimp [j] at hj4
              omega
            have hT1 : T1 (h+6)=true := by
              simpa [T1] using hcells.2.1
            have hbefore : T2 (h+6)=T1 (h+6) := by
              dsimp [T2]
              exact d0Sweep_before b T1 (h+10) (h+6) (by omega)
            rw [hx6,hbefore,hT1]
            simp [hiMod]
      exact hperiod.trans (sideBit_d0pow_mod b i hi0).symm
    calc
      U.tape x = T2 x := hU
      _ = sideBit (d0pow b) i := hcell
      _ = BB6Coverage.Agent6Q4Prefix.sideBit
            (d0pow b ++ d1pow 2 ++ tail) i := hside.symm
  · by_cases hi1 : i < 3*b+6
    · have hside :
          BB6Coverage.Agent6Q4Prefix.sideBit
            (d0pow b ++ d1pow 2 ++ tail) i = true := by
        rw [List.append_assoc]
        rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
          (d0pow b) (d1pow 2 ++ tail) i (by rw [hlen0]; omega)]
        rw [hlen0]
        rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_left
          (d1pow 2) tail (i-3*b) (by rw [hlen1]; omega)]
        exact BB6Coverage.Agent6Q4Prefix.sideBit_d1pow_true
          2 (i-3*b) (by omega)
      have hcell : T2 x = true := by
        have hbefore : T2 x = T1 x := by
          dsimp [T2]
          exact d0Sweep_before b T1 (h+10) x (by dsimp [x]; omega)
        let j : Nat := i-3*b
        have hj : j<6 := by dsimp [j]; omega
        have hk : 5-j < 6 := by omega
        have hxk : x=h+((5-j:Int)) := by
          dsimp [x,j]
          omega
        have hT1 : T1 x=true := by
          rw [hxk]
          exact first10_six T h (5-j) hk
        exact hbefore.trans hT1
      calc
        U.tape x = T2 x := hU
        _ = true := hcell
        _ = BB6Coverage.Agent6Q4Prefix.sideBit
              (d0pow b ++ d1pow 2 ++ tail) i := hside.symm
    · let j : Nat := i-(3*b+6)
      have hside :
          BB6Coverage.Agent6Q4Prefix.sideBit
            (d0pow b ++ d1pow 2 ++ tail) i =
          sideBit tail j := by
        rw [List.append_assoc]
        rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
          (d0pow b) (d1pow 2 ++ tail) i (by rw [hlen0]; omega)]
        rw [hlen0]
        rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
          (d1pow 2) tail (i-3*b) (by rw [hlen1]; omega)]
        rw [hlen1]
        have hidx : (i-3*b)-6 = j := by
          dsimp [j]
          omega
        rw [hidx]
      have hcell : T2 x = sideBit tail j := by
        have hbefore : T2 x = T1 x := by
          dsimp [T2]
          exact d0Sweep_before b T1 (h+10) x (by dsimp [x]; omega)
        have hfirst : T1 x = T x := by
          dsimp [T1]
          rw [frameAt_tape]
          have hnot : q4First10Inside (x-h) = false := by
            simp [q4First10Inside]
            dsimp [x]
            omega
          simp [hnot]
        have hxcoord : x = h-((j+1:Int)) := by
          dsimp [x,j]
          omega
        have hprefix : T x =
            sideBit Q (j+1) := by
          rw [hxcoord]
          exact hleft (j+1)
        have hdrop := sideBit_drop_one Q j
        calc
          T2 x = T1 x := hbefore
          _ = T x := hfirst
          _ = sideBit Q (j+1) := hprefix
          _ = sideBit tail j := hdrop.symm
      calc
        U.tape x = T2 x := hU
        _ = sideBit tail j := hcell
        _ = BB6Coverage.Agent6Q4Prefix.sideBit
              (d0pow b ++ d1pow 2 ++ tail) i := hside.symm

/-- The source cut retains the infinite blank right ray required by the
q4 suffix's complete right-facing endpoint theorem. -/
theorem m1Even_q4_prefix_far_tail (a b : Nat) (h : Int) :
    ∀ i : Nat, 9+3*b ≤ i →
      m1EvenQ4CutTape a b h (h+1+(i:Int)) = false := by
  intro i hi
  let T := (s1Config 3 6 1 a 0 b h).tape
  let N : Nat := 3*a+1
  let x : Int := h+1+(i:Int)
  have hout : m1EvenQ4Inside (x-(h-(N:Int))) = false := by
    simp [m1EvenQ4Inside,x,N]
    omega
  have hcut :
      m1EvenQ4CutTape a b h x = sweptLeft N T h x := by
    simp [m1EvenQ4CutTape,T,N]
    rw [frameAt_tape]
    simp [hout]
  have hpres : sweptLeft N T h x = T x := by
    exact sweptLeft_preserves_right N T h x (by dsimp [x]; omega)
  have hsrc : T x =
      sideBit (s1PhysicalRight b) i := by
    have hcell := s1Config_right_cell 3 6 1 a 0 b h i
    simpa [T,x] using hcell
  have hlen : (s1PhysicalRight b).length = 9+3*b := by
    simp [s1PhysicalRight,s0PhysicalRight,d1pow_length]
    omega
  have hblank :
      sideBit (s1PhysicalRight b) i = false :=
    BB6Coverage.Agent6Q4Prefix.sideBit_ge_length
      (s1PhysicalRight b) i (by omega)
  exact hcut.trans (hpres.trans (hsrc.trans hblank))

/-- Identify Agent 48's complete reset-prefix frame with the exact
marker-0 S1 successor. -/
theorem m1Even_q4_reset_prefix_source (a b : Nat) (h : Int) :
    run tm2 (resetPrefixCost 1 6 a b)
      (s1Config 3 6 1 a 0 b h) =
      some (s1Config 3 5 0 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  let T := m1EvenQ4CutTape a b h
  let T1 := (frameAt T h q4First10Inside q4First10End).tape
  let T2 := d0Sweep b T1 (h+10)
  let g : Int := h+10+(3*b:Int)
  let U := frameAt T2 g q4TailInside q4TailEnd
  have hshape6 := m1Even_q4_prefix_rightShape a b h
  have hshape8 : BB6Coverage.Agent8Q4Suffix.q4RightShape T h b := by
    simpa [BB6Coverage.Agent6Q4Prefix.q4RightShape,
      BB6Coverage.Agent8Q4Suffix.q4RightShape] using hshape6
  have hleft := m1Even_q4_prefix_leftFacing a b h
  have htail := m1Even_q4_prefix_far_tail a b h
  have hleftU :
      ∀ i : Nat, U.tape (h+5+(3*b:Int)-(i:Int)) =
        sideBit
          (d0pow b ++ d1pow 2 ++ (m1EvenQ4LeftFacing a).drop 1) i := by
    simpa [U,T1,T2,g] using
      q4_suffix_left_word_of_stream T h b (m1EvenQ4LeftFacing a) hleft
  have hrightU :
      ∀ i : Nat, U.tape (h+6+(3*b:Int)+(i:Int)) =
        sideBit (s0RightFacing 0) i := by
    simpa [U,T1,T2,g] using
      q4_suffix_right_word T h b hshape8 htail
  have hframe := m1Even_reset_prefix_frame a b h
  have hframe' :
      run tm2 (79+12*a+3*b) (s1Config 3 6 1 a 0 b h) = some U := by
    simpa [U,T1,T2,g] using hframe
  let H : Int := h+5+(3*b:Int)
  have htarget : U =
      s1Config 3 5 0 (a+b+2) (2^b-1) 0 H := by
    apply config_ext
    · simp [U,frameAt_state,q4TailEnd]
    · simp [U,frameAt_head,q4TailEnd,g,H] <;> omega
    · funext x
      by_cases hx : x ≤ H
      · let i : Nat := Int.toNat (H-x)
        have hcoord : x = H-(i:Int) := by
          dsimp [i]
          omega
        rw [hcoord]
        have hleftCell :
            U.tape (H-(i:Int)) =
              (s1Config 3 5 0 (a+b+2) (2^b-1) 0 H).tape
                (H-(i:Int)) := by
          calc
            U.tape (H-(i:Int)) =
                U.tape (h+5+(3*b:Int)-(i:Int)) := by simp [H]
            _ = sideBit
                  (d0pow b ++ d1pow 2 ++ (m1EvenQ4LeftFacing a).drop 1) i :=
              hleftU i
            _ = sideBit
                  (s1LeftFacing 3 5 0 (a+b+2) (2^b-1)) i := by
              rw [← m1EvenQ4SuffixTargetLeft a b]
            _ = (s1Config 3 5 0 (a+b+2) (2^b-1) 0 H).tape
                  (H-(i:Int)) :=
              (s1Config_left_cell 3 5 0 (a+b+2) (2^b-1) 0 H i).symm
        exact hleftCell
      · let i : Nat := Int.toNat (x-H-1)
        have hcoord : x = H+1+(i:Int) := by
          dsimp [i]
          omega
        rw [hcoord]
        calc
          U.tape (H+1+(i:Int)) =
              sideBit (s0RightFacing 0) i := by
                have hr := hrightU i
                have hrightCoord :
                    h+6+(3*b:Int)+(i:Int) = H+1+(i:Int) := by
                  dsimp [H]
                  omega
                rw [hrightCoord] at hr
                exact hr
          _ = sideBit (s1PhysicalRight 0) i := by
                rfl
          _ = (s1Config 3 5 0 (a+b+2) (2^b-1) 0 H).tape
                (H+1+(i:Int)) := by
                exact (s1Config_right_cell
                  3 5 0 (a+b+2) (2^b-1) 0 H i).symm
  rw [m1Even_resetPrefixCost_eq,hframe',htarget]

/-- A complete source-level Rst1 decrement for n=6, including its
geometric all-ones drain.  This is exactly the first proposed increment
in the TM63 recurrence. -/
theorem m1Even_q4_counted_increment_source
    (a b : Nat) (h : Int) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 1 6 a b)
      (s1Config 3 6 1 a 0 b h) =
      some (s1Config 3 5 0 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m1Even_q4_reset_prefix_source a b h
  have hbound := resetDrainBound a b 1 ha
  have hdrain := s1Config_counted_drain 3 5 0 (a+b+2) b 0
    (h+5+3*b) (by simpa [resetDelta] using hbound)
  rw [proposedIncrementCost_decomp,run_add,hp]
  simpa [s1Config] using hdrain

#print axioms q4_suffix_left_word_of_stream
#print axioms m1Even_q4_prefix_far_tail
#print axioms m1Even_q4_reset_prefix_source
#print axioms m1Even_q4_counted_increment_source

end BB6Coverage.Agent42M1EvenSuffix
