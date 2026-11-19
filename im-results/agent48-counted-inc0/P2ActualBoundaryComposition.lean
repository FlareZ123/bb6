import P2ActualBoundaryBridge
import S0CountedDrain
import Q4S0FirstCycleMacros
import Lean.Elab.Tactic.Omega

/-!
# S0 drain + corrected P2 boundary + right continuation

For the authentic residual family
  1^(m+2) ++ 0101 ++ 1^7 ++ 00 ++ tail,
the all-ones S0 drain exposes a left-facing d1 counter.  The state-3
left sweep clears the cell immediately to the right of the 0101 boundary,
so the exact 73-step arbitrary-exterior bridge applies.  The bridge
restores the three-cell right run; the swept interval and the drained
right counter then supply the long state-4 scan, two-zero setup, and
state-1 d1-block scan.

This is an intermediate source theorem.  It does not identify a concrete
q4Tail output with this S0 family and is not a BB(6) halting result.
-/ 

namespace BB6Coverage.Agent48P2ActualBoundaryComposition

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent42Q4S0Drain
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent38P2ActualBoundary
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix

set_option maxHeartbeats 4000000

/-- The corrected residual left word.  The tail after the two explicit
zeroes is arbitrary and is not inspected by the 73-step bridge. -/
def p2ActualResidualLeft (m : Nat) (tail : List Bool) : List Bool :=
  List.replicate (m+2) true ++ [false,true,false,true] ++
    List.replicate 7 true ++ [false,false] ++ tail

private theorem sideBit_replicate_true_local (n i : Nat) (hi : i<n) :
    sideBit (List.replicate n true) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [sideBit]
      | succ i =>
          have hi' : i<n := by omega
          simpa [sideBit] using ih i hi'

private theorem sideBit_d1pow_true_local (n i : Nat) (hi : i<3*n) :
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

private theorem p2ActualResidualLeft_prefix
    (m : Nat) (tail : List Bool) (i : Nat) (hi : i<m+2) :
    sideBit (p2ActualResidualLeft m tail) i = true := by
  unfold p2ActualResidualLeft
  rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_left
    (List.replicate (m+2) true)
    ([false,true,false,true] ++ List.replicate 7 true ++
      [false,false] ++ tail) i (by simp; omega)]
  exact sideBit_replicate_true_local (m+2) i hi

private theorem p2ActualResidualLeft_after_prefix
    (m : Nat) (tail : List Bool) (j : Nat) :
    sideBit (p2ActualResidualLeft m tail) (m+2+j) =
      sideBit
        ([false,true,false,true] ++ List.replicate 7 true ++
          [false,false] ++ tail) j := by
  unfold p2ActualResidualLeft
  rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
    (List.replicate (m+2) true)
    ([false,true,false,true] ++ List.replicate 7 true ++
      [false,false] ++ tail) (m+2+j) (by simp)]
  have hidx : m+2+j-(List.replicate (m+2) true).length = j := by simp
  rw [hidx]

/-- The state-4 frame after the corrected 73-step bridge, starting from
the drained S0 configuration and its left sweep. -/
def p2ActualS0BridgeFrame (m n : Nat) (tail : List Bool) : Config :=
  let a := n-1
  let H : Int := (m+2+3*n : Int)
  let ell := p2ActualResidualLeft m tail
  let T := (s0Config ell a 0 (2^a-1) H).tape
  let K := 3*a+(m+2)
  let S := s0LeftSweep K T H
  BB6Coverage.Agent6Q4Prefix.frameAt S 3
    p2ActualBoundaryInside p2ActualBoundaryEnd

/-- Exact state-2 endpoint after the right continuation. -/
def p2ActualS0State2Endpoint (m n : Nat) (tail : List Bool) : Config :=
  let a := n-1
  let H : Int := (m+2+3*n : Int)
  let B := p2ActualS0BridgeFrame m n tail
  ⟨2, H+6+(3*(2^a:Int)),
    p2WriteOne
      (BB6Coverage.Agent8Q4Suffix.d0Sweep (2^a)
        (p2AfterTwoZeros B.tape H) (H+7))
      (H+7+(3*(2^a:Int)))⟩

private theorem config_ext_local {c d : Config}
    (hs : c.state=d.state) (hh : c.head=d.head)
    (ht : c.tape=d.tape) : c=d := by
  cases c with
  | mk cs ch ct =>
    cases d with
    | mk ds dh dt =>
      simp_all

/-- A generic, exact original-TM2 continuation from the corrected P2
S0 boundary to the state-2 edge after all 2^a right-hand d1 blocks have
been converted.  The tail after the two explicit left zeroes is arbitrary. -/
theorem p2ActualS0_to_state2
    (m n : Nat) (tail : List Bool) (hn : 2≤n) :
    run tm2
      ((6*4^(n-1)+42*2^(n-1)-12*(n-1)-48) +
        (3*(3*(n-1)+(m+2))+73) +
        ((m+2+3*n)+6+3*2^(n-1)))
      (s0Config (p2ActualResidualLeft m tail) (n-1)
        (2^(n-1)-1) 0 ((m+2+3*n:Int))) =
      some (p2ActualS0State2Endpoint m n tail) := by
  let a : Nat := n-1
  let H : Nat := m+2+3*n
  let h : Int := (H:Int)
  let K : Nat := 3*a+(m+2)
  let ell : List Bool := p2ActualResidualLeft m tail
  let T : Int → Bool := (s0Config ell a 0 (2^a-1) h).tape
  let S : Int → Bool := s0LeftSweep K T h
  let B : Config :=
    BB6Coverage.Agent6Q4Prefix.frameAt S 3
      p2ActualBoundaryInside p2ActualBoundaryEnd
  let D : Nat := 6*4^a+42*2^a-12*a-48

  have ha : 1≤a := by dsimp [a]; omega
  have hpowpos : 0<2^a := by positivity
  have hK : 0<K := by dsimp [K]; omega
  have hHK : h-(K:Int)=3 := by dsimp [h,H,K,a]; omega

  have hleftFacing : s0LeftFacing ell a 0 = d1pow a ++ ell := by
    simp [s0LeftFacing,binDec_zero]

  have hleftOnes : s0LeftOnes T h K := by
    intro i hi
    have hcell := s0Config_left_cell ell a 0 (2^a-1) h i
    rw [hleftFacing] at hcell
    by_cases hsmall : i<3*a
    · exact hcell.trans (sideBit_d1pow_true_local a i hsmall)
    · have hidx : i-3*a<m+2 := by dsimp [K] at hi; omega
      have hsplit :=
        BB6Coverage.Agent6Q4Prefix.sideBit_append_right
          (d1pow a) ell i (by rw [d1pow_length]; omega)
      have hlen : (d1pow a).length=3*a := by simp [d1pow_length]
      have hidx' : i-(d1pow a).length=i-3*a := by rw [hlen]
      rw [hidx'] at hsplit
      have hbit := p2ActualResidualLeft_prefix m tail (i-3*a) hidx
      exact hcell.trans (hsplit.trans hbit)

  have hright : T (h+1)=false := by
    have hc := s0Config_right_cell ell a 0 (2^a-1) h 0
    simpa [s0RightFacing,sideBit] using hc

  have hsweep_before (x : Int) (hx : x≤3) : S x=T x := by
    change s0LeftSweep K T h x = T x
    rw [s0LeftSweep_shift K T h hK x]
    have hne : x ≠ h-(K:Int)+1 := by rw [hHK]; omega
    have hnot : ¬(h-(K:Int)+2≤x ∧ x≤h+1) := by rw [hHK]; omega
    simp [hne,hnot]

  have hboundary (j : Nat) :
      S (3-(j:Int)) =
        sideBit
          ([false,true,false,true] ++ List.replicate 7 true ++
            [false,false] ++ tail) j := by
    rw [hsweep_before (3-(j:Int)) (by omega)]
    have hcell := s0Config_left_cell ell a 0 (2^a-1) h
      (3*a+(m+2+j))
    rw [hleftFacing] at hcell
    have hcoord :
        h-((3*a+(m+2+j):Nat):Int) = 3-(j:Int) := by
      dsimp [h,H,a]
      omega
    rw [hcoord] at hcell
    have hsplit :=
      BB6Coverage.Agent6Q4Prefix.sideBit_append_right
        (d1pow a) ell (3*a+(m+2+j))
        (by rw [d1pow_length]; omega)
    have hlen : (d1pow a).length=3*a := by simp [d1pow_length]
    have hidx :
        (3*a+(m+2+j))-(d1pow a).length=m+2+j := by
      rw [hlen]
    rw [hidx] at hsplit
    calc
      S (3-(j:Int)) = T (3-(j:Int)) := by
        exact hsweep_before (3-(j:Int)) (by omega)
      _ = sideBit (d1pow a ++ ell) (3*a+(m+2+j)) := hcell
      _ = sideBit ell (m+2+j) := hsplit
      _ = sideBit
          ([false,true,false,true] ++ List.replicate 7 true ++
            [false,false] ++ tail) j :=
        p2ActualResidualLeft_after_prefix m tail j

  have hinput : p2ActualBoundaryInput S 3 := by
    have h0 : S 3=false := by simpa [sideBit] using hboundary 0
    have h1 : S 2=true := by simpa [sideBit] using hboundary 1
    have h2 : S 1=false := by simpa [sideBit] using hboundary 2
    have h3 : S 0=true := by simpa [sideBit] using hboundary 3
    have hones : ∀ i : Nat, i<7 → S (3-4-(i:Int))=true := by
      intro i hi
      have hb := hboundary (4+i)
      have hbit :
          sideBit
            ([false,true,false,true] ++ List.replicate 7 true ++
              [false,false] ++ tail) (4+i) = true := by
        rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
          ([false,true,false,true] : List Bool)
          (List.replicate 7 true ++ [false,false] ++ tail)
          (4+i) (by simp)]
        have hidx : 4+i-([false,true,false,true] : List Bool).length=i := by simp
        rw [hidx]
        rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_left
          (List.replicate 7 true) ([false,false] ++ tail) i
          (by simp; omega)]
        exact sideBit_replicate_true_local 7 i hi
      have hcoord : 3-(4+(i:Int))=3-4-(i:Int) := by omega
      simpa [hcoord,hbit] using hb
    have hzero11 :
        sideBit
          ([false,true,false,true] ++ List.replicate 7 true ++
            [false,false] ++ tail) 11 = false := by
      rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
        ([false,true,false,true] : List Bool)
        (List.replicate 7 true ++ [false,false] ++ tail) 11 (by simp)]
      have hidx : 11-([false,true,false,true] : List Bool).length=7 := by simp
      rw [hidx]
      rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
        (List.replicate 7 true) ([false,false] ++ tail) 7 (by simp)]
      simp [sideBit]
    have hzero12 :
        sideBit
          ([false,true,false,true] ++ List.replicate 7 true ++
            [false,false] ++ tail) 12 = false := by
      rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
        ([false,true,false,true] : List Bool)
        (List.replicate 7 true ++ [false,false] ++ tail) 12 (by simp)]
      have hidx : 12-([false,true,false,true] : List Bool).length=8 := by simp
      rw [hidx]
      rw [BB6Coverage.Agent6Q4Prefix.sideBit_append_right
        (List.replicate 7 true) ([false,false] ++ tail) 8 (by simp)]
      have hidx' : 8-7=1 := by omega
      rw [hidx']
      simp [sideBit]
    have h4 : S 4=false := by
      change s0LeftSweep K T h 4=false
      rw [s0LeftSweep_shift K T h hK 4]
      simp [hHK]
    exact ⟨h0,h1,h2,h3,hones,
      (by simpa [hzero11] using hboundary 11),
      (by simpa [hzero12] using hboundary 12),h4⟩

  have hpost :
      run tm2 (3*K+73) ⟨3,h,T⟩ =
        some B := by
    simpa [S,B] using p2ActualPostlude_at K T h hleftOnes hright hinput

  have hBconfig : B=⟨4,2,B.tape⟩ := by
    apply config_ext_local
    · simp [B,BB6Coverage.Agent6Q4Prefix.frameAt_state,
        p2ActualBoundaryEnd]
    · simp [B,BB6Coverage.Agent6Q4Prefix.frameAt_head,
        p2ActualBoundaryEnd]
    · rfl

  have hBoutside (x : Int) (hx : 5≤x) : B.tape x=S x := by
    rw [BB6Coverage.Agent6Q4Prefix.frameAt_tape]
    have hnot : p2ActualBoundaryInside (x-3)=false := by
      simp [p2ActualBoundaryInside]
      omega
    simp [hnot]

  have hsweep_run (x : Int) (hxlo : 5≤x) (hxhi : x≤h+1) :
      S x=true := by
    change s0LeftSweep K T h x=true
    rw [s0LeftSweep_shift K T h hK x]
    have hne : x≠h-(K:Int)+1 := by rw [hHK]; omega
    have hlow : h-(K:Int)+2≤x := by rw [hHK]; omega
    simp [hne,hlow,hxhi]

  have hsweep_after (x : Int) (hx : h+1<x) : S x=T x := by
    change s0LeftSweep K T h x=T x
    rw [s0LeftSweep_shift K T h hK x]
    have hne : x≠h-(K:Int)+1 := by rw [hHK]; omega
    have hnot : ¬(h-(K:Int)+2≤x ∧ x≤h+1) := by omega
    simp [hne,hnot]

  have hrightCell (j : Nat) (hj : j=1 ∨ j=2 ∨ j=3) :
      T (h+1+(j:Int))=true := by
    rcases hj with hj|hj|hj
    · subst j
      have hc := s0Config_right_cell ell a 0 (2^a-1) h 1
      simpa [s0RightFacing,sideBit] using hc
    · subst j
      have hc := s0Config_right_cell ell a 0 (2^a-1) h 2
      simpa [s0RightFacing,sideBit] using hc
    · subst j
      have hc := s0Config_right_cell ell a 0 (2^a-1) h 3
      simpa [s0RightFacing,sideBit] using hc

  have hrightOnes : ∀ i : Nat, i<H+3 →
      B.tape (2+(i:Int))=true := by
    intro i hi
    by_cases hi0 : i<3
    · have hend := p2ActualBoundary_end_right_ones S 3
      rcases hend with ⟨_,_,h2,h3,h4⟩
      have hc : i=0 ∨ i=1 ∨ i=2 := by omega
      rcases hc with hi|hi|hi
      · subst i
        simpa using h2
      · subst i
        simpa using h3
      · subst i
        simpa using h4
    · by_cases hi1 : i<H
      · have hxlo : 5≤2+(i:Int) := by omega
        have hxhi : 2+(i:Int)≤h+1 := by dsimp [h,H]; omega
        rw [hBoutside (2+(i:Int)) hxlo]
        exact hsweep_run (2+(i:Int)) hxlo hxhi
      · have hc : i=H ∨ i=H+1 ∨ i=H+2 := by omega
        rcases hc with hi|hi|hi
        · subst i
          have hxlo : 5≤h+2 := by dsimp [h,H]; omega
          rw [hBoutside (h+2) hxlo]
          rw [hsweep_after (h+2) (by omega)]
          have hc := hrightCell 1 (by simp)
          simpa using hc
        · subst i
          have hxlo : 5≤h+3 := by dsimp [h,H]; omega
          rw [hBoutside (h+3) hxlo]
          rw [hsweep_after (h+3) (by omega)]
          have hc := hrightCell 2 (by simp)
          simpa using hc
        · subst i
          have hxlo : 5≤h+4 := by dsimp [h,H]; omega
          rw [hBoutside (h+4) hxlo]
          rw [hsweep_after (h+4) (by omega)]
          have hc := hrightCell 3 (by simp)
          simpa using hc

  have hzero5 : B.tape (h+5)=false := by
    have hxlo : 5≤h+5 := by dsimp [h,H]; omega
    rw [hBoutside (h+5) hxlo]
    rw [hsweep_after (h+5) (by omega)]
    have hc := s0Config_right_cell ell a 0 (2^a-1) h 4
    simpa [s0RightFacing,sideBit] using hc

  have hzero6 : B.tape (h+6)=false := by
    have hxlo : 5≤h+6 := by dsimp [h,H]; omega
    rw [hBoutside (h+6) hxlo]
    rw [hsweep_after (h+6) (by omega)]
    have hc := s0Config_right_cell ell a 0 (2^a-1) h 5
    simpa [s0RightFacing,sideBit] using hc

  have hrightUnary (u : Nat) (hu : u<3*2^a) :
      T (h+7+(u:Int))=true := by
    have hu' : u<3*((2^a-1)+1) := by
      have hp : 1≤2^a := by omega
      omega
    simpa using
      s0Config_carryRightOnes ell a 0 (2^a-1) h u hu'

  have hblocks :
      d1BlocksOn (p2AfterTwoZeros B.tape h) (h+7) (2^a) := by
    intro i hi
    have hcell (j : Nat) (hj : j<3) :
        p2AfterTwoZeros B.tape h (h+7+3*(i:Int)+(j:Int))=true := by
      have hne5 : h+7+3*(i:Int)+(j:Int) ≠ h+5 := by omega
      have hne6 : h+7+3*(i:Int)+(j:Int) ≠ h+6 := by omega
      calc
        p2AfterTwoZeros B.tape h (h+7+3*(i:Int)+(j:Int)) =
            B.tape (h+7+3*(i:Int)+(j:Int)) := by
              simp [p2AfterTwoZeros,p2WriteOne,hne5,hne6]
        _ = S (h+7+3*(i:Int)+(j:Int)) :=
              hBoutside _ (by omega)
        _ = T (h+7+3*(i:Int)+(j:Int)) :=
              hsweep_after _ (by omega)
        _ = true := by
              have hsrc := hrightUnary (3*i+j) (by omega)
              simpa [Nat.cast_add,Nat.cast_mul,Int.add_assoc,
                Int.mul_add] using hsrc
    exact ⟨hcell 0 (by omega),hcell 1 (by omega),hcell 2 (by omega)⟩

  have hblankSource :
      T (h+7+(3*(2^a:Int)))=false := by
    have hc := s0Config_right_cell ell a 0 (2^a-1) h (6+3*2^a)
    have hlen :
        (s0RightFacing (2^a-1)).length=6+3*2^a := by
      simp [s0RightFacing,d1pow_length]
    have hside :
        sideBit (s0RightFacing (2^a-1)) (6+3*2^a)=false :=
      BB6Coverage.Agent6Q4Prefix.sideBit_ge_length
        (s0RightFacing (2^a-1)) (6+3*2^a) (by rw [hlen])
    have hcoord :
        h+7+(3*(2^a:Int)) = h+1+((6+3*2^a:Int)) := by omega
    rw [hcoord] at hc
    exact hc.trans hside

  have hblank :
      p2AfterTwoZeros B.tape h (h+7+(3*(2^a:Int)))=false := by
    calc
      p2AfterTwoZeros B.tape h (h+7+(3*(2^a:Int))) =
          B.tape (h+7+(3*(2^a:Int))) := by
            simp [p2AfterTwoZeros,p2WriteOne] <;> omega
      _ = S (h+7+(3*(2^a:Int))) :=
            hBoutside _ (by omega)
      _ = T (h+7+(3*(2^a:Int))) :=
            hsweep_after _ (by omega)
      _ = false := hblankSource

  have hrightRun := p2ActualRightContinuation H a B.tape
    hrightOnes hzero5 hzero6 hblocks hblank

  have hD :
      run tm2 D
        (s0Config ell a (2^a-1) 0 h) =
      some (s0Config ell a 0 (2^a-1) h) := by
    simpa [D] using
      s0Config_counted_drain_closed ell a a h (by omega)

  have hafter :
      run tm2 (D+(3*K+73))
        (s0Config ell a (2^a-1) 0 h) =
      some ⟨4,2,B.tape⟩ := by
    rw [run_append,hD]
    simp only [Option.bind_some]
    simpa [T,B,hHK] using hpost

  have hcost :
      ((6*4^(n-1)+42*2^(n-1)-12*(n-1)-48) +
        (3*(3*(n-1)+(m+2))+73) +
        ((m+2+3*n)+6+3*2^(n-1))) =
      D+(3*K+73)+(H+6+3*2^a) := by
    dsimp [D,K,H,a]
    omega

  rw [hcost,run_append,hafter]
  simp only [Option.bind_some]
  simpa [p2ActualS0State2Endpoint,B,a,H,h] using hrightRun

#print axioms p2ActualS0_to_state2

end BB6Coverage.Agent48P2ActualBoundaryComposition
