import M0EvenEightValuationSource
import Q4RightEndpoint
import Lean.Elab.Tactic.Omega

/-!
# Marker-0, n=8q all-valuation counted source increment

This is the missing all-q composition for the (marker,n mod 8)=(0,0)
row.  It connects the valuation-dependent q4 prefix to the parity-free
q4 suffix and the existing counted S1 drain.  The proof is source-level:
all runs are over the original TM2 transition table and arbitrary bounded
S1 configurations, not blank-root reachability.
-/

namespace BB6Coverage.Agent48M0EvenEightValuationQ4Source

open BB6Coverage
open BB6ChampionArithmetic
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent48M0EvenEightValuation
open BB6Coverage.Agent48M0EvenEightValuationFixedPrefix
open BB6Coverage.Agent48M0EvenEightValuationSweepFacts
open BB6Coverage.Agent48M0EvenEightValuationEncoding
open BB6Coverage.Agent48M0EvenEightValuationSuffix
open BB6Coverage.Agent48M0EvenEightValuationSource

set_option maxHeartbeats 3000000

private def expandedLeftFacing (a t len u : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++
    d0pow (t+4) ++ d1 ++ binDec len u ++ lh

private theorem d0pow_length_local (n : Nat) :
    (d0pow n).length = 3*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [d0pow,d0,ih]
      omega

private theorem sideBit_d0pow_mod_local (n i : Nat)
    (hi : i < 3*n) :
    sideBit (d0pow n) i = decide (i % 3 = 2) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      change sideBit (d0 ++ d0pow n) i = decide (i % 3 = 2)
      by_cases hi0 : i < 3
      · have hc : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hc with h0 | h1 | h2 <;> subst i <;>
          simp [d0,sideBit]
      · have hi3 : 3 ≤ i := by omega
        have hi' : i-3 < 3*n := by omega
        rw [sideBit_append_right d0 (d0pow n) i
          (by simp [d0]; omega)]
        rw [show d0.length = 3 by rfl]
        have hmod : (i-3)%3 = i%3 := by omega
        simpa [hmod] using ih (i-3) hi'

private theorem expanded_prefix_allTrue
    (a t len u i : Nat) (ha : 0 < a)
    (hi : i < 3*a-2) :
    sideBit (expandedLeftFacing a t len u) i = true := by
  let pre := [true] ++ d1pow (a-1)
  let rest := markerWord 2 ++ d0pow (t+4) ++
    d1 ++ binDec len u ++ lh
  have hsplit : expandedLeftFacing a t len u = pre ++ rest := by
    simp [expandedLeftFacing,pre,rest,List.append_assoc]
  have hlen : pre.length = 3*a-2 := by
    simp [pre,d1pow_length]
    omega
  rw [hsplit]
  rw [sideBit_append_left pre rest i (by rw [hlen]; omega)]
  by_cases hi0 : i=0
  · subst i
    simp [pre,sideBit]
  · rw [sideBit_append_right [true] (d1pow (a-1)) i
      (by simp; omega)]
    exact sideBit_d1pow_true (a-1) (i-1) (by omega)

private theorem expanded_marker_bit
    (a t len u k : Nat) (ha : 0 < a)
    (hk : k < 4) :
    sideBit (expandedLeftFacing a t len u) (3*a-2+k) =
      if k=2 then false else true := by
  let pre := [true] ++ d1pow (a-1)
  let tail := d0pow (t+4) ++ d1 ++ binDec len u ++ lh
  let rest := markerWord 2 ++ tail
  have hsplit : expandedLeftFacing a t len u = pre ++ rest := by
    simp [expandedLeftFacing,pre,rest,tail,List.append_assoc]
  have hlen : pre.length = 3*a-2 := by
    simp [pre,d1pow_length]
    omega
  rw [hsplit]
  rw [sideBit_append_right pre rest (3*a-2+k)
    (by rw [hlen]; omega)]
  rw [hlen,show 3*a-2+k-(3*a-2)=k by omega]
  dsimp [rest]
  have hinside : k < (markerWord 2).length := by
    simp [markerWord]
    omega
  rw [sideBit_append_left (markerWord 2) tail k hinside]
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hc with h0 | h1 | h2 | h3 <;> subst k <;>
    simp [markerWord,sideBit]

private theorem expanded_d0_bit
    (a t len u j r : Nat) (ha : 0 < a) (hj : j < t+4)
    (hr : r < 3) :
    sideBit (expandedLeftFacing a t len u)
      (3*a+2+3*j+r) = decide (r=2) := by
  let pre := [true] ++ d1pow (a-1) ++ markerWord 2
  let tail := d1 ++ binDec len u ++ lh
  let rest := d0pow (t+4) ++ tail
  have hsplit : expandedLeftFacing a t len u = pre ++ rest := by
    simp [expandedLeftFacing,pre,rest,tail,List.append_assoc]
  have hlen : pre.length = 3*a+2 := by
    simp [pre,d1pow_length,markerWord]
    omega
  rw [hsplit]
  rw [sideBit_append_right pre rest (3*a+2+3*j+r)
    (by rw [hlen]; omega)]
  rw [hlen,show 3*a+2+3*j+r-(3*a+2)=3*j+r by omega]
  dsimp [rest]
  have hi : 3*j+r < 3*(t+4) := by omega
  rw [sideBit_append_left (d0pow (t+4)) tail (3*j+r) (by rw [d0pow_length_local]; exact hi)]
  have hmod : (3*j+r)%3 = r := by omega
  simpa [hmod] using
    sideBit_d0pow_mod_local (t+4) (3*j+r) hi

private theorem expanded_d1_bit
    (a t len u r : Nat) (ha : 0 < a) (hr : r < 3) :
    sideBit (expandedLeftFacing a t len u)
      (3*a+14+3*t+r) = true := by
  let pre := [true] ++ d1pow (a-1) ++
    markerWord 2 ++ d0pow (t+4)
  let tail := binDec len u ++ lh
  let rest := d1 ++ tail
  have hsplit : expandedLeftFacing a t len u = pre ++ rest := by
    simp [expandedLeftFacing,pre,rest,tail,List.append_assoc]
  have hlen : pre.length = 3*a+14+3*t := by
    simp [pre,d1pow_length,d0pow_length_local,markerWord]
    omega
  rw [hsplit]
  rw [sideBit_append_right pre rest
    (3*a+14+3*t+r) (by rw [hlen]; omega)]
  rw [hlen,show 3*a+14+3*t+r-(3*a+14+3*t)=r by omega]
  dsimp [rest]
  have hi : r < d1.length := by simp [d1]; omega
  rw [sideBit_append_left d1 tail r hi]
  have hc : r=0 ∨ r=1 ∨ r=2 := by omega
  rcases hc with h0 | h1 | h2 <;> subst r <;> rfl

private theorem sourceSuffix_lastD0_true (t len u : Nat) :
    sideBit (m0EvenEightValuationSourceSuffix t len u)
      (16+3*t) = true := by
  let pre := markerWord 0 ++ d0 ++ d1pow (t+3)
  let tail := d0 ++ binDec len u ++ lh
  have hsplit :
      m0EvenEightValuationSourceSuffix t len u = pre ++ tail := by
    simp [m0EvenEightValuationSourceSuffix,pre,tail,
      List.append_assoc]
  have hlen : pre.length = 14+3*t := by
    simp [pre,markerWord,d0,d1pow_length]
    omega
  rw [hsplit]
  rw [sideBit_append_right pre tail (16+3*t)
    (by rw [hlen]; omega)]
  rw [hlen,show 16+3*t-(14+3*t)=2 by omega]
  dsimp [tail]
  rw [List.append_assoc]
  have hi : 2 < d0.length := by decide
  rw [sideBit_append_left d0 (binDec len u ++ lh) 2 hi]
  simp [d0,sideBit]

private theorem expanded_tail_equiv
    (L q a b u t len i : Nat)
    (hface :
      s1LeftFacing L (8*q) 0 a 0 =
        d1pow a ++ m0EvenEightValuationSourceSuffix t len u)
    (ha : 0 < a)
    (hExpanded :
      m0EvenEightQ4LeftFacingAll L q a =
        expandedLeftFacing a t len u)
    (hi : 3*a+17+3*t ≤ i) :
    sideBit (s1LeftFacing L (8*q) 0 a 0) i =
      sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
  let sourcePrefix := d1pow a ++ markerWord 0 ++ d0 ++
    d1pow (t+3) ++ d0
  let targetPrefix := [true] ++ d1pow (a-1) ++
    markerWord 2 ++ d0pow (t+4) ++ d1
  let tail := binDec len u ++ lh
  have hsource :
      s1LeftFacing L (8*q) 0 a 0 = sourcePrefix ++ tail := by
    rw [hface]
    simp [m0EvenEightValuationSourceSuffix,sourcePrefix,tail,
      List.append_assoc]
  have htarget :
      m0EvenEightQ4LeftFacingAll L q a = targetPrefix ++ tail := by
    rw [hExpanded]
    simp [expandedLeftFacing,targetPrefix,tail,List.append_assoc]
  have hlenSource : sourcePrefix.length = 3*a+17+3*t := by
    simp [sourcePrefix,markerWord,d0,d1,d1pow_length]
    omega
  have hlenTarget : targetPrefix.length = 3*a+17+3*t := by
    simp [targetPrefix,markerWord,d1,d1pow_length,d0pow_length_local]
    omega
  rw [hsource,htarget]
  rw [sideBit_append_right sourcePrefix tail i
    (by rw [hlenSource]; omega)]
  rw [sideBit_append_right targetPrefix tail i
    (by rw [hlenTarget]; omega)]
  rw [hlenSource,hlenTarget]

private theorem bridgeMid_twelve_ones_local
    (bit : Bool) (i : Nat) (hi : i < 12) :
    decide ((-12+(i:Int)) ∈ (bridgeMidWithBit bit).marked) = true := by
  have hc :
      i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨
      i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 |
    h6 | h7 | h8 | h9 | h10 | h11 <;> subst i <;>
    cases bit <;> decide

/-- The valuation bubble appends 4+t complete all-one blocks to the
fixed twelve-cell output of the 44-step bridge. -/
private theorem valuationQ4_rightOnes
    (T1 : Int → Bool) (hN : Int) (t : Nat) :
    rightOnes
      (afterZeroExit4
        (sweptLeft (3*t)
          (frameAt T1 hN bridgeInside44
            (bridgeMidWithBit (decide (0<t)))).tape
          (hN-14))
        (hN-14-(3*t:Int)))
      (hN-12-(3*t:Int)) (4+t) := by
  let T2 := (frameAt T1 hN bridgeInside44
    (bridgeMidWithBit (decide (0<t)))).tape
  let hH := hN-14
  let hB := hH-(3*t:Int)
  let hR := hB+2
  have hfixed : ∀ i : Nat, i < 12 →
      T2 (hH+2+(i:Int)) = true := by
    intro i hi
    have hcoord : hH+2+(i:Int)-hN = -12+(i:Int) := by
      dsimp [hH]
      omega
    have hin : bridgeInside44
        (hH+2+(i:Int)-hN) = true := by
      rw [hcoord]
      simp [bridgeInside44]
      omega
    have hf := frameAt_tape_inside T1 hN bridgeInside44
      (bridgeMidWithBit (decide (0<t))) (hH+2+(i:Int)) hin
    have hm := bridgeMid_twelve_ones_local
      (decide (0<t)) i hi
    rw [hcoord] at hf
    simpa [T2] using hf.trans hm
  have hraw := sweptLeft_creates_rightOnes t T2 hH hfixed
  intro i hi
  obtain ⟨h0,h1,h2⟩ := hraw i hi
  have hx0 : hR+3*(i:Int) ≠ hB-1 := by
    dsimp [hR,hB,hH]
    omega
  have hx1 : hR+3*(i:Int)+1 ≠ hB-1 := by
    dsimp [hR,hB,hH]
    omega
  have hx2 : hR+3*(i:Int)+2 ≠ hB-1 := by
    dsimp [hR,hB,hH]
    omega
  have hy0 : hR+3*(i:Int) ≠ hB := by
    dsimp [hR,hB,hH]
    omega
  have hy1 : hR+3*(i:Int)+1 ≠ hB := by
    dsimp [hR,hB,hH]
    omega
  have hy2 : hR+3*(i:Int)+2 ≠ hB := by
    dsimp [hR,hB,hH]
    omega
  have hz0 : hR+3*(i:Int) ≠ hB+1 := by
    dsimp [hR,hB,hH]
    omega
  have hz1 : hR+3*(i:Int)+1 ≠ hB+1 := by
    dsimp [hR,hB,hH]
    omega
  have hz2 : hR+3*(i:Int)+2 ≠ hB+1 := by
    dsimp [hR,hB,hH]
    omega
  have hR' : hN-12-(3*t:Int) = hR := by dsimp [hR,hB,hH]; omega
  change afterZeroExit4 (sweptLeft (3*t) T2 hH) hB (hN-12-(3*t:Int)+3*(i:Int)) = true ∧
    afterZeroExit4 (sweptLeft (3*t) T2 hH) hB (hN-12-(3*t:Int)+3*(i:Int)+1) = true ∧
    afterZeroExit4 (sweptLeft (3*t) T2 hH) hB (hN-12-(3*t:Int)+3*(i:Int)+2) = true
  rw [hR']
  exact ⟨by simpa [afterZeroExit4,hx0,hy0,hz0] using h0,
    by simpa [afterZeroExit4,hx1,hy1,hz1] using h1,
    by simpa [afterZeroExit4,hx2,hy2,hz2] using h2⟩

private theorem sweptRight1_preserves_right_local
    (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : h+3*(n:Int) ≤ x) :
    sweptRight1 n T h x = T x := by
  induction n generalizing T h with
  | zero => simp [sweptRight1]
  | succ n ih =>
      simp only [sweptRight1]
      have hp := ih (afterRight1 T h) (h+3) (by omega)
      rw [hp]
      have hx0 : x ≠ h := by omega
      have hx1 : x ≠ h+1 := by omega
      have hx2 : x ≠ h+2 := by omega
      simp [afterRight1,hx0,hx1,hx2]

private theorem valuationQ4_cutTape_scanBlock
    (L q a b t : Nat) (h : Int) (i : Nat)
    (hi : i < 4+t) :
    m0EvenEightValuationQ4CutTape L q a b t h
        (h-((3*a:Nat):Int)-12-(3*t:Int)+3*(i:Int)) = false ∧
    m0EvenEightValuationQ4CutTape L q a b t h
        (h-((3*a:Nat):Int)-12-(3*t:Int)+3*(i:Int)+1) = false ∧
    m0EvenEightValuationQ4CutTape L q a b t h
        (h-((3*a:Nat):Int)-12-(3*t:Int)+3*(i:Int)+2) = true := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let N : Nat := 3*a
  let hN : Int := h-((N:Nat):Int)
  let bit : Bool := decide (0<t)
  let T1 := sweptLeft N T h
  let T2 := (frameAt T1 hN bridgeInside44
    (bridgeMidWithBit bit)).tape
  let hH : Int := hN-14
  let T3 := sweptLeft (3*t) T2 hH
  let hB : Int := hH-((3*t:Nat):Int)
  let T4 := afterZeroExit4 T3 hB
  let hR : Int := hB+2
  let T5 := sweptRight1 (4+t) T4 hR
  have hOnes : rightOnes T4 hR (4+t) := by
    have heq : hR = hN-12-(3*t:Int) := by dsimp [hR,hB,hH]; omega
    rw [heq]
    exact valuationQ4_rightOnes T1 hN t
  have hlast : hR+3*((4+t:Nat):Int) = hN := by
    dsimp [hR,hB,hH]
    omega
  have hx0 : hR+3*(i:Int) < hN := by
    rw [← hlast]
    omega
  have hx1 : hR+3*(i:Int)+1 < hN := by
    rw [← hlast]
    omega
  have hx2 : hR+3*(i:Int)+2 < hN := by
    rw [← hlast]
    omega
  have hblock := sweptRight1_block (4+t) T4 hR hOnes i hi
  have heq : h-((3*a:Nat):Int)-12-(3*t:Int)+3*(i:Int) = hR+3*(i:Int) := by dsimp [hR,hB,hH,hN,N]; omega
  rw [heq]
  change after101 T5 hN (hR+3*(i:Int)) = false ∧
      after101 T5 hN (hR+3*(i:Int)+1) = false ∧
      after101 T5 hN (hR+3*(i:Int)+2) = true
  refine ⟨?_,?_,?_⟩
  · have he0 : hR+3*(i:Int) ≠ hN := by omega
    have he1 : hR+3*(i:Int) ≠ hN+1 := by omega
    have he2 : hR+3*(i:Int) ≠ hN+2 := by omega
    simpa [after101,he0,he1,he2] using hblock.1
  · have he0 : hR+3*(i:Int)+1 ≠ hN := by omega
    have he1 : hR+3*(i:Int)+1 ≠ hN+1 := by omega
    have he2 : hR+3*(i:Int)+1 ≠ hN+2 := by omega
    simpa [after101,he0,he1,he2] using hblock.2.1
  · have he0 : hR+3*(i:Int)+2 ≠ hN := by omega
    have he1 : hR+3*(i:Int)+2 ≠ hN+1 := by omega
    have he2 : hR+3*(i:Int)+2 ≠ hN+2 := by omega
    simpa [after101,he0,he1,he2] using hblock.2.2

private theorem valuationQ4_cutTape_exitCells
    (L q a b t : Nat) (h : Int) :
    m0EvenEightValuationQ4CutTape L q a b t h
      (h-((3*a:Nat):Int)-14-(3*t:Int)-1) = true ∧
    m0EvenEightValuationQ4CutTape L q a b t h
      (h-((3*a:Nat):Int)-14-(3*t:Int)) = true ∧
    m0EvenEightValuationQ4CutTape L q a b t h
      (h-((3*a:Nat):Int)-14-(3*t:Int)+1) = true := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let N : Nat := 3*a
  let hN : Int := h-((N:Nat):Int)
  let bit : Bool := decide (0<t)
  let T1 := sweptLeft N T h
  let T2 := (frameAt T1 hN bridgeInside44
    (bridgeMidWithBit bit)).tape
  let hH : Int := hN-14
  let T3 := sweptLeft (3*t) T2 hH
  let hB : Int := hH-((3*t:Nat):Int)
  let T4 := afterZeroExit4 T3 hB
  let hR : Int := hB+2
  let T5 := sweptRight1 (4+t) T4 hR
  have hp0 := sweptRight1_preserves_left (4+t) T4 hR (hB-1) (by dsimp [hR]; omega)
  have hp1 := sweptRight1_preserves_left (4+t) T4 hR hB (by dsimp [hR]; omega)
  have hp2 := sweptRight1_preserves_left (4+t) T4 hR (hB+1) (by dsimp [hR]; omega)
  have h1010 : after101 T5 hN (hB-1) = T5 (hB-1) := by
    simp only [after101]
    split <;> rename_i he
    · dsimp [hB,hH,hN] at he; omega
    · split <;> rename_i he2
      · simp at he2; dsimp [hB,hH,hN] at he2; omega
      · rfl
  have h1011 : after101 T5 hN hB = T5 hB := by
    simp only [after101]
    split <;> rename_i he
    · dsimp [hB,hH,hN] at he; omega
    · split <;> rename_i he2
      · simp at he2; dsimp [hB,hH,hN] at he2; omega
      · rfl
  have h1012 : after101 T5 hN (hB+1) = T5 (hB+1) := by
    simp only [after101]
    split <;> rename_i he
    · dsimp [hB,hH,hN] at he; omega
    · split <;> rename_i he2
      · simp at he2; dsimp [hB,hH,hN] at he2; omega
      · rfl
  change after101 T5 hN (hB-1) = true ∧
      after101 T5 hN hB = true ∧
      after101 T5 hN (hB+1) = true
  refine ⟨?_,?_,?_⟩
  · calc
      after101 T5 hN (hB-1) = T5 (hB-1) := h1010
      _ = T4 (hB-1) := hp0
      _ = true := by simp [T4,afterZeroExit4]
  · calc
      after101 T5 hN hB = T5 hB := h1011
      _ = T4 hB := hp1
      _ = true := by simp [T4,afterZeroExit4]
  · calc
      after101 T5 hN (hB+1) = T5 (hB+1) := h1012
      _ = T4 (hB+1) := hp2
      _ = true := by simp [T4,afterZeroExit4]

private theorem valuationQ4_cutTape_markerCells
    (L q a b t : Nat) (h : Int) :
    m0EvenEightValuationQ4CutTape L q a b t h
      (h-((3*a:Nat):Int)+3) = true ∧
    m0EvenEightValuationQ4CutTape L q a b t h
      (h-((3*a:Nat):Int)+2) = true ∧
    m0EvenEightValuationQ4CutTape L q a b t h
      (h-((3*a:Nat):Int)+1) = true ∧
    m0EvenEightValuationQ4CutTape L q a b t h
      (h-((3*a:Nat):Int)) = false := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let N : Nat := 3*a
  let hN : Int := h-((N:Nat):Int)
  let bit : Bool := decide (0<t)
  let T1 := sweptLeft N T h
  let T2 := (frameAt T1 hN bridgeInside44
    (bridgeMidWithBit bit)).tape
  let hH : Int := hN-14
  let T3 := sweptLeft (3*t) T2 hH
  let hB : Int := hH-((3*t:Nat):Int)
  let T4 := afterZeroExit4 T3 hB
  let hR : Int := hB+2
  let T5 := sweptRight1 (4+t) T4 hR
  have hin : bridgeInside44 ((hN+3)-hN) = true := by
    simp [bridgeInside44] <;> omega
  have hf := frameAt_tape_inside T1 hN bridgeInside44
    (bridgeMidWithBit bit) (hN+3) hin
  have hm : decide (3 ∈ (bridgeMidWithBit bit).marked) = true := by
    by_cases hb : bit = true <;> simp [bridgeMidWithBit,hb]
  have hT2 : T2 (hN+3) = true := by
    rw [show hN+3-hN=3 by omega] at hf
    simpa [T2] using hf.trans hm
  have hT3 : T3 (hN+3) = T2 (hN+3) := by
    have hp := sweptLeft_preserves_right (3*t) T2 hH (hN+3) (by dsimp [hH]; omega)
    simpa [T3] using hp
  have hT4 : T4 (hN+3) = T3 (hN+3) := by
    simp [T4,afterZeroExit4]
    dsimp [hB,hH]
    omega
  have hlast : hR+3*((4+t:Nat):Int) = hN := by
    dsimp [hR,hB,hH]
    omega
  have hT5 : T5 (hN+3) = T4 (hN+3) := by
    have hp := sweptRight1_preserves_right_local (4+t) T4 hR (hN+3)
      (by rw [hlast]; omega)
    simpa [T5] using hp
  change after101 T5 hN (hN+3) = true ∧
      after101 T5 hN (hN+2) = true ∧
      after101 T5 hN (hN+1) = true ∧
      after101 T5 hN hN = false
  refine ⟨?_,?_,?_,?_⟩
  · calc
      after101 T5 hN (hN+3) = T5 (hN+3) := by simp [after101,show hN+3 ≠ hN by omega,show hN+3 ≠ hN+1 by omega,show hN+3 ≠ hN+2 by omega]
      _ = T4 (hN+3) := hT5
      _ = T3 (hN+3) := hT4
      _ = T2 (hN+3) := hT3
      _ = true := hT2
  · simp [after101,show hN+2 ≠ hN by omega]
  · simp [after101,show hN+1 ≠ hN by omega]
  · simp [after101]

private theorem valuationQ4_cutTape_eq_swept
    (L q a b t : Nat) (h x : Int)
    (hout :
      x < h-(3*a:Int)-15-(3*t:Int) ∨
      h-(3*a:Int)+3 < x) :
    m0EvenEightValuationQ4CutTape L q a b t h x =
      sweptLeft (3*a) (s1Config L (8*q) 0 a 0 b h).tape h x := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let N : Nat := 3*a
  let hN : Int := h-((N:Nat):Int)
  let bit : Bool := decide (0<t)
  let T1 := sweptLeft N T h
  let T2 := (frameAt T1 hN bridgeInside44
    (bridgeMidWithBit bit)).tape
  let hH : Int := hN-14
  let T3 := sweptLeft (3*t) T2 hH
  let hB : Int := hH-((3*t:Nat):Int)
  let T4 := afterZeroExit4 T3 hB
  let hR : Int := hB+2
  let T5 := sweptRight1 (4+t) T4 hR
  have houtFrame : bridgeInside44 (x-hN) = false := by
    rcases hout with hx | hx
    · change decide (-13 ≤ x-hN ∧ x-hN ≤ 3) = false
      apply decide_eq_false_iff_not.mpr
      dsimp [hN]
      omega
    · change decide (-13 ≤ x-hN ∧ x-hN ≤ 3) = false
      apply decide_eq_false_iff_not.mpr
      dsimp [hN]
      omega
  have hT2 : T2 x = T1 x := by
    have hf := frameAt_tape_outside T1 hN bridgeInside44
      (bridgeMidWithBit bit) x houtFrame
    simpa [T2] using hf
  have hT3 : T3 x = T2 x := by
    rcases hout with hx | hx
    · have hp := sweptLeft_preserves_left (3*t) T2 hH x (by
        dsimp [hB,hH]
        omega)
      simpa [T3] using hp
    · have hp := sweptLeft_preserves_right (3*t) T2 hH x (by
        dsimp [hH]
        omega)
      simpa [T3] using hp
  have hT4 : T4 x = T3 x := by
    have hx0 : x ≠ hB-1 := by rcases hout with hx | hx <;> dsimp [hB,hH,hN] <;> omega
    have hx1 : x ≠ hB := by rcases hout with hx | hx <;> dsimp [hB,hH,hN] <;> omega
    have hx2 : x ≠ hB+1 := by rcases hout with hx | hx <;> dsimp [hB,hH,hN] <;> omega
    simp [T4,afterZeroExit4,hx0,hx1,hx2]
  have hlast : hR+3*((4+t:Nat):Int) = hN := by
    dsimp [hR,hB,hH]
    omega
  have hT5 : T5 x = T4 x := by
    rcases hout with hx | hx
    · have hp := sweptRight1_preserves_left (4+t) T4 hR x (by
        dsimp [hR,hB,hH,hN]
        omega)
      simpa [T5] using hp
    · have hp := sweptRight1_preserves_right_local (4+t) T4 hR x (by
        rw [hlast]
        omega)
      simpa [T5] using hp
  have hT6 : after101 T5 hN x = T5 x := by
    have hx0 : x ≠ hN := by rcases hout with hx | hx <;> dsimp [hN] <;> omega
    have hx1 : x ≠ hN+1 := by rcases hout with hx | hx <;> dsimp [hN] <;> omega
    have hx2 : x ≠ hN+2 := by rcases hout with hx | hx <;> dsimp [hN] <;> omega
    simp [after101,hx0,hx1,hx2]
  change after101 T5 hN x = T1 x
  calc
    after101 T5 hN x = T5 x := hT6
    _ = T4 x := hT5
    _ = T3 x := hT4
    _ = T2 x := hT3
    _ = T1 x := hT2

private theorem valuationQ4_cutTape_eq_source_right
    (L q a b t : Nat) (h x : Int)
    (ha : 0 < a) (hx : h+2 ≤ x) :
    m0EvenEightValuationQ4CutTape L q a b t h x =
      (s1Config L (8*q) 0 a 0 b h).tape x := by
  have hright : h-(3*a:Int)+3 < x := by omega
  have hcut := valuationQ4_cutTape_eq_swept L q a b t h x
    (Or.inr hright)
  have hpres := sweptLeft_preserves_right (3*a)
    (s1Config L (8*q) 0 a 0 b h).tape h x hx
  exact hcut.trans hpres

private theorem valuationQ4_cutTape_sourceRightCell
    (L q a b t : Nat) (h : Int) (j : Nat)
    (ha : 0 < a) (hj : 1 ≤ j) :
    m0EvenEightValuationQ4CutTape L q a b t h (h+1+(j:Int)) =
      sideBit (s1PhysicalRight b) j := by
  have hx : h+2 ≤ h+1+(j:Int) := by omega
  rw [valuationQ4_cutTape_eq_source_right L q a b t h
    (h+1+(j:Int)) ha hx]
  exact s1Config_right_cell L (8*q) 0 a 0 b h j

private theorem valuationQ4_cutTape_head_true
    (L q a b t : Nat) (h : Int) (ha : 0 < a) :
    m0EvenEightValuationQ4CutTape L q a b t h h = true := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let hN : Int := h-((3*a:Nat):Int)
  by_cases ha1 : a=1
  · subst a
    have hcoord : h-((3*1:Nat):Int)+3=h := by omega
    have hm := valuationQ4_cutTape_markerCells L q 1 b t h
    simpa [hcoord] using hm.1
  · have ha2 : 2 ≤ a := by omega
    have hright : hN+3 < h := by dsimp [hN]; omega
    have hcut := valuationQ4_cutTape_eq_swept L q a b t h h
      (Or.inr hright)
    have hs : sweptLeft (3*a) T h h = true := by
      have hnum : (3*a-2)+2 = 3*a := by omega
      rw [← hnum]
      exact sweptLeft_head (3*a-2) T h
    exact hcut.trans hs

private theorem valuationQ4_cutTape_plus1_true
    (L q a b t : Nat) (h : Int) (ha : 0 < a) :
    m0EvenEightValuationQ4CutTape L q a b t h (h+1) = true := by
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let hN : Int := h-((3*a:Nat):Int)
  have hright : hN+3 < h+1 := by dsimp [hN]; omega
  have hcut := valuationQ4_cutTape_eq_swept L q a b t h (h+1)
    (Or.inr hright)
  have hs : sweptLeft (3*a) T h (h+1) = true := by
    have hnum : (3*a-1)+1 = 3*a := by omega
    simpa [hnum] using sweptLeft_plus1 (3*a-1) T h
  exact hcut.trans hs

private theorem sideBit_false_after_length_local
    (xs : List Bool) (i : Nat) (hi : xs.length ≤ i) :
    sideBit xs i = false := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons x xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by simp at hi; omega
          simpa [sideBit] using ih i hi'

/-- The complete left-facing stream at the all-valuation q4 cut. -/
theorem m0EvenEight_valuation_q4_prefix_leftFacing
    (L q a b u t len : Nat) (h : Int)
    (hL : 4 ≤ L) (hq : 0 < q)
    (hbound : 8*q < 2^L) (ha : 0 < a)
    (hfactor : q = (2*u+1)*2^t)
    (hlen : L = len+1+(t+3)) (hu : u < 2^len)
    (hface :
      s1LeftFacing L (8*q) 0 a 0 =
        d1pow a ++ m0EvenEightValuationSourceSuffix t len u) :
    ∀ i : Nat,
      m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
        sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
  have hpow3 : 2^(t+3) = 8*2^t := by
    calc
      2^(t+3) = 2^t * 2^3 := Nat.pow_add 2 t 3
      _ = 8*2^t := by rw [show (2:Nat)^3 = 8 by decide, Nat.mul_comm]
  have hnum : 8*q = (2*u+1)*2^(t+3) := by
    calc
      8*q = 8*((2*u+1)*2^t) := by rw [hfactor]
      _ = (2*u+1)*(8*2^t) := by
        calc
          8*((2*u+1)*2^t) = (8*(2*u+1))*2^t := by rw [← Nat.mul_assoc]
          _ = ((2*u+1)*8)*2^t := by rw [Nat.mul_comm 8 (2*u+1)]
          _ = (2*u+1)*(8*2^t) := by rw [Nat.mul_assoc]
      _ = (2*u+1)*2^(t+3) := by rw [← hpow3]
  have hbin : binDec L (8*q-1) =
      d0pow (t+3) ++ d1 ++ binDec len u := by
    rw [hlen,hnum]
    exact binDec_sub_one_carryPrefix len u (t+3) hu
  have hExpanded :
      m0EvenEightQ4LeftFacingAll L q a =
        expandedLeftFacing a t len u := by
    unfold m0EvenEightQ4LeftFacingAll expandedLeftFacing
    rw [hbin]
    have hlenD : t+4 = (t+3)+1 := by omega
    rw [hlenD]
    simp [d0pow,List.append_assoc]
  let T := (s1Config L (8*q) 0 a 0 b h).tape
  let hN : Int := h-((3*a:Nat):Int)
  intro i
  by_cases hsmall : i < 3*a-3
  · have hx : hN+3 < h-(i:Int) := by dsimp [hN]; omega
    have hcut := valuationQ4_cutTape_eq_swept L q a b t h
      (h-(i:Int)) (Or.inr hx)
    have hblock := sweptLeft_block (3*a) i T h (by omega)
    have htarget := expanded_prefix_allTrue a t len u i ha (by omega)
    calc
      m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
          sweptLeft (3*a) T h (h-(i:Int)) := hcut
      _ = true := by simpa using hblock
      _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
        rw [hExpanded]
        exact htarget.symm
  · by_cases hmid : i ≤ 3*a+15+3*t
    · let k : Nat := i-(3*a-3)
      have hk : k ≤ 18+3*t := by dsimp [k]; omega
      have hcoord : h-(i:Int) = hN+3-(k:Int) := by
        dsimp [k,hN]
        omega
      by_cases hk0 : k=0
      · have hidx : i=3*a-3 := by dsimp [k] at hk0; omega
        have hactual := valuationQ4_cutTape_markerCells L q a b t h
        have htarget := expanded_prefix_allTrue a t len u (3*a-3)
          ha (by omega)
        calc
          m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
              m0EvenEightValuationQ4CutTape L q a b t h (hN+3) := by
                rw [hcoord,hk0] <;> congr 1 <;> omega
          _ = true := hactual.1
          _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
                rw [hidx,hExpanded]
                exact htarget.symm
      · by_cases hk1 : k=1
        · have hidx : i=3*a-2 := by dsimp [k] at hk1; omega
          have hactual := valuationQ4_cutTape_markerCells L q a b t h
          have htarget := expanded_marker_bit a t len u 0 ha (by omega)
          calc
            m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
                m0EvenEightValuationQ4CutTape L q a b t h (hN+2) := by
                  rw [hcoord,hk1] <;> congr 1 <;> omega
            _ = true := hactual.2.1
            _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
                  rw [hidx,hExpanded]
                  rw [show 3*a-2 = 3*a-2+0 by omega]
                  simpa using htarget.symm
        · by_cases hk2 : k=2
          · have hidx : i=3*a-1 := by dsimp [k] at hk2; omega
            have hactual := valuationQ4_cutTape_markerCells L q a b t h
            have htarget := expanded_marker_bit a t len u 1 ha (by omega)
            calc
              m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
                  m0EvenEightValuationQ4CutTape L q a b t h (hN+1) := by
                    rw [hcoord,hk2] <;> congr 1 <;> omega
              _ = true := hactual.2.2.1
              _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
                    rw [hidx,hExpanded]
                    rw [show 3*a-1 = 3*a-2+1 by omega]
                    simpa using htarget.symm
          · by_cases hk3 : k=3
            · have hidx : i=3*a := by dsimp [k] at hk3; omega
              have hactual := valuationQ4_cutTape_markerCells L q a b t h
              have htarget := expanded_marker_bit a t len u 2 ha (by omega)
              calc
                m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
                    m0EvenEightValuationQ4CutTape L q a b t h hN := by
                      rw [hcoord,hk3] <;> congr 1 <;> omega
                _ = false := hactual.2.2.2
                _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
                      rw [hidx,hExpanded]
                      rw [show 3*a = 3*a-2+2 by omega]
                      simpa using htarget.symm
            · by_cases hk4 : k=4
              · have hidx : i=3*a+1 := by dsimp [k] at hk4; omega
                have hactual := valuationQ4_cutTape_scanBlock L q a b t h
                  (3+t) (by omega)
                have hcoordScan :
                    h-((3*a:Nat):Int)-12-(3*t:Int)+
                      3*((3+t:Nat):Int)+2 =
                    hN-1 := by dsimp [hN]; omega
                have htarget := expanded_marker_bit a t len u 3 ha (by omega)
                calc
                  m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
                      m0EvenEightValuationQ4CutTape L q a b t h (hN-1) := by
                        rw [hcoord,hk4] <;> congr 1 <;> omega
                  _ = true := by
                        rw [← hcoordScan]
                        exact hactual.2.2
                  _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
                        rw [hidx,hExpanded]
                        rw [show 3*a+1 = 3*a-2+3 by omega]
                        simpa using htarget.symm
              · have hk5 : 5 ≤ k := by omega
                let j : Nat := (k-5)/3
                let r : Nat := (k-5)%3
                have hdecomp : k=5+3*j+r := by
                  dsimp [j,r]
                  omega
                have hr : r<3 := by
                  exact Nat.mod_lt _ (by decide)
                have hjbound : j≤t+4 := by
                  dsimp [j,r] at *
                  omega
                have hidx : i=3*a+2+3*j+r := by
                  dsimp [k] at hdecomp
                  omega
                by_cases hjlast : j=t+4
                · have hrcases : r=0 ∨ r=1 := by omega
                  rcases hrcases with hr0 | hr1
                  · have hactual := valuationQ4_cutTape_exitCells L q a b t h
                    have htarget := expanded_d1_bit a t len u 0 ha (by omega)
                    have hcoordExit :
                        hN+3-(k:Int) =
                          h-((3*a:Nat):Int)-14-(3*t:Int) := by
                      rw [hdecomp,hjlast,hr0]
                      dsimp [hN]
                      omega
                    have htarget' :
                        sideBit (m0EvenEightQ4LeftFacingAll L q a) i = true := by
                      have hidx' : i=3*a+14+3*t := by
                        rw [hidx,hjlast,hr0]
                        omega
                      rw [hidx',hExpanded]
                      simpa using htarget
                    calc
                      m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
                          m0EvenEightValuationQ4CutTape L q a b t h
                            (h-((3*a:Nat):Int)-14-(3*t:Int)) := by
                              rw [hcoord,hcoordExit]
                      _ = true := hactual.2.1
                      _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i :=
                        htarget'.symm
                  · have hactual := valuationQ4_cutTape_exitCells L q a b t h
                    have htarget := expanded_d1_bit a t len u 1 ha (by omega)
                    have hcoordExit :
                        hN+3-(k:Int) =
                          h-((3*a:Nat):Int)-14-(3*t:Int)-1 := by
                      rw [hdecomp,hjlast,hr1]
                      dsimp [hN]
                      omega
                    have htarget' :
                        sideBit (m0EvenEightQ4LeftFacingAll L q a) i = true := by
                      have hidx' : i=3*a+15+3*t := by
                        rw [hidx,hjlast,hr1]
                        omega
                      rw [hidx',hExpanded]
                      rw [show 3*a+15+3*t = 3*a+14+3*t+1 by omega]
                      exact htarget
                    calc
                      m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
                          m0EvenEightValuationQ4CutTape L q a b t h
                            (h-((3*a:Nat):Int)-14-(3*t:Int)-1) := by
                              rw [hcoord,hcoordExit]
                      _ = true := hactual.1
                      _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i :=
                        htarget'.symm
                · have hj : j<t+4 := by omega
                  have htarget := expanded_d0_bit a t len u j r ha hj hr
                  have htarget' :
                      sideBit (m0EvenEightQ4LeftFacingAll L q a) i =
                        decide (r=2) := by
                    rw [hidx,hExpanded]
                    exact htarget
                  by_cases hr0 : r=0
                  · let s : Nat := 3+t-j
                    have hs : s<4+t := by dsimp [s]; omega
                    have hactual := valuationQ4_cutTape_scanBlock L q a b t h s hs
                    have hcoordScan :
                        hN+3-(k:Int) =
                          h-((3*a:Nat):Int)-12-(3*t:Int)+3*(s:Int)+1 := by
                      rw [hdecomp,hr0]
                      dsimp [s,hN]
                      omega
                    calc
                      m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
                          m0EvenEightValuationQ4CutTape L q a b t h
                            (h-((3*a:Nat):Int)-12-(3*t:Int)+3*(s:Int)+1) := by
                              rw [hcoord,hcoordScan]
                      _ = false := hactual.2.1
                      _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
                        rw [htarget']
                        simp [hr0]
                  · by_cases hr1 : r=1
                    · let s : Nat := 3+t-j
                      have hs : s<4+t := by dsimp [s]; omega
                      have hactual := valuationQ4_cutTape_scanBlock L q a b t h s hs
                      have hcoordScan :
                          hN+3-(k:Int) =
                            h-((3*a:Nat):Int)-12-(3*t:Int)+3*(s:Int) := by
                        rw [hdecomp,hr1]
                        dsimp [s,hN]
                        omega
                      calc
                        m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
                            m0EvenEightValuationQ4CutTape L q a b t h
                              (h-((3*a:Nat):Int)-12-(3*t:Int)+3*(s:Int)) := by
                                rw [hcoord,hcoordScan]
                        _ = false := hactual.1
                        _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
                          rw [htarget']
                          simp [hr1]
                    · have hr2 : r=2 := by omega
                      by_cases hjlast0 : j=t+3
                      · have hactual := valuationQ4_cutTape_exitCells L q a b t h
                        have htarget' :
                            sideBit (m0EvenEightQ4LeftFacingAll L q a) i = true := by
                          have hidx' : i=3*a+2+3*(t+3)+2 := by
                            rw [hidx,hr2,hjlast0] <;> omega
                          rw [hidx',hExpanded]
                          exact expanded_d0_bit a t len u (t+3) 2 ha
                            (by omega) (by omega)
                        have hcoordExit :
                            hN+3-(k:Int) =
                              h-((3*a:Nat):Int)-14-(3*t:Int)+1 := by
                          rw [hdecomp,hr2,hjlast0]
                          dsimp [hN]
                          omega
                        calc
                          m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
                              m0EvenEightValuationQ4CutTape L q a b t h
                                (h-((3*a:Nat):Int)-14-(3*t:Int)+1) := by
                                  rw [hcoord,hcoordExit]
                          _ = true := hactual.2.2
                          _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i :=
                            htarget'.symm
                      · have hj2 : j≤t+2 := by omega
                        let s : Nat := 2+t-j
                        have hs : s<4+t := by dsimp [s]; omega
                        have hactual := valuationQ4_cutTape_scanBlock L q a b t h s hs
                        have hcoordScan :
                            hN+3-(k:Int) =
                              h-((3*a:Nat):Int)-12-(3*t:Int)+3*(s:Int)+2 := by
                          rw [hdecomp,hr2]
                          dsimp [s,hN]
                          omega
                        calc
                          m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
                              m0EvenEightValuationQ4CutTape L q a b t h
                                (h-((3*a:Nat):Int)-12-(3*t:Int)+3*(s:Int)+2) := by
                                  rw [hcoord,hcoordScan]
                          _ = true := hactual.2.2
                          _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
                            rw [htarget']
                            simp [hr2]
    · by_cases hlast : i=3*a+16+3*t
      · have hcoord : h-(i:Int) =
            h-((3*a:Nat):Int)-14-(3*t:Int)-2 := by omega
        have hcut := valuationQ4_cutTape_eq_swept L q a b t h
          (h-(i:Int)) (Or.inl (by omega))
        have hpres := sweptLeft_preserves_left (3*a) T h
          (h-(i:Int)) (by dsimp [hN]; omega)
        have hcell := s1Config_left_cell L (8*q) 0 a 0 b h i
        rw [hface] at hcell
        rw [sideBit_append_right (d1pow a)
          (m0EvenEightValuationSourceSuffix t len u) i
          (by simp [d1pow_length]; omega)] at hcell
        have hidx : i-3*a = 16+3*t := by omega
        rw [d1pow_length,hidx,sourceSuffix_lastD0_true t len u] at hcell
        have htarget := expanded_d1_bit a t len u 2 ha (by omega)
        calc
          m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
              sweptLeft (3*a) T h (h-(i:Int)) := hcut
          _ = T (h-(i:Int)) := hpres
          _ = true := by simpa [T] using hcell
          _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
                rw [hExpanded]
                rw [hlast,show 3*a+16+3*t = 3*a+14+3*t+2 by omega]
                exact htarget.symm
      · have htail : 3*a+17+3*t ≤ i := by omega
        have hcut := valuationQ4_cutTape_eq_swept L q a b t h
          (h-(i:Int)) (Or.inl (by omega))
        have hpres := sweptLeft_preserves_left (3*a) T h
          (h-(i:Int)) (by dsimp [hN]; omega)
        have hcell := s1Config_left_cell L (8*q) 0 a 0 b h i
        have hequiv := expanded_tail_equiv L q a b u t len i
          hface ha hExpanded htail
        calc
          m0EvenEightValuationQ4CutTape L q a b t h (h-(i:Int)) =
              sweptLeft (3*a) T h (h-(i:Int)) := hcut
          _ = T (h-(i:Int)) := hpres
          _ = sideBit (s1LeftFacing L (8*q) 0 a 0) i := by
                simpa [T] using hcell
          _ = sideBit (m0EvenEightQ4LeftFacingAll L q a) i := hequiv

/-- The complete right-facing q4 guard at the valuation-dependent cut. -/
theorem m0EvenEight_valuation_q4_prefix_rightShape
    (L q a b t : Nat) (h : Int) (ha : 0 < a) :
    BB6Coverage.Agent8Q4Suffix.q4RightShape (m0EvenEightValuationQ4CutTape L q a b t h) h b := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi
    have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hc with h0 | h1 | h2 | h3 | h4
    · subst i
      simpa using valuationQ4_cutTape_head_true L q a b t h ha
    · subst i
      exact valuationQ4_cutTape_plus1_true L q a b t h ha
    · subst i
      have hcell := valuationQ4_cutTape_sourceRightCell
        L q a b t h 1 ha (by omega)
      have hcoord : h+1+(1:Int) = h+2 := by omega
      simpa [hcoord,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hcell
    · subst i
      have hcell := valuationQ4_cutTape_sourceRightCell
        L q a b t h 2 ha (by omega)
      have hcoord : h+1+(2:Int) = h+3 := by omega
      simpa [hcoord,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hcell
    · subst i
      have hcell := valuationQ4_cutTape_sourceRightCell
        L q a b t h 3 ha (by omega)
      have hcoord : h+1+(3:Int) = h+4 := by omega
      simpa [hcoord,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hcell
  · have hcell := valuationQ4_cutTape_sourceRightCell
      L q a b t h 4 ha (by omega)
    have hcoord : h+1+(4:Int) = h+5 := by omega
    simpa [hcoord,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hcell
  · have hcell := valuationQ4_cutTape_sourceRightCell
      L q a b t h 5 ha (by omega)
    have hcoord : h+1+(5:Int) = h+6 := by omega
    simpa [hcoord,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hcell
  · intro i hi
    have hcell := valuationQ4_cutTape_sourceRightCell
      L q a b t h (6+i) ha (by omega)
    have hcoord :
        h+7+(i:Int) = h+1+((6+i:Nat):Int) := by push_cast; omega
    have hside : sideBit (s1PhysicalRight b) (6+i) = true := by
      simp only [s1PhysicalRight,s0PhysicalRight,s0RightFacing]
      rw [sideBit_append_right [false,true,true,true,false,false]
        (d1pow (b+1)) (6+i) (by simp)]
      have hidx : 6+i-6 = i := by omega
      rw [show ([false,true,true,true,false,false] : List Bool).length = 6 by rfl,hidx]
      exact sideBit_d1pow_true (b+1) i (by omega)
    rw [← hcoord,hside] at hcell
    exact hcell
  · intro i hi
    let j : Nat := 9+3*b+i
    have hcell := valuationQ4_cutTape_sourceRightCell
      L q a b t h j ha (by dsimp [j]; omega)
    have hcoord :
        h+10+(3*b:Int)+(i:Int) = h+1+((j:Int)) := by
      dsimp [j]
      push_cast
      omega
    have hlen : (s1PhysicalRight b).length = 9+3*b := by
      simp [s1PhysicalRight,s0PhysicalRight,s0RightFacing,d1pow_length] <;> omega
    have hfalse := sideBit_false_after_length_local
      (s1PhysicalRight b) j (by rw [hlen]; dsimp [j]; omega)
    rw [← hcoord,hfalse] at hcell
    exact hcell

/-- The infinite blank right tail required by the generic q4 suffix. -/
theorem m0EvenEight_valuation_q4_prefix_far_tail
    (L q a b t : Nat) (h : Int) (ha : 0 < a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m0EvenEightValuationQ4CutTape L q a b t h
        (h+1+(i:Int)) = false := by
  intro i hi
  have hcell := valuationQ4_cutTape_sourceRightCell
    L q a b t h i ha (by omega)
  have hlen : (s1PhysicalRight b).length = 9+3*b := by
    simp [s1PhysicalRight,s0PhysicalRight,s0RightFacing,d1pow_length] <;> omega
  have hfalse := sideBit_false_after_length_local
    (s1PhysicalRight b) i (by rw [hlen]; exact hi)
  rw [hfalse] at hcell
  exact hcell

private theorem resetPrefixCost_valuation_factor
    (q a b u t : Nat)
    (hfactor : q=(2*u+1)*2^t) :
    resetPrefixCost 0 (8*q) a b =
      (60+12*a+12*t)+(39+3*b) := by
  have hpow3 : 2^(t+3) = 8*2^t := by
    calc
      2^(t+3) = 2^t * 2^3 := Nat.pow_add 2 t 3
      _ = 8*2^t := by rw [show (2:Nat)^3 = 8 by decide, Nat.mul_comm]
  have hnum : 8*q = (2*u+1)*2^(t+3) := by
    calc
      8*q = 8*((2*u+1)*2^t) := by rw [hfactor]
      _ = (2*u+1)*(8*2^t) := by
        calc
          8*((2*u+1)*2^t) = (8*(2*u+1))*2^t := by rw [← Nat.mul_assoc]
          _ = ((2*u+1)*8)*2^t := by rw [Nat.mul_comm 8 (2*u+1)]
          _ = (2*u+1)*(8*2^t) := by rw [Nat.mul_assoc]
      _ = (2*u+1)*2^(t+3) := by rw [← hpow3]
  have hv2 : v2 (8*q) = t+3 := by
    rw [hnum]
    exact v2_odd_factor u (t+3)
  unfold resetPrefixCost
  rw [hv2]
  omega

/-- Complete q4 reset-prefix composition for every positive q. -/
theorem m0EvenEight_valuation_q4_reset_prefix_source
    (L q a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hq : 0 < q)
    (hbound : 8*q < 2^L) (ha : 0 < a) :
    run tm2 (resetPrefixCost 0 (8*q) a b)
      (s1Config L (8*q) 0 a 0 b h) =
      some (s1Config L (8*q-1) 2 (a+b+1) (2^b-1) 0
        (h+5+(3*b:Int))) := by
  obtain ⟨u,t,len,hfactor,hlen,hu,hface⟩ :=
    s1LeftFacing_8q_all L q a hL hq hbound
  let Tq := m0EvenEightValuationQ4CutTape L q a b t h
  have hface' : s1LeftFacing L (8*q) 0 a 0 = d1pow a ++ m0EvenEightValuationSourceSuffix t len u := by
    simpa [m0EvenEightValuationSourceSuffix,List.append_assoc] using hface
  have hprefix0 := m0EvenEight_valuation_q4_prefix_run_of_leftFacing
    L q a b u t len h hL hq hbound ha hface'
  have hprefix :
      run tm2 (60+12*a+12*t)
        (s1Config L (8*q) 0 a 0 b h) = some ⟨4,h,Tq⟩ := by
    simpa [Tq] using hprefix0
  have hleft0 := m0EvenEight_valuation_q4_prefix_leftFacing
    L q a b u t len h hL hq hbound ha hfactor hlen hu hface'
  have hleft :
      ∀ i : Nat, Tq (h-(i:Int)) =
        sideBit (m0EvenEightQ4LeftFacingAll L q a) i := by
    simpa [Tq] using hleft0
  have hshape0 := m0EvenEight_valuation_q4_prefix_rightShape
    L q a b t h ha
  have hshape : BB6Coverage.Agent8Q4Suffix.q4RightShape Tq h b := by
    simpa [Tq] using hshape0
  have htail0 := m0EvenEight_valuation_q4_prefix_far_tail
    L q a b t h ha
  have htail :
      ∀ i : Nat, 9+3*b ≤ i → Tq (h+1+(i:Int)) = false := by
    simpa [Tq] using htail0
  have happend := m0EvenEightQ4SuffixTargetLeftAllQ L q a b ha
  have hsuffix := q4_suffix_run_to_s1Config
    Tq h b L (8*q-1) 2 (a+b+1) (2^b-1)
    (m0EvenEightQ4LeftFacingAll L q a) hshape htail hleft happend
  have hcost := resetPrefixCost_valuation_factor q a b u t hfactor
  rw [hcost,run_add,hprefix]
  simp only [Option.bind_some]
  simpa [Tq] using hsuffix


#print axioms m0EvenEight_valuation_q4_reset_prefix_source
