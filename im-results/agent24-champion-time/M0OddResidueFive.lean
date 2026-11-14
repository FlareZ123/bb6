import M0OddQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# Uniform m=0, n = 8*k+5 source reset prefix

The finite q4 bridge is independent of the high-order input-counter tail.
This module lifts the checked L=3,n=5 source prefix to every admissible
n=8*k+5 by a half-line frame, then composes the generic q4 suffix and the
proved counted drain.  The result remains an intermediate source theorem;
it is not a complete BB(6) itinerary.
-/

namespace BB6Coverage.Agent24M0OddResidueFive

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent24M0OddQ4Prefix
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

/-- The low three bits of every admissible n=8*k+5. -/
theorem binDec_residue5 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+5 < 2^L) :
    binDec L (8*k+5) = d0 ++ d1 ++ d0 ++ binDec (L-3) k := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    rw [show L = (L-3)+3 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    rw [show L-1 = (L-3)+2 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    rw [show L-2 = (L-3)+1 by omega, Nat.pow_add]
    norm_num
    ring
  have hk : k < 2^(L-3) := by
    rw [hpow3] at hbound
    omega
  have hq1 : 4*k+2 < 2^(L-1) := by
    rw [hpow2]
    omega
  have hq2 : 2*k+1 < 2^(L-2) := by
    rw [hpow1]
    omega
  have h1 : binDec L (8*k+5) =
      d0 ++ binDec (L-1) (4*k+2) := by
    rw [show L = (L-1)+1 by omega,
      show 8*k+5 = 2*(4*k+2)+1 by omega]
    exact binDec_odd (L-1) (4*k+2) hq1
  have h2 : binDec (L-1) (4*k+2) =
      d1 ++ binDec (L-2) (2*k+1) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*k+2 = 2*(2*k+1) by omega]
    exact binDec_even (L-2) (2*k+1) hq2
  have h3 : binDec (L-2) (2*k+1) =
      d0 ++ binDec (L-3) k := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_odd (L-3) k hk
  rw [h1,h2,h3]
  simp [List.append_assoc]

/-- The low three bits of the target n-1=8*k+4. -/
theorem binDec_residue4 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+4 < 2^L) :
    binDec L (8*k+4) = d1 ++ d1 ++ d0 ++ binDec (L-3) k := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    rw [show L = (L-3)+3 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    rw [show L-1 = (L-3)+2 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    rw [show L-2 = (L-3)+1 by omega, Nat.pow_add]
    norm_num
    ring
  have hk : k < 2^(L-3) := by
    rw [hpow3] at hbound
    omega
  have hq1 : 4*k+2 < 2^(L-1) := by
    rw [hpow2]
    omega
  have hq2 : 2*k+1 < 2^(L-2) := by
    rw [hpow1]
    omega
  have h1 : binDec L (8*k+4) =
      d1 ++ binDec (L-1) (4*k+2) := by
    rw [show L = (L-1)+1 by omega,
      show 8*k+4 = 2*(4*k+2) by omega]
    exact binDec_even (L-1) (4*k+2) hq1
  have h2 : binDec (L-1) (4*k+2) =
      d1 ++ binDec (L-2) (2*k+1) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*k+2 = 2*(2*k+1) by omega]
    exact binDec_even (L-2) (2*k+1) hq2
  have h3 : binDec (L-2) (2*k+1) =
      d0 ++ binDec (L-3) k := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_odd (L-3) k hk
  rw [h1,h2,h3]
  simp [List.append_assoc]

private def m0OddResidueFiveSourceHeadPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 0 ++ d0

private def m0OddResidueFiveTargetHeadPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0

private def m0OddResidueFiveInputPrefix (a : Nat) : List Bool :=
  m0OddResidueFiveSourceHeadPrefix a ++ d0 ++ d1 ++ d0

private def m0OddResidueFiveTargetPrefix (a : Nat) : List Bool :=
  m0OddResidueFiveTargetHeadPrefix a ++ d1 ++ d1 ++ d0

/-- The q4 cut's complete left-facing word, including the arbitrary
higher-order tail shared by the source and target encodings. -/
def m0OddResidueFiveLeftFacing (L k a : Nat) : List Bool :=
  m0OddResidueFiveTargetPrefix a ++ (binDec (L-3) k ++ lh)

private theorem m0OddResidueFive_sourceHeadPrefix_length (a : Nat) :
    (m0OddResidueFiveSourceHeadPrefix a).length = 3*a+5 := by
  simp [m0OddResidueFiveSourceHeadPrefix,d1pow_length,markerWord,d0]
  omega

private theorem m0OddResidueFive_targetHeadPrefix_length (a : Nat) :
    (m0OddResidueFiveTargetHeadPrefix a).length = 3*a+5 := by
  simp [m0OddResidueFiveTargetHeadPrefix,d1pow_length,markerWord,d0]
  omega

private theorem m0OddResidueFive_inputPrefix_length (a : Nat) :
    (m0OddResidueFiveInputPrefix a).length = 3*a+14 := by
  simp [m0OddResidueFiveInputPrefix,m0OddResidueFiveSourceHeadPrefix,
    d1pow_length,markerWord,d0,d1]
  omega

private theorem m0OddResidueFive_targetPrefix_length (a : Nat) :
    (m0OddResidueFiveTargetPrefix a).length = 3*a+14 := by
  simp [m0OddResidueFiveTargetPrefix,m0OddResidueFiveTargetHeadPrefix,
    d1pow_length,markerWord,d0,d1]
  omega

private theorem m0OddResidueFive_source_left
    (L k a : Nat) (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L) :
    s1LeftFacing L (8*k+5) 0 a 0 =
      m0OddResidueFiveSourceHeadPrefix a ++
        (d0 ++ d1 ++ d0 ++ binDec (L-3) k ++ lh) := by
  have hbin := binDec_residue5 L k hL hbound
  simp [s1LeftFacing,m0OddResidueFiveSourceHeadPrefix,
    hbin,binDec_zero,List.append_assoc]

private theorem m0OddResidueFive_input_left
    (L k a : Nat) (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L) :
    s1LeftFacing L (8*k+5) 0 a 0 =
      m0OddResidueFiveInputPrefix a ++ (binDec (L-3) k ++ lh) := by
  have hsrc := m0OddResidueFive_source_left L k a hL hbound
  unfold m0OddResidueFiveInputPrefix m0OddResidueFiveSourceHeadPrefix
  rw [hsrc]
  simp [List.append_assoc]

private theorem m0OddResidueFive_base_input_left (a : Nat) :
    s1LeftFacing 3 5 0 a 0 =
      m0OddResidueFiveInputPrefix a ++ lh := by
  have hbin := binDec_residue5 3 0 (by omega) (by decide)
  have hsrc := m0OddResidueFive_source_left 3 0 a (by omega) (by decide)
  simpa [m0OddResidueFiveInputPrefix,
    m0OddResidueFiveSourceHeadPrefix,binDec_zero,List.append_assoc] using hsrc

private theorem m0OddResidueFive_base_q4_leftFacing (a : Nat) :
    m0OddQ4LeftFacing a = m0OddResidueFiveTargetPrefix a ++ lh := by
  have hbin := binDec_residue4 3 0 (by omega) (by decide)
  simp [m0OddQ4LeftFacing,m0OddResidueFiveTargetPrefix,
    m0OddResidueFiveTargetHeadPrefix,hbin,binDec_zero,List.append_assoc]

private theorem m0OddResidueFive_target_tail
    (L k a : Nat) (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L) :
    m0OddResidueFiveLeftFacing L k a =
      m0OddResidueFiveTargetHeadPrefix a ++
        (d1 ++ d1 ++ d0 ++ binDec (L-3) k ++ lh) := by
  have hbin := binDec_residue4 L k hL (by omega)
  simp [m0OddResidueFiveLeftFacing,m0OddResidueFiveTargetPrefix,
    m0OddResidueFiveTargetHeadPrefix,hbin,List.append_assoc]

private theorem sideBit_append_after_local (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) :=
  Agent6Q4Prefix.sideBit_append_right xs ys i hi

private theorem m0OddResidueFive_tail_bits (tail : List Bool) (j : Nat)
    (hj : 2 ≤ j) :
    sideBit (d0 ++ d1 ++ d0 ++ tail) j =
      sideBit (d1 ++ d1 ++ d0 ++ tail) j := by
  by_cases hj2 : j = 2
  · subst j
    simp [d0,d1,sideBit]
  · have hj3 : 3 ≤ j := by omega
    have hs := sideBit_append_after_local d0 (d1 ++ d0 ++ tail) j
      (by simp [d0]; omega)
    have ht := sideBit_append_after_local d1 (d1 ++ d0 ++ tail) j
      (by simp [d1]; omega)
    simpa [List.append_assoc] using hs.trans ht.symm

private theorem m0OddResidueFive_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L) :
    ∀ x, m0OddResidueFiveInside a h x = true →
      (s1Config L (8*k+5) 0 a 0 b h).tape x =
        (s1Config 3 5 0 a 0 b h).tape x := by
  have hsource := m0OddResidueFive_input_left L k a hL hbound
  have hbase := m0OddResidueFive_base_input_left a
  have hlen := m0OddResidueFive_inputPrefix_length a
  intro x hx
  by_cases hleft : x ≤ h
  · let i : Nat := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i:Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int) = x := by omega
    have hthreshold :
        h-((3*a+13:Int)) ≤ x := by
      simpa [m0OddResidueFiveInside] using hx
    have hi : i ≤ 3*a+13 := by
      dsimp [i]
      omega
    have hiPrefix :
        i < (m0OddResidueFiveInputPrefix a).length := by
      rw [hlen]
      omega
    have hsrc := s1Config_left_cell L (8*k+5) 0 a 0 b h i
    have hbaseCell := s1Config_left_cell 3 5 0 a 0 b h i
    rw [hcoord] at hsrc hbaseCell
    rw [hsource] at hsrc
    rw [hbase] at hbaseCell
    have hsrcBit := Agent6Q4Prefix.sideBit_append_left
      (m0OddResidueFiveInputPrefix a)
      (binDec (L-3) k ++ lh) i hiPrefix
    have hbaseBit := Agent6Q4Prefix.sideBit_append_left
      (m0OddResidueFiveInputPrefix a) lh i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbaseCell
    exact hsrc.trans hbaseCell.symm
  · let i : Nat := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i:Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int) = x := by omega
    have hsrc := s1Config_right_cell L (8*k+5) 0 a 0 b h i
    have hbaseCell := s1Config_right_cell 3 5 0 a 0 b h i
    rw [hcoord] at hsrc hbaseCell
    exact hsrc.trans hbaseCell.symm

/-- The finite half-line read by the base prefix. -/
def m0OddResidueFiveInside (a : Nat) (h x : Int) : Bool :=
  decide (h-((3*a+13:Int)) ≤ x)

/-- The generalized cut retains the arbitrary higher-order source tail. -/
def m0OddResidueFiveCutTape
    (L k a b : Nat) (h : Int) : Int → Bool :=
  (frame (m0OddResidueFiveInside a h)
    (s1Config L (8*k+5) 0 a 0 b h).tape
    (⟨4,h,m0OddQ4CutTape a b h⟩ : Config)).tape

private theorem m0OddResidueFive_config_ext (c d : Config)
    (hstate : c.state = d.state) (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  cases c with
  | mk cs ch ct =>
    cases d with
    | mk ds dh dt =>
      cases hstate
      cases hhead
      cases htape
      rfl

private theorem m0OddResidueFive_cut_eq_base
    (L k a b : Nat) (h x : Int) (hx : h ≤ x) :
    m0OddResidueFiveCutTape L k a b h x =
      m0OddQ4CutTape a b h x := by
  have hin : m0OddResidueFiveInside a h x = true := by
    simp [m0OddResidueFiveInside]
    omega
  simp [m0OddResidueFiveCutTape,frame,hin]

private theorem m0OddResidueFive_cut_eq_input
    (L k a b : Nat) (h x : Int)
    (hout : m0OddResidueFiveInside a h x = false) :
    m0OddResidueFiveCutTape L k a b h x =
      (s1Config L (8*k+5) 0 a 0 b h).tape x := by
  simp [m0OddResidueFiveCutTape,frame,hout]

private theorem q4RightShape_congr
    (T U : Int → Bool) (h : Int) (b : Nat)
    (heq : ∀ x, h ≤ x → T x = U x)
    (hT : q4RightShape T h b) :
    q4RightShape U h b := by
  unfold q4RightShape at *
  rcases hT with ⟨h0,h5,h6,h79,hzero⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi
    rw [← heq (h+(i:Int)) (by omega)]
    exact h0 i hi
  · rw [← heq (h+5) (by omega)]
    exact h5
  · rw [← heq (h+6) (by omega)]
    exact h6
  · intro i hi
    rw [← heq (h+7+(i:Int)) (by omega)]
    exact h79 i hi
  · intro i hi
    rw [← heq (h+10+(3*b:Int)+(i:Int)) (by omega)]
    exact hzero i hi

private theorem m0OddResidueFive_base_leftFacing
    (a : Nat) (i : Nat) :
    sideBit (m0OddQ4LeftFacing a) i =
      sideBit (m0OddResidueFiveTargetPrefix a ++ lh) i := by
  rw [m0OddResidueFive_base_q4_leftFacing]

private theorem m0OddResidueFive_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m0OddResidueFiveCutTape L k a b h (h-(i:Int)) =
        sideBit (m0OddResidueFiveLeftFacing L k a) i := by
  have hbaseLeft : ∀ i : Nat,
      m0OddQ4CutTape a b h (h-(i:Int)) =
        sideBit (m0OddQ4LeftFacing a) i := by
    exact m0Odd_q4_prefix_leftFacing a b h ha
  have hsourceTail := m0OddResidueFive_source_left L k a hL hbound
  have htargetTail := m0OddResidueFive_target_tail L k a hL hbound
  have hsourceLen := m0OddResidueFive_sourceHeadPrefix_length a
  have htargetLen := m0OddResidueFive_targetHeadPrefix_length a
  have hbaseList := m0OddResidueFive_base_q4_leftFacing a
  have htargetPrefixLen := m0OddResidueFive_targetPrefix_length a
  intro i
  by_cases hi : i ≤ 3*a+13
  · have hin :
      m0OddResidueFiveInside a h (h-(i:Int)) = true := by
      simp [m0OddResidueFiveInside]
      omega
    rw [m0OddResidueFive_cut_eq_base L k a b h
      (h-(i:Int)) (by omega)]
    rw [hbaseLeft i]
    have hbaseBit := Agent6Q4Prefix.sideBit_append_left
      (m0OddResidueFiveTargetPrefix a) lh i
      (by rw [htargetPrefixLen]; omega)
    have hgenBit := Agent6Q4Prefix.sideBit_append_left
      (m0OddResidueFiveTargetPrefix a)
      (binDec (L-3) k ++ lh) i
      (by rw [htargetPrefixLen]; omega)
    rw [hbaseList] at hbaseBit
    rw [m0OddResidueFiveLeftFacing] at hgenBit
    calc
      sideBit (m0OddQ4LeftFacing a) i =
          sideBit (m0OddResidueFiveTargetPrefix a) i := hbaseBit
      _ = sideBit (m0OddResidueFiveLeftFacing L k a) i := hgenBit.symm
  · have hout :
      m0OddResidueFiveInside a h (h-(i:Int)) = false := by
      simp [m0OddResidueFiveInside]
      omega
    rw [m0OddResidueFive_cut_eq_input L k a b h
      (h-(i:Int)) hout]
    have hcell := s1Config_left_cell L (8*k+5) 0 a 0 b h i
    rw [hsourceTail] at hcell
    have hs := sideBit_append_after_local
      (m0OddResidueFiveSourceHeadPrefix a)
      (d0 ++ d1 ++ d0 ++ binDec (L-3) k ++ lh) i
      (by rw [hsourceLen]; omega)
    have ht := sideBit_append_after_local
      (m0OddResidueFiveTargetHeadPrefix a)
      (d1 ++ d1 ++ d0 ++ binDec (L-3) k ++ lh) i
      (by rw [htargetLen]; omega)
    rw [hs] at hcell
    rw [ht]
    have hj : 2 ≤ i-(3*a+5) := by
      rw [hsourceLen] at *
      omega
    exact m0OddResidueFive_tail_bits
      (binDec (L-3) k ++ lh) (i-(3*a+5)) hj

private theorem m0OddResidueFive_rightFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m0OddResidueFiveCutTape L k a b h (h+1+(i:Int)) =
        sideBit (q4RightFacing b) i := by
  intro i
  rw [m0OddResidueFive_cut_eq_base L k a b h
    (h+1+(i:Int)) (by omega)]
  exact m0Odd_q4_prefix_rightFacing a b h ha i

private theorem m0OddResidueFive_prefix_rightShape
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L) (ha : 0<a) :
    q4RightShape (m0OddResidueFiveCutTape L k a b h) h b := by
  apply q4RightShape_congr
    (m0OddQ4CutTape a b h)
    (m0OddResidueFiveCutTape L k a b h) h b
  · intro x hx
    exact (m0OddResidueFive_cut_eq_base L k a b h x hx).symm
  · exact m0Odd_q4_prefix_rightShape a b h ha

/-- Every prefix of the base m=0,n=5 source run stays in the finite
half-line used by the generalized frame. -/
private theorem m0Odd_q4_prefix_head_bound
    (a b : Nat) (h : Int) (ha : 0<a) :
    ∀ k, k < 24+12*a → ∀ d,
      run tm2 k (s1Config 3 5 0 a 0 b h) = some d →
      h-((3*a+13:Int)) ≤ d.head := by
  let T := (s1Config 3 5 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m0OddQ4CutTape a b h
  have hleft :
      s1LeftFacing 3 5 0 a 0 =
        d1pow a ++
          (markerWord 0 ++ d0 ++ d0 ++ d1 ++ d0 ++ lh) := by
    have hsrc := m0OddResidueFive_base_input_left a
    simpa [m0OddResidueFiveInputPrefix,
      m0OddResidueFiveSourceHeadPrefix,List.append_assoc] using hsrc
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 5 0 a 0 b h i
    rw [hleft] at hcell
    have hbit := Agent6Q4Prefix.sideBit_append_left
      (d1pow a) (markerWord 0 ++ d0 ++ d0 ++ d1 ++ d0 ++ lh) i
      (by rw [d1pow_length]; omega)
    rw [hbit] at hcell
    exact hcell.trans (sideBit_d1pow_true a i hi)
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 5 0 a 0 b h 0
    simpa [T,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m0OddQ4Bridge_input_match a b h ha
  have hBridge := m0OddQ4Bridge27At T1 hN hmatch
  have hBridge' :
      run tm2 27 ⟨3,hN,T1⟩ =
        some ⟨4,hN+3,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m0OddQ4Bridge27Inside m0OddQ4Bridge27End =
          (⟨4,hN+3,T2⟩ : Config) := by
      apply m0OddResidueFive_config_ext
      · simp [frameAt_state,m0OddQ4Bridge27End]
      · simp [frameAt_head,m0OddQ4Bridge27End] <;> omega
      · rfl
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+3) (3*(a-1)) := by
    intro i hi
    let x : Int := hN+3+(i:Int)
    by_cases hi0 : i=0
    · subst i
      have hrel : x-hN=3 := by dsimp [x]; omega
      have hin : m0OddQ4Bridge27Inside (x-hN)=true := by
        simp [m0OddQ4Bridge27Inside,hrel]
      have hcut := m0OddQ4CutTape_eq_end_inside a b h x hin
      have hmark :
          decide ((x-hN) ∈ m0OddQ4Bridge27End.marked) = true := by
        rw [hrel]
        simp [m0OddQ4Bridge27End]
      simpa [T2,x,hN] using hcut.trans hmark
    · have hrel : x-hN=3+(i:Int) := by dsimp [x]; omega
      have hout : m0OddQ4Bridge27Inside (x-hN)=false := by
        simp [m0OddQ4Bridge27Inside,hrel]
        omega
      have hcut := m0OddQ4CutTape_eq_swept a b h x hout
      let j : Nat := 3*a-3-i
      have hj : j+1 < N := by
        dsimp [j,N]
        omega
      have hblock := sweptLeft_block N j T h hj
      have hcoord : x = h-(j:Int) := by
        dsimp [x,j,N,hN]
        omega
      have hblock' : sweptLeft N T h x = true := by
        rw [hcoord]
        exact hblock
      simpa [T2,x] using hcut.trans hblock'
  intro k hk d hd
  let p1 := 3*N
  let p2 := p1+27
  by_cases hk1 : k < p1
  · have hlow := counted_left_sweep_heads N T h hOn hright k
      (by dsimp [p1]; omega) d hd
    dsimp [hN,N] at *
    omega
  · by_cases hk2 : k < p2
    · let j := k-p1
      have hj : j<27 := by dsimp [j,p1] at *; omega
      have hkEq : k=p1+j := by dsimp [j,p1]; omega
      rw [hkEq,run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      have hlow := m0Odd_bridge_prefix_lower T1 hN hmatch j hj d hd
      dsimp [hN,N] at *
      omega
    · let j := k-p2
      have hj : j<3*(a-1) := by dsimp [j,p2,p1,N] at *; omega
      have hkEq : k=p1+(27+j) := by dsimp [j,p2,p1]; omega
      rw [hkEq,run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      rw [run_add,hBridge'] at hd
      simp only [Option.bind_some] at hd
      have hhead := E_scan_prefix_head T2 (hN+3) (3*(a-1)) hlinear j hj d hd
      dsimp [hN,N] at *
      omega

/-- The generalized q4 prefix is the base L=3,n=5 run framed by its
common readable half-line; the arbitrary high-order tail is untouched. -/
theorem m0Odd_residue5_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L) (ha : 0<a) :
    run tm2 (24+12*a)
      (s1Config L (8*k+5) 0 a 0 b h) =
      some ⟨4,h,m0OddResidueFiveCutTape L k a b h⟩ := by
  let base : Config := ⟨3,h,(s1Config 3 5 0 a 0 b h).tape⟩
  let background := (s1Config L (8*k+5) 0 a 0 b h).tape
  have hinput := m0OddResidueFive_input_matches L k a b h hL hbound
  have hstart :
      frame (m0OddResidueFiveInside a h) background base =
        s1Config L (8*k+5) 0 a 0 b h := by
    apply m0OddResidueFive_config_ext
    · rfl
    · rfl
    · funext x
      by_cases hx : m0OddResidueFiveInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 24+12*a → ∀ d,
        run tm2 j base = some d →
        m0OddResidueFiveInside a h d.head = true := by
    intro j hj d hd
    have hlow := m0Odd_q4_prefix_head_bound a b h ha j hj d hd
    simpa [m0OddResidueFiveInside] using hlow
  have hlift := run_frame tm2 (m0OddResidueFiveInside a h)
    background base (24+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (24+12*a) base =
        some (⟨4,h,m0OddQ4CutTape a b h⟩ : Config) := by
    have hrun := m0Odd_q4_prefix_run a b h ha
    simpa [base] using hrun
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  simpa [m0OddResidueFiveCutTape,background] using hlift

/-- The generalized prefix exposes the complete q4 suffix interface. -/
theorem m0Odd_residue5_q4_prefix_data
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L) (ha : 0<a) :
    ∃ Tq,
      run tm2 (24+12*a) (s1Config L (8*k+5) 0 a 0 b h) =
        some ⟨4,h,Tq⟩ ∧
      (∀ i : Nat, Tq (h-(i:Int)) =
        sideBit (m0OddResidueFiveLeftFacing L k a) i) ∧
      q4RightShape Tq h b ∧
      (∀ i : Nat, Tq (h+1+(i:Int)) =
        sideBit (q4RightFacing b) i) := by
  refine ⟨m0OddResidueFiveCutTape L k a b h, ?_, ?_, ?_, ?_⟩
  · exact m0Odd_residue5_q4_prefix_source L k a b h hL hbound ha
  · exact m0OddResidueFive_leftFacing L k a b h hL hbound ha
  · exact m0OddResidueFive_prefix_rightShape L k a b h hL hbound ha
  · exact m0OddResidueFive_rightFacing L k a b h hL hbound ha

/-- The complete right ray is blank beyond the q4 suffix's finite window. -/
private theorem m0OddResidueFive_prefix_far_tail
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L) (ha : 0<a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m0OddResidueFiveCutTape L k a b h (h+1+(i:Int)) = false := by
  intro i hi
  rw [m0OddResidueFive_rightFacing L k a b h hL hbound ha i]
  apply sideBit_ge_length
  rw [q4RightFacing_length]
  omega

/-- The q4 suffix target is the canonical S1 state for n-1=8*k+4. -/
private theorem m0OddResidueFive_suffix_target_left
    (L k a b : Nat) (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L)
    (ha : 0<a) :
    s1LeftFacing L (8*k+4) 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m0OddResidueFiveLeftFacing L k a).drop 1 := by
  have hbinPow := binDec_pow2_sub_one (a-1) b
  have hlen : a-1+b+2 = a+b+1 := by omega
  have hexp : a-1+2 = a+1 := by omega
  have hbin : binDec (a+b+1) (2^b-1) =
      d0pow b ++ d1pow (a+1) := by
    simpa [hlen,hexp] using hbinPow
  have hbin4 := binDec_residue4 L k hL (by omega)
  unfold s1LeftFacing
  rw [hbin,hbin4]
  rw [← hexp]
  rw [d1pow_add_right (a-1) 2]
  simp [m0OddResidueFiveLeftFacing,m0OddResidueFiveTargetPrefix,
    m0OddResidueFiveTargetHeadPrefix,List.drop,List.append_assoc]

/-- v2(8*k+5)=0, so the prefix cost is the same 63+12a+3b. -/
private theorem m0OddResidueFive_resetPrefixCost_eq (k a b : Nat) :
    resetPrefixCost 0 (8*k+5) a b = 63+12*a+3*b := by
  have hv : v2 (8*k+5) = 0 := by
    exact v2_of_odd (8*k+5) (by omega)
  simp [resetPrefixCost,hv]

/-- Full source-level Rst0 reset prefix for every admissible n=8*k+5. -/
theorem m0Odd_residue5_q4_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 0 (8*k+5) a b)
      (s1Config L (8*k+5) 0 a 0 b h) =
      some (s1Config L (8*k+4) 2 (a+b+1) (2^b-1) 0
        (h+5+3*b)) := by
  obtain ⟨Tq,hprefix,hleft,hshape,hright⟩ :=
    m0Odd_residue5_q4_prefix_data L k a b h hL hbound ha
  have htail : ∀ i : Nat, 9+3*b ≤ i →
      Tq (h+1+(i:Int)) = false := by
    intro i hi
    rw [hright i]
    apply sideBit_ge_length
    rw [q4RightFacing_length]
    omega
  have happend := m0OddResidueFive_suffix_target_left L k a b hL hbound ha
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    L (8*k+4) 2 (a+b+1) (2^b-1)
    (m0OddResidueFiveLeftFacing L k a)
    hshape htail hleft happend
  have hsum :
      resetPrefixCost 0 (8*k+5) a b = (24+12*a)+(39+3*b) := by
    rw [m0OddResidueFive_resetPrefixCost_eq]
    omega
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

/-- Complete original-TM2 m=0 increment for every admissible n=8*k+5,
including the exact geometric all-ones drain. -/
theorem m0Odd_residue5_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+5 < 2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 0 (8*k+5) a b)
      (s1Config L (8*k+5) 0 a 0 b h) =
      some (s1Config L (8*k+4) 2 (a+b+1) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m0Odd_residue5_q4_reset_prefix_source
    L k a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 0 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*k+4) 2 (a+b+1) b (h+5+3*b)
    (s1Config L (8*k+5) 0 a 0 b h)
    (resetPrefixCost 0 (8*k+5) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms binDec_residue5
#print axioms binDec_residue4
#print axioms m0Odd_residue5_q4_prefix_source
#print axioms m0Odd_residue5_q4_reset_prefix_source
#print axioms m0Odd_residue5_counted_increment_source

end BB6Coverage.Agent24M0OddResidueFive
