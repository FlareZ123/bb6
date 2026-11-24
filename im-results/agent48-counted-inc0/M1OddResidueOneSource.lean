import M1OneQ4Prefix
import S1CountedDrain
import M1OddResidueOneTargetLeft
import M1OddResidueOneHeadBound
import Q4Suffix
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48M1OddResidueOneSource

open BB6Coverage
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent24M1OddQ4Prefix
open BB6Coverage.Agent8CountedReset
open BB6ChampionArithmetic
open BB6Coverage.Agent48FinalRst1
open BB6Coverage.Agent48M1OddResidueOneTargetLeft
open BB6Coverage.Agent48M1OddResidueOneHeadBound
open BB6Coverage.Agent24Q4Endpoint

set_option maxHeartbeats 3000000

def m1OddResidueOneInside (a : Nat) (h : Int) : Int → Bool :=
  fun x => decide (h-((3*a+1:Int))-7 ≤ x)

def m1OddResidueOneCutTape
    (L k a b : Nat) (h : Int) : Int → Bool :=
  (frame (m1OddResidueOneInside a h)
    (s1Config L (8*k+1) 1 a 0 b h).tape
    (⟨4,h+4,m1OneQ4CutTape 3 a b h⟩ : Config)).tape

private def m1OddResidueOneInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ d1 ++ d1

private def m1OddResidueOneTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d1 ++ d1

private def m1OddResidueOneInputBoundary (a : Nat) : List Bool :=
  d1pow a ++ markerWord 1 ++ d0

private def m1OddResidueOneTargetBoundary (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0

private theorem m1OddResidueOne_config_ext_by_fields (c d : Config)
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

/-- The n=8k+1 and n=1 S1 source tapes agree on the half-line read by
the n=1 prefix. Their left words share the complete low-order input prefix;
their right words depend only on b. -/
private theorem m1OddResidueOne_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) :
    ∀ x, m1OddResidueOneInside a h x = true →
      (s1Config L (8*k+1) 1 a 0 b h).tape x =
      (s1Config 3 1 1 a 0 b h).tape x := by
  have hbin3 := binDec_residue1 L k hL hbound
  have hbin33 : binDec 3 1 = d0 ++ d1 ++ d1 := by
    have hh := binDec_residue1 3 0 (by omega) (by decide)
    simpa [binDec_zero,d1pow] using hh
  have hsourceLeft :
      s1LeftFacing L (8*k+1) 1 a 0 =
        m1OddResidueOneInputPrefix a ++
          (binDec (L-3) k ++ lh) := by
    simp [s1LeftFacing,m1OddResidueOneInputPrefix,
      binDec_zero,hbin3,List.append_assoc]
  have hbaseLeft :
      s1LeftFacing 3 1 1 a 0 =
        m1OddResidueOneInputPrefix a ++ lh := by
    simp [s1LeftFacing,m1OddResidueOneInputPrefix,
      binDec_zero,hbin33,List.append_assoc]
  have hprefixLength :
      (m1OddResidueOneInputPrefix a).length = 3*a+15 := by
    simp [m1OddResidueOneInputPrefix,d1pow_length,markerWord,d0,d1]
  intro x hx
  by_cases hleft : x ≤ h
  · let i := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i : Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int) = x := by omega
    have hthreshold : h - ((3*a+1:Int)) - 7 ≤ x := by
      simpa [m1OddResidueOneInside] using hx
    have hi : i ≤ 3*a+8 := by omega
    have hiPrefix : i < (m1OddResidueOneInputPrefix a).length := by
      rw [hprefixLength]
      omega
    have hsrc := s1Config_left_cell L (8*k+1) 1 a 0 b h i
    have hbase := s1Config_left_cell 3 1 1 a 0 b h i
    rw [hcoord] at hsrc hbase
    rw [hsourceLeft] at hsrc
    rw [hbaseLeft] at hbase
    have hsrcBit := sideBit_append_left
      (m1OddResidueOneInputPrefix a) (binDec (L-3) k ++ lh)
      i hiPrefix
    have hbaseBit := sideBit_append_left
      (m1OddResidueOneInputPrefix a) lh i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbase
    exact hsrc.trans hbase.symm
  · let i := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i : Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int) = x := by omega
    have hsrc := s1Config_right_cell L (8*k+1) 1 a 0 b h i
    have hbase := s1Config_right_cell 3 1 1 a 0 b h i
    rw [hcoord] at hsrc hbase
    exact hsrc.trans hbase.symm

/-- Lift the 32+12a source prefix from n=1 to every admissible n=8k+1.
The base n=1 run reads only the common half-line, so the rest of the
general source tape is preserved exactly by run_frame. -/
theorem m1OddResidueOne_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) :
    run tm2 (32+12*a)
      (s1Config L (8*k+1) 1 a 0 b h) =
      some ⟨4,h+4,m1OddResidueOneCutTape L k a b h⟩ := by
  let base : Config := ⟨3,h,(s1Config 3 1 1 a 0 b h).tape⟩
  let background := (s1Config L (8*k+1) 1 a 0 b h).tape
  have hinput := m1OddResidueOne_input_matches L k a b h hL hbound
  have hstart :
      frame (m1OddResidueOneInside a h) background base =
        s1Config L (8*k+1) 1 a 0 b h := by
    apply m1OddResidueOne_config_ext_by_fields
    · rfl
    · rfl
    · funext x
      by_cases hx : m1OddResidueOneInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 32+12*a → ∀ d,
        run tm2 j base = some d →
        m1OddResidueOneInside a h d.head = true := by
    intro j hj d hd
    have hlow := m1OddResidueOne_q4_prefix_head_bound a b h j hj d hd
    simpa [m1OddResidueOneInside] using hlow
  have hlift := run_frame tm2 (m1OddResidueOneInside a h)
    background base (32+12*a) hheads
  rw [hstart] at hlift
  rw [m1One_q4_prefix_run 3 a b h (by omega)] at hlift
  simp only [Option.map_some] at hlift
  simpa [m1OddResidueOneCutTape,background,frame] using hlift

private theorem m1OddResidueOne_cut_eq_base
    (L k a b : Nat) (h x : Int) (hx : h ≤ x) :
    m1OddResidueOneCutTape L k a b h x =
      m1OneQ4CutTape 3 a b h x := by
  have hin : m1OddResidueOneInside a h x = true := by
    simp [m1OddResidueOneInside]
    omega
  simp [m1OddResidueOneCutTape,frame,hin]

private theorem m1OddResidueOne_cut_eq_base_inside
    (L k a b : Nat) (h x : Int)
    (hin : m1OddResidueOneInside a h x = true) :
    m1OddResidueOneCutTape L k a b h x =
      m1OneQ4CutTape 3 a b h x := by
  simp [m1OddResidueOneCutTape,frame,hin]

private theorem m1OddResidueOne_cut_eq_input
    (L k a b : Nat) (h x : Int)
    (hout : m1OddResidueOneInside a h x = false) :
    m1OddResidueOneCutTape L k a b h x =
      (s1Config L (8*k+1) 1 a 0 b h).tape x := by
  simp [m1OddResidueOneCutTape,frame,hout]

private theorem q4RightShape_congr
    (T U : Int → Bool) (h : Int) (b : Nat)
    (heq : ∀ x, h ≤ x → T x = U x)
    (hT : Agent8Q4Suffix.q4RightShape T h b) :
    Agent8Q4Suffix.q4RightShape U h b := by
  unfold Agent8Q4Suffix.q4RightShape at *
  rcases hT with ⟨h0,h5,h6,h67,hzero⟩
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
    exact h67 i hi
  · intro i hi
    rw [← heq (h+10+(3*b:Int)+(i:Int)) (by omega)]
    exact hzero i hi

private theorem sideBit_residue1_eq_residue0_after2
    (tail : List Bool) (i : Nat) (hi : 2 ≤ i) :
    sideBit (d0 ++ d1 ++ d1 ++ tail) i =
      sideBit (d1 ++ d1 ++ d1 ++ tail) i := by
  by_cases hi9 : i < 9
  · have hcases : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases hcases with h2 | h3 | h4 | h5 | h6 | h7 | h8
    all_goals subst i <;> simp [sideBit,d0,d1]
  · have hlen0 : (d0 ++ d1 ++ d1).length = 9 := by simp [d0,d1]
    have hlen1 : (d1 ++ d1 ++ d1).length = 9 := by simp [d0,d1]
    have h0 := sideBit_append_right (d0 ++ d1 ++ d1) tail i
      (by rw [hlen0]; omega)
    have h1 := sideBit_append_right (d1 ++ d1 ++ d1) tail i
      (by rw [hlen1]; omega)
    rw [h0,h1]

private theorem m1OddResidueOne_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) :
    ∀ i : Nat, m1OddResidueOneCutTape L k a b h (h-(i:Int)) =
      sideBit (m1OddResidueOneLeftFacing L k a) i := by
  have hbin3 := binDec_residue1 L k hL hbound
  have hbaseLeft :
      m1OneQ4LeftFacing 3 a =
        m1OddResidueOneTargetPrefix a ++ lh := by
    simp [m1OneQ4LeftFacing,m1OddResidueOneTargetPrefix,
      d1pow,markerWord,d0,d1,List.append_assoc]
  have htargetLeft :
      m1OddResidueOneLeftFacing L k a =
        m1OddResidueOneTargetPrefix a ++
          (binDec (L-3) k ++ lh) := by
    simp [m1OddResidueOneLeftFacing,m1OddResidueOneTargetPrefix,
      List.append_assoc]
  have htargetPrefixLength :
      (m1OddResidueOneTargetPrefix a).length = 3*a+15 := by
    simp [m1OddResidueOneTargetPrefix,d1pow_length,markerWord,d0,d1]
  have hinputLeft :
      s1LeftFacing L (8*k+1) 1 a 0 =
        m1OddResidueOneInputBoundary a ++
          (d0 ++ d1 ++ d1 ++ binDec (L-3) k ++ lh) := by
    simp [s1LeftFacing,m1OddResidueOneInputBoundary,
      binDec_zero,hbin3,List.append_assoc]
  have htargetBoundary :
      m1OddResidueOneLeftFacing L k a =
        m1OddResidueOneTargetBoundary a ++
          (d1 ++ d1 ++ d1 ++ binDec (L-3) k ++ lh) := by
    simp [m1OddResidueOneLeftFacing,m1OddResidueOneTargetBoundary,
      List.append_assoc]
  have hinputBoundaryLength :
      (m1OddResidueOneInputBoundary a).length = 3*a+6 := by
    simp [m1OddResidueOneInputBoundary,d1pow_length,markerWord,d0]
  have htargetBoundaryLength :
      (m1OddResidueOneTargetBoundary a).length = 3*a+6 := by
    simp [m1OddResidueOneTargetBoundary,d1pow_length,markerWord,d0]
  intro i
  by_cases hi : i ≤ 3*a+8
  · have hin : m1OddResidueOneInside a h (h-(i:Int)) = true := by
      simp [m1OddResidueOneInside]
      omega
    rw [m1OddResidueOne_cut_eq_base_inside L k a b h (h-(i:Int)) hin]
    rw [m1One_q4_prefix_leftFacing 3 a b h (by omega) i]
    rw [hbaseLeft,htargetLeft]
    have hbaseBit := sideBit_append_left
      (m1OddResidueOneTargetPrefix a) lh i
      (by rw [htargetPrefixLength]; omega)
    have htargetBit := sideBit_append_left
      (m1OddResidueOneTargetPrefix a) (binDec (L-3) k ++ lh) i
      (by rw [htargetPrefixLength]; omega)
    rw [hbaseBit,htargetBit]
  · have hout : m1OddResidueOneInside a h (h-(i:Int)) = false := by
      simp [m1OddResidueOneInside]
      omega
    rw [m1OddResidueOne_cut_eq_input L k a b h (h-(i:Int)) hout]
    rw [s1Config_left_cell L (8*k+1) 1 a 0 b h i]
    rw [hinputLeft,htargetBoundary]
    have hinputBit := sideBit_append_right
      (m1OddResidueOneInputBoundary a)
      (d0 ++ d1 ++ d1 ++ binDec (L-3) k ++ lh) i
      (by rw [hinputBoundaryLength]; omega)
    have htargetBit := sideBit_append_right
      (m1OddResidueOneTargetBoundary a)
      (d1 ++ d1 ++ d1 ++ binDec (L-3) k ++ lh) i
      (by rw [htargetBoundaryLength]; omega)
    rw [hinputBit,htargetBit]
    apply sideBit_residue1_eq_residue0_after2
    omega

private theorem m1OddResidueOne_rightShape
    (L k a b : Nat) (h : Int) :
    Agent8Q4Suffix.q4RightShape (m1OddResidueOneCutTape L k a b h) h b := by
  apply q4RightShape_congr (m1OneQ4CutTape 3 a b h)
    (m1OddResidueOneCutTape L k a b h) h b
  · intro x hx
    symm
    exact m1OddResidueOne_cut_eq_base L k a b h x hx
  · exact m1One_q4_prefix_rightShape 3 a b h

private theorem m1OddResidueOne_far_tail
    (L k a b : Nat) (h : Int) :
    ∀ i, 9+3*b ≤ i →
      m1OddResidueOneCutTape L k a b h (h+1+(i:Int)) = false := by
  intro i hi
  rw [m1OddResidueOne_cut_eq_base L k a b h
    (h+1+(i:Int)) (by omega)]
  exact m1One_q4_prefix_far_tail 3 a b h i hi

private theorem m1OddResidueOne_target_left
    (L k a b : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+1 < 2^L) :
    s1LeftFacing L (8*k) 0 (a+b+2) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m1OddResidueOneLeftFacing L k a).drop 1 := by
  exact m1OddResidueOneSuffixTargetLeft L k a b hL hbound

/-- A complete source-level m=1 reset prefix for every n=8k+1. The only
specialized simulation reused is the n=1 finite bridge; its arbitrary left
tail is transported by run_frame, and the suffix consumes only the right
counter and the explicitly described left-facing stream. -/
theorem m1OddResidueOne_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) :
    run tm2 (67+12*a+3*b)
      (s1Config L (8*k+1) 1 a 0 b h) =
      some (s1Config L (8*k) 0 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  let T := m1OddResidueOneCutTape L k a b h
  let sourceLeft := m1OddResidueOneLeftFacing L k a
  have hprefix := m1OddResidueOne_q4_prefix_source L k a b h hL hbound
  have hshape := m1OddResidueOne_rightShape L k a b h
  have htail := m1OddResidueOne_far_tail L k a b h
  have hleft := m1OddResidueOne_leftFacing L k a b h hL hbound
  have happend := m1OddResidueOne_target_left L k a b hL hbound
  have hfullSuffix := q4_suffix_run_to_s1Config
    T h b L (8*k) 0 (a+b+2) (2^b-1) sourceLeft
    hshape htail hleft happend
  have hfirst : run tm2 4 ⟨4,h,T⟩ = some ⟨4,h+4,T⟩ := by
    have hlinear : linearRightOnes T h 4 := by
      intro i hi
      exact hshape.1 i (by omega)
    exact E_scan T h 4 hlinear
  have hnum : 39+3*b = 4+(35+3*b) := by omega
  rw [hnum,run_add,hfirst] at hfullSuffix
  simp only [Option.bind_some] at hfullSuffix
  have hnumTotal : 67+12*a+3*b =
      (32+12*a)+(35+3*b) := by omega
  rw [hnumTotal,run_add,hprefix]
  simp only [Option.bind_some]
  exact hfullSuffix

/-- Counted drain closes the full generic residue-one increment. -/
theorem m1OddResidueOne_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 1 (8*k+1) a b)
      (s1Config L (8*k+1) 1 a 0 b h) =
      some (s1Config L (8*k) 0 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hvodd : v2 (8*k+1) = 0 :=
    v2_of_odd (8*k+1) (by omega)
  have hcost : resetPrefixCost 1 (8*k+1) a b =
      67+12*a+3*b := by
    simp [resetPrefixCost,hvodd]
    omega
  have hprefix := m1OddResidueOne_reset_prefix_source
    L k a b h hL hbound
  have hdrainBound := resetDrainBound a b 1 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*k) 0 (a+b+2) b (h+5+3*b)
    (s1Config L (8*k+1) 1 a 0 b h)
    (resetPrefixCost 1 (8*k+1) a b)
    (by simpa [hcost] using hprefix)
    (by simpa [resetDelta] using hdrainBound)
  rw [proposedIncrementCost_decomp 1 (8*k+1) a b,hcost]
  simpa [hcost] using hrun

/-- The symbolic endpoint matches the additive notation used by sectionResult. -/
theorem m1OddResidueOne_counted_increment_source_symbolic
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 1 (8*k+1) a b)
      (s1Config L (8*k+1) 1 a 0 b h) =
      some (s1Config L (8*k) (nextMarker 1)
        (nextExponent 1 a b) 0 (nextRight b) (h+5+3*b)) := by
  simpa [nextMarker,nextExponent,nextRight] using
    m1OddResidueOne_counted_increment_source L k a b h hL hbound ha

#print axioms binDec_residue1
#print axioms binDec_residue0
#print axioms m1OddResidueOne_q4_prefix_source
#print axioms m1OddResidueOne_reset_prefix_source
#print axioms m1OddResidueOne_counted_increment_source
#print axioms m1OddResidueOne_counted_increment_source_symbolic

end BB6Coverage.Agent48M1OddResidueOneSource
