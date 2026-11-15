import M1EvenQ4Suffix
import M1EvenResidueSix
import M1EvenResidueTwoInputFrame
import Lean.Elab.Tactic.Omega

/-!
# Source composition for the m=1, n=8k+2 row

The existing 41-step n=6 q4 bridge already suffices for n=8k+2:
its read/head window is [-9,4], and the two S1 source tapes agree on the
entire half-line read by the prefix.  The newer 40-step residue-two bridge
is therefore not needed for this source theorem.  We lift the existing
n=6 prefix with run_frame, preserve the arbitrary high counter tail, then
reuse the proved q4 suffix and counted drain.
-/

namespace BB6Coverage.Agent48M1EvenResidueTwoSource

open BB6Coverage
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent42M1EvenSuffix
open BB6Coverage.Agent42M1EvenResidueSix
open BB6Coverage.Agent8M1EvenResidueTwoInputFrameGeneral
open BB6Coverage.Agent8CountedReset
open BB6ChampionArithmetic

/-- Convert the source bound into the three-bit quotient bound. -/
private theorem residueTwo_quotient_bound (L k : Nat)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) :
    k < 2^(L-3) := by
  have hpow : 2^L = 8 * 2^(L-3) := by
    rw [show L = (L-3)+3 by omega, Nat.pow_add]
    norm_num
    ring
  rw [hpow] at hbound
  omega

/-- The half-line actually read by the existing n=6 q4 prefix. -/
def m1EvenResidueTwoInside (a : Nat) (h : Int) : Int → Bool :=
  fun x => decide (h-((3*a+1:Int))-9 ≤ x)

/-- The lifted cut retains the n=8k+2 source tail to the left of the
existing n=6 prefix's read window. -/
def m1EvenResidueTwoCutTape
    (L k a b : Nat) (h : Int) : Int → Bool :=
  (frame (m1EvenResidueTwoInside a h)
    (s1Config L (8*k+2) 1 a 0 b h).tape
    (⟨4,h+4,m1EvenQ4CutTape a b h⟩ : Config)).tape

private theorem config_ext_by_fields (c d : Config)
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

/-- The n=8k+2 source and the base n=6 source agree wherever the
44+12a prefix can read.  Their first two low-order counter blocks agree;
the differing third block lies strictly beyond the prefix's left reach. -/
private theorem m1EvenResidueTwo_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) :
    ∀ x, m1EvenResidueTwoInside a h x = true →
      (s1Config L (8*k+2) 1 a 0 b h).tape x =
      (s1Config 3 6 1 a 0 b h).tape x := by
  have hk := residueTwo_quotient_bound L k hL hbound
  have hbin2 := binDec_residue_two L k hL hk
  have hbin36 : binDec 3 6 = d1 ++ d0 ++ d0 := by
    have hh := binDec_residue6 3 0 (by omega) (by decide)
    simpa [binDec_zero,d1pow] using hh
  let P : List Bool := d1pow a ++ markerWord 1 ++ d0 ++ d1 ++ d0
  have hsourceLeft :
      s1LeftFacing L (8*k+2) 1 a 0 =
        P ++ (d1 ++ binDec (L-3) k ++ lh) := by
    simp [s1LeftFacing,binDec_zero,hbin2,P,List.append_assoc]
  have hbaseLeft :
      s1LeftFacing 3 6 1 a 0 = P ++ (d0 ++ lh) := by
    simp [s1LeftFacing,binDec_zero,hbin36,P,List.append_assoc]
  have hprefixLength : P.length = 3*a+12 := by
    simp [P,d1pow_length,markerWord,d0,d1]
  intro x hx
  by_cases hleft : x ≤ h
  · let i : Nat := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i : Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int) = x := by omega
    have hthreshold : h-((3*a+1:Int))-9 ≤ x := by
      simpa [m1EvenResidueTwoInside] using hx
    have hi : i ≤ 3*a+10 := by omega
    have hiPrefix : i < P.length := by
      rw [hprefixLength]
      omega
    have hsrc := s1Config_left_cell L (8*k+2) 1 a 0 b h i
    have hbase := s1Config_left_cell 3 6 1 a 0 b h i
    rw [hcoord] at hsrc hbase
    rw [hsourceLeft] at hsrc
    rw [hbaseLeft] at hbase
    have hsrcBit := sideBit_append_left P
      (d1 ++ binDec (L-3) k ++ lh) i hiPrefix
    have hbaseBit := sideBit_append_left P (d0 ++ lh) i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbase
    exact hsrc.trans hbase.symm
  · let i : Nat := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i : Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int) = x := by omega
    have hsrc := s1Config_right_cell L (8*k+2) 1 a 0 b h i
    have hbase := s1Config_right_cell 3 6 1 a 0 b h i
    rw [hcoord] at hsrc hbase
    exact hsrc.trans hbase.symm

/-- The n=8k+2 q4 prefix is the existing n=6 prefix, framed by the
actual n=8k+2 source on the unread left tail. -/
theorem m1Even_residue2_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) :
    run tm2 (44+12*a)
      (s1Config L (8*k+2) 1 a 0 b h) =
      some ⟨4,h+4,m1EvenResidueTwoCutTape L k a b h⟩ := by
  let base : Config := ⟨3,h,(s1Config 3 6 1 a 0 b h).tape⟩
  let background := (s1Config L (8*k+2) 1 a 0 b h).tape
  have hinput := m1EvenResidueTwo_input_matches L k a b h hL hbound
  have hstart :
      frame (m1EvenResidueTwoInside a h) background base =
        s1Config L (8*k+2) 1 a 0 b h := by
    apply config_ext_by_fields
    · rfl
    · rfl
    · funext x
      by_cases hx : m1EvenResidueTwoInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 44+12*a → ∀ d,
        run tm2 j base = some d →
        m1EvenResidueTwoInside a h d.head = true := by
    intro j hj d hd
    have hd' :
        run tm2 j (s1Config 3 6 1 a 0 b h) = some d := by
      simpa [base] using hd
    have hlow :=
      m1Even_q4_prefix_head_bound a b h j hj d hd'
    simpa [m1EvenResidueTwoInside] using hlow
  have hlift := run_frame tm2 (m1EvenResidueTwoInside a h)
    background base (44+12*a) hheads
  rw [hstart] at hlift
  rw [m1Even_q4_prefix_run a b h] at hlift
  simp only [Option.map_some] at hlift
  simpa [m1EvenResidueTwoCutTape,background] using hlift

/-- Left-facing tape stream after the lifted q4 prefix, before the
generic q4 suffix consumes its first cell. -/
def m1EvenResidueTwoLeftFacing (L k a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ binDec L (8*k+1) ++ lh

private theorem m1EvenResidueTwo_cut_eq_base
    (L k a b : Nat) (h x : Int)
    (hin : m1EvenResidueTwoInside a h x = true) :
    m1EvenResidueTwoCutTape L k a b h x =
      m1EvenQ4CutTape a b h x := by
  simp [m1EvenResidueTwoCutTape,frame,hin]

private theorem m1EvenResidueTwo_cut_eq_input
    (L k a b : Nat) (h x : Int)
    (hout : m1EvenResidueTwoInside a h x = false) :
    m1EvenResidueTwoCutTape L k a b h x =
      (s1Config L (8*k+2) 1 a 0 b h).tape x := by
  simp [m1EvenResidueTwoCutTape,frame,hout]

private theorem sideBit_residue2_eq_residue1_after5
    (tail : List Bool) (j : Nat) (hj : 5 ≤ j) :
    sideBit (d1 ++ d0 ++ d1 ++ tail) j =
      sideBit (d0 ++ d1 ++ d1 ++ tail) j := by
  by_cases hj5 : j = 5
  · subst j
    simp [sideBit,d0,d1]
  · have hj6 : 6 ≤ j := by omega
    calc
      sideBit (d1 ++ d0 ++ d1 ++ tail) j =
          sideBit (d1 ++ tail) (j-6) := by
            exact sideBit_append_right (d1 ++ d0) (d1 ++ tail) j
              (by simp [d0,d1]; omega)
      _ = sideBit (d0 ++ d1 ++ d1 ++ tail) j := by
            symm
            exact sideBit_append_right (d0 ++ d1) (d1 ++ tail) j
              (by simp [d0,d1]; omega)

/-- The q4 cut has exactly the left-facing stream of the n=8k+1
marker-zero successor, including its arbitrary high binary tail. -/
private theorem m1EvenResidueTwo_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) :
    ∀ i, m1EvenResidueTwoCutTape L k a b h (h-(i:Int)) =
      sideBit (m1EvenResidueTwoLeftFacing L k a) i := by
  have hk := residueTwo_quotient_bound L k hL hbound
  have hbound1 : 8*k+1 < 2^L := by omega
  have hbin1 := binDec_residue_one L k hL hk
  have hbin35 : binDec 3 5 = d0 ++ d1 ++ d0 := by
    have hh := binDec_residue5 3 0 (by omega) (by decide)
    simpa [binDec_zero,d1pow] using hh
  let P : List Bool := [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ d0 ++ d1
  let inputBoundary : List Bool := d1pow a ++ markerWord 1 ++ d0
  let targetBoundary : List Bool := [true] ++ d1pow a ++ markerWord 0 ++ d0
  have hbaseLeft :
      m1EvenQ4LeftFacing a = P ++ (d0 ++ lh) := by
    simp [m1EvenQ4LeftFacing,P,hbin35,List.append_assoc]
  have htargetLeft :
      m1EvenResidueTwoLeftFacing L k a =
        P ++ (d1 ++ binDec (L-3) k ++ lh) := by
    simp [m1EvenResidueTwoLeftFacing,s1LeftFacing,binDec_zero,
      hbin1,P,List.append_assoc]
  have hinputLeft :
      s1LeftFacing L (8*k+2) 1 a 0 =
        inputBoundary ++ (d1 ++ d0 ++ d1 ++ binDec (L-3) k ++ lh) := by
    have hbin2 := binDec_residue_two L k hL hk
    simp [s1LeftFacing,binDec_zero,hbin2,inputBoundary,List.append_assoc]
  have hprefixLength : P.length = 3*a+12 := by
    simp [P,d1pow_length,markerWord,d0,d1]
  have hinputBoundaryLength : inputBoundary.length = 3*a+6 := by
    simp [inputBoundary,d1pow_length,markerWord,d0,d1]
  have htargetBoundaryLength : targetBoundary.length = 3*a+6 := by
    simp [targetBoundary,d1pow_length,markerWord,d0,d1]
  intro i
  by_cases hi : i ≤ 3*a+10
  · have hin : m1EvenResidueTwoInside a h (h-(i:Int)) = true := by
      simp [m1EvenResidueTwoInside]
      omega
    rw [m1EvenResidueTwo_cut_eq_base L k a b h (h-(i:Int)) hin]
    rw [m1Even_q4_prefix_leftFacing a b h i]
    rw [hbaseLeft,htargetLeft]
    have hbaseBit := sideBit_append_left P (d0 ++ lh) i
      (by rw [hprefixLength]; omega)
    have htargetBit :=
      sideBit_append_left P (d1 ++ binDec (L-3) k ++ lh) i
        (by rw [hprefixLength]; omega)
    rw [hbaseBit,htargetBit]
  · have hout : m1EvenResidueTwoInside a h (h-(i:Int)) = false := by
      simp [m1EvenResidueTwoInside]
      omega
    rw [m1EvenResidueTwo_cut_eq_input L k a b h (h-(i:Int)) hout]
    rw [s1Config_left_cell L (8*k+2) 1 a 0 b h i]
    rw [hinputLeft,htargetLeft]
    have hinputBit := sideBit_append_right inputBoundary
      (d1 ++ d0 ++ d1 ++ binDec (L-3) k ++ lh) i
      (by rw [hinputBoundaryLength]; omega)
    have htargetBit := sideBit_append_right targetBoundary
      (d0 ++ d1 ++ d1 ++ binDec (L-3) k ++ lh) i
      (by rw [htargetBoundaryLength]; omega)
    rw [hinputBit,htargetBit]
    have hj : 5 ≤ i-(3*a+6) := by omega
    exact sideBit_residue2_eq_residue1_after5
      (binDec (L-3) k ++ lh) (i-(3*a+6)) hj

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

private theorem m1EvenResidueTwo_rightShape
    (L k a b : Nat) (h : Int) :
    q4RightShape (m1EvenResidueTwoCutTape L k a b h) h b := by
  apply q4RightShape_congr (m1EvenQ4CutTape a b h)
    (m1EvenResidueTwoCutTape L k a b h) h b
  · intro x hx
    have hin : m1EvenResidueTwoInside a h x = true := by
      simp [m1EvenResidueTwoInside]
      omega
    symm
    exact m1EvenResidueTwo_cut_eq_base L k a b h x hin
  · exact m1Even_q4_prefix_rightShape a b h

private theorem m1EvenResidueTwo_far_tail
    (L k a b : Nat) (h : Int) :
    ∀ i, 9+3*b ≤ i →
      m1EvenResidueTwoCutTape L k a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hin : m1EvenResidueTwoInside a h (h+1+(i:Int)) = true := by
    simp [m1EvenResidueTwoInside]
    omega
  rw [m1EvenResidueTwo_cut_eq_base L k a b h
    (h+1+(i:Int)) hin]
  exact m1Even_q4_prefix_far_tail a b h i hi

/-- The generic q4 suffix converts the lifted left stream into the exact
n=8k+1 marker-zero successor stream. -/
private theorem m1EvenResidueTwo_target_left
    (L k a b : Nat) :
    s1LeftFacing L (8*k+1) 0 (a+b+2) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m1EvenResidueTwoLeftFacing L k a).drop 1 := by
  unfold s1LeftFacing m1EvenResidueTwoLeftFacing
  rw [binDec_pow2_sub_one]
  rw [d1pow_add_right a 2]
  simp [List.drop,List.append_assoc]

/-- Complete source-level reset prefix for every admissible n=8k+2. -/
theorem m1Even_residue2_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) :
    run tm2 (79+12*a+3*b)
      (s1Config L (8*k+2) 1 a 0 b h) =
      some (s1Config L (8*k+1) 0 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  let T := m1EvenResidueTwoCutTape L k a b h
  let sourceLeft := m1EvenResidueTwoLeftFacing L k a
  have hprefix := m1Even_residue2_q4_prefix_source L k a b h hL hbound
  have hshape := m1EvenResidueTwo_rightShape L k a b h
  have htail := m1EvenResidueTwo_far_tail L k a b h
  have hleft := m1EvenResidueTwo_leftFacing L k a b h hL hbound
  have happend := m1EvenResidueTwo_target_left L k a b
  have hfullSuffix := q4_suffix_run_to_s1Config
    T h b L (8*k+1) 0 (a+b+2) (2^b-1) sourceLeft
    hshape htail hleft happend
  have hfirst := m1EvenQ4First4_at T h hshape.1
  have hnum : 39+3*b = 4+(35+3*b) := by omega
  rw [hnum,run_add,hfirst] at hfullSuffix
  simp only [Option.bind_some] at hfullSuffix
  have hnumTotal : 79+12*a+3*b =
      (44+12*a)+(35+3*b) := by omega
  rw [hnumTotal,run_add,hprefix]
  simp only [Option.bind_some]
  exact hfullSuffix

/-- Attach the geometric all-ones drain and obtain the complete counted
m=1, n=8k+2 increment, with exact original-source step cost. -/
theorem m1Even_residue2_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 1 (8*k+2) a b)
      (s1Config L (8*k+2) 1 a 0 b h) =
      some (s1Config L (8*k+1) 0 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hvodd : v2 (4*k+1) = 0 :=
    v2_of_odd (4*k+1) (by omega)
  have hfactor : 8*k+2 = 2*(4*k+1) := by omega
  have hv : v2 (8*k+2) = 1 := by
    rw [hfactor]
    have hgt : 1 < 2*(4*k+1) := by omega
    have heven : (2*(4*k+1)) % 2 = 0 := by omega
    have hdiv : (2*(4*k+1)) / 2 = 4*k+1 := by omega
    simp [v2,hgt,heven,hdiv,hvodd]
  have hcost : resetPrefixCost 1 (8*k+2) a b =
      79+12*a+3*b := by
    simp [resetPrefixCost,hv]
    omega
  have hprefix := m1Even_residue2_reset_prefix_source
    L k a b h hL hbound
  have hdrainBound := resetDrainBound a b 1 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*k+1) 0 (a+b+2) b (h+5+3*b)
    (s1Config L (8*k+2) 1 a 0 b h)
    (resetPrefixCost 1 (8*k+2) a b)
    (by simpa [hcost] using hprefix)
    (by simpa [resetDelta] using hdrainBound)
  rw [proposedIncrementCost_decomp 1 (8*k+2) a b,hcost]
  exact hrun

#print axioms residueTwo_quotient_bound
#print axioms m1Even_residue2_q4_prefix_source
#print axioms m1Even_residue2_reset_prefix_source
#print axioms m1Even_residue2_counted_increment_source

end BB6Coverage.Agent48M1EvenResidueTwoSource
