import M2EvenSixteenQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# m=2, n=32*k+16: source-exact even reset row

The n=16 base case is the 74-step finite q4 bridge in
M2EvenSixteenQ4Prefix.lean. This module transports that proof across the
common five-block BinDec prefix, then composes the generic q4 suffix and
the counted all-ones drain. The intended root application has k odd-quotient
parameterized by the middle-section residue.
-/

namespace BB6Coverage.Agent41M2EvenResidueSixteen

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent41M2EvenSixteenQ4

/-- Binary decrement prefix for n=32*k+16=(2*k+1)*2^4. -/
theorem binDec_residue16 (L k : Nat)
    (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) :
    binDec L (32*k+16) =
      d1pow 4 ++ d0 ++ binDec (L-5) k := by
  have hpow : 2^L = 32 * 2^(L-5) := by
    calc
      2^L = 2^(L-5+5) := by congr 1 <;> omega
      _ = 2^(L-5) * 2^5 := Nat.pow_add 2 (L-5) 5
      _ = 32 * 2^(L-5) := by norm_num [Nat.mul_comm]
  have hbound' : 32*k+16 < 32*2^(L-5) := by
    rw [← hpow]
    exact hbound
  have hq : k < 2^(L-5) := by omega
  have hlen : (L-5)+1+4 = L := by omega
  have hnum : (2*k+1)*2^4 = 32*k+16 := by norm_num; omega
  rw [← hlen, ← hnum]
  exact binDec_carryPrefix (L-5) k 4 hq

/-- Binary decrement prefix for n-1=32*k+15. -/
theorem binDec_residue15 (L k : Nat)
    (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) :
    binDec L (32*k+15) =
      d0pow 4 ++ d1 ++ binDec (L-5) k := by
  have hpow : 2^L = 32 * 2^(L-5) := by
    calc
      2^L = 2^(L-5+5) := by congr 1 <;> omega
      _ = 2^(L-5) * 2^5 := Nat.pow_add 2 (L-5) 5
      _ = 32 * 2^(L-5) := by norm_num [Nat.mul_comm]
  have hbound' : 32*k+16 < 32*2^(L-5) := by
    rw [← hpow]
    exact hbound
  have hq : k < 2^(L-5) := by omega
  have hlen : (L-5)+1+4 = L := by omega
  have hnum : ((2*k+1)*2^4)-1 = 32*k+15 := by norm_num; omega
  rw [← hlen, ← hnum]
  exact binDec_sub_one_carryPrefix (L-5) k 4 hq

/-- The common low-order input prefix through the fifth BinDec block. -/
def m2EvenResidueSixteenInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 2 ++ d0 ++ d1pow 4 ++ d0

/-- The corresponding common q4 target prefix. -/
def m2EvenResidueSixteenTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 1 ++ d0 ++ d0pow 4 ++ d1

private theorem m2EvenResidueSixteenInputPrefix_length (a : Nat) :
    (m2EvenResidueSixteenInputPrefix a).length = 3*a+22 := by
  simp [m2EvenResidueSixteenInputPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m2EvenResidueSixteenTargetPrefix_length (a : Nat) :
    (m2EvenResidueSixteenTargetPrefix a).length = 3*a+22 := by
  simp [m2EvenResidueSixteenTargetPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m2EvenResidueSixteen_source_base_left (a : Nat) :
    s1LeftFacing 5 16 2 a 0 =
      m2EvenResidueSixteenInputPrefix a ++ lh := by
  simp [s1LeftFacing,binDec_zero,binDec_five_sixteen,
    m2EvenResidueSixteenInputPrefix,List.append_assoc]

private theorem m2EvenResidueSixteen_source_left
    (L k a : Nat) (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) :
    s1LeftFacing L (32*k+16) 2 a 0 =
      m2EvenResidueSixteenInputPrefix a ++
        (binDec (L-5) k ++ lh) := by
  simp [s1LeftFacing,m2EvenResidueSixteenInputPrefix,
    binDec_residue16 L k hL hbound,List.append_assoc]

private theorem m2EvenResidueSixteen_target_base_left (a : Nat) :
    q4LeftFacing 5 15 a =
      m2EvenResidueSixteenTargetPrefix a ++ lh := by
  simp [q4LeftFacing,m2EvenResidueSixteenTargetPrefix,
    binDec_five_fifteen,List.append_assoc]

private theorem m2EvenResidueSixteen_target_left
    (L k a : Nat) (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) :
    q4LeftFacing L (32*k+15) a =
      m2EvenResidueSixteenTargetPrefix a ++
        (binDec (L-5) k ++ lh) := by
  simp [q4LeftFacing,m2EvenResidueSixteenTargetPrefix,
    binDec_residue15 L k hL hbound,List.append_assoc]

/-- The frame begins one cell farther left than the maximal read head,
so the full common 3*a+22-cell source prefix is inside it. -/
def m2EvenResidueSixteenInside (a : Nat) (h : Int) : Int → Bool :=
  fun x => decide (h-((3*a+2:Int))-19 ≤ x)

def m2EvenResidueSixteenCutTape
    (L k a b : Nat) (h : Int) : Int → Bool :=
  (frame (m2EvenResidueSixteenInside a h)
    (s1Config L (32*k+16) 2 a 0 b h).tape
    (⟨4,h,m2EvenSixteenQ4CutTape a b h⟩ : Config)).tape

private theorem m2EvenResidueSixteen_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) :
    ∀ x, m2EvenResidueSixteenInside a h x = true →
      (s1Config L (32*k+16) 2 a 0 b h).tape x =
      (s1Config 5 16 2 a 0 b h).tape x := by
  have hsourceLeft :=
    m2EvenResidueSixteen_source_left L k a hL hbound
  have hbaseLeft := m2EvenResidueSixteen_source_base_left a
  have hprefixLength := m2EvenResidueSixteenInputPrefix_length a
  intro x hx
  by_cases hleft : x ≤ h
  · let i := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i:Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int)=x := by omega
    have hi : i ≤ 3*a+21 := by
      dsimp [i] at *
      simp [m2EvenResidueSixteenInside] at hx
      omega
    have hiPrefix :
        i < (m2EvenResidueSixteenInputPrefix a).length := by
      rw [hprefixLength]
      omega
    have hsrc := s1Config_left_cell L (32*k+16) 2 a 0 b h i
    have hbase := s1Config_left_cell 5 16 2 a 0 b h i
    rw [hcoord] at hsrc hbase
    rw [hsourceLeft] at hsrc
    rw [hbaseLeft] at hbase
    have hsrcBit := sideBit_append_left
      (m2EvenResidueSixteenInputPrefix a) (binDec (L-5) k ++ lh)
      i hiPrefix
    have hbaseBit := sideBit_append_left
      (m2EvenResidueSixteenInputPrefix a) lh i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbase
    exact hsrc.trans hbase.symm
  · let i := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i:Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int)=x := by omega
    have hsrc := s1Config_right_cell L (32*k+16) 2 a 0 b h i
    have hbase := s1Config_right_cell 5 16 2 a 0 b h i
    rw [hcoord] at hsrc hbase
    exact hsrc.trans hbase.symm

private theorem m2EvenResidueSixteen_cut_eq_base
    (L k a b : Nat) (h x : Int)
    (hin : m2EvenResidueSixteenInside a h x = true) :
    m2EvenResidueSixteenCutTape L k a b h x =
      m2EvenSixteenQ4CutTape a b h x := by
  simp [m2EvenResidueSixteenCutTape,frame,hin]

private theorem m2EvenResidueSixteen_cut_eq_input
    (L k a b : Nat) (h x : Int)
    (hout : m2EvenResidueSixteenInside a h x = false) :
    m2EvenResidueSixteenCutTape L k a b h x =
      (s1Config L (32*k+16) 2 a 0 b h).tape x := by
  simp [m2EvenResidueSixteenCutTape,frame,hout]

private theorem m2EvenResidueSixteen_q4RightShape_congr
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

/-- The generalized q4 left-facing word after the n=32*k+16 bridge. -/
def m2EvenResidueSixteenLeftFacing (L k a : Nat) : List Bool :=
  q4LeftFacing L (32*k+15) a

private theorem m2EvenResidueSixteen_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m2EvenResidueSixteenCutTape L k a b h (h-(i:Int)) =
        sideBit (m2EvenResidueSixteenLeftFacing L k a) i := by
  have hsourceLeft :=
    m2EvenResidueSixteen_source_left L k a hL hbound
  have htargetLeft :=
    m2EvenResidueSixteen_target_left L k a hL hbound
  have hbaseTarget :=
    m2EvenResidueSixteen_target_base_left a
  have hbaseFace :
      m2EvenSixteenQ4LeftFacing a = q4LeftFacing 5 15 a := by
    simp [m2EvenSixteenQ4LeftFacing,m2EvenSixteenQ4LeftSuffix,
      q4LeftFacing,List.append_assoc]
  have hprefixLength :=
    m2EvenResidueSixteenTargetPrefix_length a
  have hinputLength :=
    m2EvenResidueSixteenInputPrefix_length a
  have hbaseLeft : ∀ i : Nat,
      m2EvenSixteenQ4CutTape a b h (h-(i:Int)) =
        sideBit (m2EvenSixteenQ4LeftFacing a) i := by
    obtain ⟨Tq,_,hleft,_,_⟩ := m2EvenSixteen_q4_prefix_data a b h ha
    have hTq : Tq = m2EvenSixteenQ4CutTape a b h := by rfl
    simpa [hTq] using hleft
  intro i
  by_cases hi : i ≤ 3*a+21
  · have hin :
      m2EvenResidueSixteenInside a h (h-(i:Int)) = true := by
      simp [m2EvenResidueSixteenInside]
      omega
    rw [m2EvenResidueSixteen_cut_eq_base L k a b h
      (h-(i:Int)) hin]
    rw [hbaseLeft i,hbaseFace]
    have hbaseBit :
        sideBit (q4LeftFacing 5 15 a) i =
          sideBit (m2EvenResidueSixteenTargetPrefix a) i := by
      rw [hbaseTarget]
      exact sideBit_append_left (m2EvenResidueSixteenTargetPrefix a)
        lh i (by rw [hprefixLength]; omega)
    have htargetBit :
        sideBit (q4LeftFacing L (32*k+15) a) i =
          sideBit (m2EvenResidueSixteenTargetPrefix a) i := by
      rw [htargetLeft]
      exact sideBit_append_left (m2EvenResidueSixteenTargetPrefix a)
        (binDec (L-5) k ++ lh) i (by rw [hprefixLength]; omega)
    exact hbaseBit.trans htargetBit.symm
  · have hout :
      m2EvenResidueSixteenInside a h (h-(i:Int)) = false := by
      simp [m2EvenResidueSixteenInside]
      omega
    rw [m2EvenResidueSixteen_cut_eq_input L k a b h
      (h-(i:Int)) hout]
    have hcell := s1Config_left_cell L (32*k+16) 2 a 0 b h i
    rw [hsourceLeft] at hcell
    rw [m2EvenResidueSixteenLeftFacing,htargetLeft]
    have hsrcBit := sideBit_append_right
      (m2EvenResidueSixteenInputPrefix a)
      (binDec (L-5) k ++ lh) i
      (by rw [hinputLength]; omega)
    have htgtBit := sideBit_append_right
      (m2EvenResidueSixteenTargetPrefix a)
      (binDec (L-5) k ++ lh) i
      (by rw [hprefixLength]; omega)
    rw [hsrcBit] at hcell
    rw [htgtBit]
    exact hcell

private theorem m2EvenResidueSixteen_rightFacing
    (L k a b : Nat) (h : Int)
    (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m2EvenResidueSixteenCutTape L k a b h (h+1+(i:Int)) =
        sideBit (q4RightFacing b) i := by
  intro i
  have hbase :
      m2EvenSixteenQ4CutTape a b h (h+1+(i:Int)) =
        sideBit (q4RightFacing b) i := by
    obtain ⟨Tq,_,_,_,hright⟩ := m2EvenSixteen_q4_prefix_data a b h ha
    have hTq : Tq = m2EvenSixteenQ4CutTape a b h := by rfl
    simpa [hTq] using hright i
  have hin :
      m2EvenResidueSixteenInside a h (h+1+(i:Int)) = true := by
    simp [m2EvenResidueSixteenInside]
    omega
  rw [m2EvenResidueSixteen_cut_eq_base L k a b h
    (h+1+(i:Int)) hin]
  exact hbase

private theorem m2EvenResidueSixteen_prefix_rightShape
    (L k a b : Nat) (h : Int)
    (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) (ha : 0<a) :
    q4RightShape (m2EvenResidueSixteenCutTape L k a b h) h b := by
  apply m2EvenResidueSixteen_q4RightShape_congr
    (m2EvenSixteenQ4CutTape a b h)
    (m2EvenResidueSixteenCutTape L k a b h) h b
  · intro x hx
    have hin : m2EvenResidueSixteenInside a h x = true := by
      simp [m2EvenResidueSixteenInside]
      omega
    exact (m2EvenResidueSixteen_cut_eq_base L k a b h x hin).symm
  · obtain ⟨Tq,_,_,hshape,_⟩ := m2EvenSixteen_q4_prefix_data a b h ha
    have hTq : Tq = m2EvenSixteenQ4CutTape a b h := by rfl
    simpa [hTq] using hshape

/-- The generalized source prefix for every admissible n=32*k+16. -/
theorem m2Even_residue16_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) (ha : 0<a) :
    run tm2 (80+12*a)
      (s1Config L (32*k+16) 2 a 0 b h) =
      some ⟨4,h,m2EvenResidueSixteenCutTape L k a b h⟩ := by
  let base : Config := ⟨3,h,(s1Config 5 16 2 a 0 b h).tape⟩
  let background := (s1Config L (32*k+16) 2 a 0 b h).tape
  have hinput := m2EvenResidueSixteen_input_matches L k a b h hL hbound
  have hstart :
      frame (m2EvenResidueSixteenInside a h) background base =
        s1Config L (32*k+16) 2 a 0 b h := by
    apply config_ext
    · rfl
    · rfl
    · funext x
      by_cases hx : m2EvenResidueSixteenInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 80+12*a → ∀ d,
        run tm2 j base = some d →
        m2EvenResidueSixteenInside a h d.head = true := by
    intro j hj d hd
    have hlow := m2EvenSixteen_q4_prefix_head_bound a b h j hj d hd
    have hweaker :
        h-((3*a+2:Int))-19 ≤ d.head := by omega
    simpa [m2EvenResidueSixteenInside] using hweaker
  have hlift := run_frame tm2 (m2EvenResidueSixteenInside a h)
    background base (80+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (80+12*a) base =
        some (⟨4,h,m2EvenSixteenQ4CutTape a b h⟩ : Config) := by
    obtain ⟨Tq,hprefix,_,_,_⟩ := m2EvenSixteen_q4_prefix_data a b h ha
    have hTq : Tq = m2EvenSixteenQ4CutTape a b h := by rfl
    simpa [base,hTq] using hprefix
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  simpa [m2EvenResidueSixteenCutTape,background] using hlift

/-- The generalized prefix provides the complete q4 suffix interface. -/
theorem m2Even_residue16_q4_prefix_data
    (L k a b : Nat) (h : Int)
    (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) (ha : 0<a) :
    ∃ Tq,
      run tm2 (80+12*a) (s1Config L (32*k+16) 2 a 0 b h) =
        some ⟨4,h,Tq⟩ ∧
      (∀ i : Nat,
        Tq (h-(i:Int)) =
          sideBit (q4LeftFacing L (32*k+15) a) i) ∧
      q4RightShape Tq h b ∧
      (∀ i : Nat,
        Tq (h+1+(i:Int)) = sideBit (q4RightFacing b) i) := by
  refine ⟨m2EvenResidueSixteenCutTape L k a b h, ?_, ?_, ?_, ?_⟩
  · exact m2Even_residue16_q4_prefix_source L k a b h hL hbound ha
  · exact m2EvenResidueSixteen_leftFacing L k a b h hL hbound ha
  · exact m2EvenResidueSixteen_prefix_rightShape L k a b h hL hbound ha
  · exact m2EvenResidueSixteen_rightFacing L k a b h hL hbound ha

private theorem m2EvenResidueSixteen_prefix_far_tail
    (L k a b : Nat) (h : Int)
    (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) (ha : 0<a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m2EvenResidueSixteenCutTape L k a b h (h+1+(i:Int)) = false := by
  intro i hi
  rw [m2EvenResidueSixteen_rightFacing L k a b h hL hbound ha i]
  apply sideBit_ge_length
  rw [q4RightFacing_length]
  omega

/-- Full source-level Rst2 reset prefix for every admissible n=32*k+16. -/
theorem m2Even_residue16_q4_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 2 (32*k+16) a b)
      (s1Config L (32*k+16) 2 a 0 b h) =
      some (s1Config L (32*k+15) 1 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  obtain ⟨Tq,hprefix,hleft,hshape,hright⟩ :=
    m2Even_residue16_q4_prefix_data L k a b h hL hbound ha
  have htail : ∀ i : Nat, 9+3*b ≤ i →
      Tq (h+1+(i:Int)) = false := by
    intro i hi
    rw [hright i]
    apply sideBit_ge_length
    rw [q4RightFacing_length]
    omega
  have happend := q4SuffixTargetLeft L (32*k+15) a b
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    L (32*k+15) 1 (a+b+2) (2^b-1)
    (q4LeftFacing L (32*k+15) a)
    hshape htail hleft happend
  have hsum :
      resetPrefixCost 2 (32*k+16) a b = (80+12*a)+(39+3*b) := by
    have hv : v2 (32*k+16) = 4 := by
      exact v2_of_odd_factorization (32*k+16) (2*k) 4 (by omega)
    simp [resetPrefixCost,hv]
    omega
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

/-- Complete source-level m=2 increment for every n=32*k+16. -/
theorem m2Even_residue16_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 5 ≤ L) (hbound : 32*k+16 < 2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 2 (32*k+16) a b)
      (s1Config L (32*k+16) 2 a 0 b h) =
      some (s1Config L (32*k+15) 1 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m2Even_residue16_q4_reset_prefix_source
    L k a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 2 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (32*k+15) 1 (a+b+2) b (h+5+3*b)
    (s1Config L (32*k+16) 2 a 0 b h)
    (resetPrefixCost 2 (32*k+16) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms binDec_residue16
#print axioms binDec_residue15
#print axioms m2Even_residue16_q4_prefix_source
#print axioms m2Even_residue16_q4_reset_prefix_source
#print axioms m2Even_residue16_counted_increment_source

end BB6Coverage.Agent41M2EvenResidueSixteen
