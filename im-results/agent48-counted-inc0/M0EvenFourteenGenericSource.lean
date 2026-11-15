import M0EvenFourteenQ4Prefix
import M0EvenFourteenHeadBound
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Generic original-table m=0,n=32*k+14 increment

Lift Agent 49's base L=5,n=14 q4 prefix to arbitrary L>=5 and
n=32*k+14.  The frame reads only the first 3*a+10 left-facing cells.
The source and target streams then share the exact tail
[true] ++ d0 ++ d0 ++ d1 ++ binDec (L-5) k ++ lh.
The q4 suffix and counted all-ones drain complete the increment.
-/

namespace BB6Coverage.Agent48M0EvenFourteenGenericSource

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent49M0EvenFourteenQ4Bridge
open BB6Coverage.Agent49M0EvenFourteenQ4Prefix
open BB6Coverage.Agent48M0EvenFourteenHeadBound
open BB6Coverage.Agent48CountedInc0
open BB6ChampionArithmetic

set_option maxHeartbeats 4000000

private def m0EvenFourteenGenericInside (a : Nat) (h : Int) : Int → Bool :=
  fun x => decide (h-((3*a+9:Int)) ≤ x)

private def m0EvenFourteenGenericInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ [false,false]

private def m0EvenFourteenGenericTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ d0 ++ [true,true]

private def m0EvenFourteenGenericCommonTail (L k : Nat) : List Bool :=
  [true] ++ d0 ++ d0 ++ d1 ++ binDec (L-5) k ++ lh

private def m0EvenFourteenGenericInputLeftFacing (L k a : Nat) : List Bool :=
  m0EvenFourteenGenericInputPrefix a ++
    m0EvenFourteenGenericCommonTail L k

def m0EvenFourteenGenericLeftFacing (L k a : Nat) : List Bool :=
  m0EvenFourteenGenericTargetPrefix a ++
    m0EvenFourteenGenericCommonTail L k

def m0EvenFourteenGenericCutTape (L k a b : Nat) (h : Int) : Int → Bool :=
  (frame (m0EvenFourteenGenericInside a h)
    (s1Config L (32*k+14) 0 a 0 b h).tape
    (⟨4,h,m0EvenFourteenQ4CutTape a b h⟩ : Config)).tape

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

private theorem m0EvenFourteen_quotient_bounds
    (L k : Nat) (hL : 5 ≤ L)
    (hbound : 32*k+14 < 2^L) :
    16*k+7 < 2^(L-1) ∧
    8*k+3 < 2^(L-2) ∧
    4*k+1 < 2^(L-3) ∧
    2*k < 2^(L-4) ∧
    k < 2^(L-5) := by
  have hp1 : 2^L = 2*2^(L-1) := by
    rw [show L = (L-1)+1 by omega, Nat.pow_succ]
    omega
  have h1 : 16*k+7 < 2^(L-1) := by
    rw [hp1] at hbound
    omega
  have hp2 : 2^(L-1) = 2*2^(L-2) := by
    rw [show L-1 = (L-2)+1 by omega, Nat.pow_succ]
    omega
  have h2 : 8*k+3 < 2^(L-2) := by
    rw [hp2] at h1
    omega
  have hp3 : 2^(L-2) = 2*2^(L-3) := by
    rw [show L-2 = (L-3)+1 by omega, Nat.pow_succ]
    omega
  have h3 : 4*k+1 < 2^(L-3) := by
    rw [hp3] at h2
    omega
  have hp4 : 2^(L-3) = 2*2^(L-4) := by
    rw [show L-3 = (L-4)+1 by omega, Nat.pow_succ]
    omega
  have h4 : 2*k < 2^(L-4) := by
    rw [hp4] at h3
    omega
  have hp5 : 2^(L-4) = 2*2^(L-5) := by
    rw [show L-4 = (L-5)+1 by omega, Nat.pow_succ]
    omega
  have h5 : k < 2^(L-5) := by
    rw [hp5] at h4
    omega
  exact ⟨h1,h2,h3,h4,h5⟩

private theorem m0EvenFourteen_binDec_source
    (L k : Nat) (hL : 5 ≤ L)
    (hbound : 32*k+14 < 2^L) :
    binDec L (32*k+14) =
      d1 ++ d0 ++ d0 ++ d0 ++ d1 ++ binDec (L-5) k := by
  have hb := m0EvenFourteen_quotient_bounds L k hL hbound
  have h1 : binDec L (32*k+14) =
      d1 ++ binDec (L-1) (16*k+7) := by
    rw [show L = (L-1)+1 by omega]
    exact binDec_even (L-1) (16*k+7) hb.1
  have h2 : binDec (L-1) (16*k+7) =
      d0 ++ binDec (L-2) (8*k+3) := by
    rw [show L-1 = (L-2)+1 by omega]
    exact binDec_odd (L-2) (8*k+3) hb.2.1
  have h3 : binDec (L-2) (8*k+3) =
      d0 ++ binDec (L-3) (4*k+1) := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_odd (L-3) (4*k+1) hb.2.2.1
  have h4 : binDec (L-3) (4*k+1) =
      d0 ++ binDec (L-4) (2*k) := by
    rw [show L-3 = (L-4)+1 by omega]
    exact binDec_odd (L-4) (4*k+1) hb.2.2.2.1
  have h5 : binDec (L-4) (2*k) =
      d1 ++ binDec (L-5) k := by
    rw [show L-4 = (L-5)+1 by omega]
    exact binDec_even (L-5) k hb.2.2.2.2
  simp [h1,h2,h3,h4,h5,List.append_assoc]

private theorem m0EvenFourteen_binDec_target
    (L k : Nat) (hL : 5 ≤ L)
    (hbound : 32*k+14 < 2^L) :
    binDec L (32*k+13) =
      d0 ++ d1 ++ d0 ++ d0 ++ d1 ++ binDec (L-5) k := by
  have hb := m0EvenFourteen_quotient_bounds L k hL hbound
  have h1 : binDec L (32*k+13) =
      d0 ++ binDec (L-1) (16*k+6) := by
    rw [show L = (L-1)+1 by omega]
    exact binDec_odd (L-1) (16*k+6) (by omega)
  have h2 : binDec (L-1) (16*k+6) =
      d1 ++ binDec (L-2) (8*k+3) := by
    rw [show L-1 = (L-2)+1 by omega]
    exact binDec_even (L-2) (8*k+3) hb.2.1
  have h3 : binDec (L-2) (8*k+3) =
      d0 ++ binDec (L-3) (4*k+1) := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_odd (L-3) (4*k+1) hb.2.2.1
  have h4 : binDec (L-3) (4*k+1) =
      d0 ++ binDec (L-4) (2*k) := by
    rw [show L-3 = (L-4)+1 by omega]
    exact binDec_odd (L-4) (4*k+1) hb.2.2.2.1
  have h5 : binDec (L-4) (2*k) =
      d1 ++ binDec (L-5) k := by
    rw [show L-4 = (L-5)+1 by omega]
    exact binDec_even (L-5) k hb.2.2.2.2
  simp [h1,h2,h3,h4,h5,List.append_assoc]

private theorem m0EvenFourteen_sourceLeftFacing
    (L k a : Nat) (hL : 5 ≤ L)
    (hbound : 32*k+14 < 2^L) :
    s1LeftFacing L (32*k+14) 0 a 0 =
      m0EvenFourteenGenericInputLeftFacing L k a := by
  have hbin := m0EvenFourteen_binDec_source L k hL hbound
  simp [s1LeftFacing,m0EvenFourteenGenericInputLeftFacing,
    m0EvenFourteenGenericInputPrefix,m0EvenFourteenGenericCommonTail,
    hbin,binDec_zero,d0,d1,List.append_assoc]

private theorem m0EvenFourteen_baseSourceLeftFacing (a : Nat) :
    s1LeftFacing 5 14 0 a 0 =
      m0EvenFourteenGenericInputPrefix a ++
        ([true] ++ d0 ++ d0 ++ d1 ++ lh) := by
  simp [s1LeftFacing,m0EvenFourteenGenericInputPrefix,
    m0EvenFourteenGenericCommonTail,
    m0EvenFourteen_binDec_five_fourteen,binDec_zero,d0,d1,
    List.append_assoc]

private theorem m0EvenFourteen_baseCutLeftFacing (a : Nat) :
    m0EvenFourteenQ4LeftFacing a =
      m0EvenFourteenGenericTargetPrefix a ++
        ([true] ++ d0 ++ d0 ++ d1 ++ lh) := by
  simp [m0EvenFourteenQ4LeftFacing,m0EvenFourteenGenericTargetPrefix,
    m0EvenFourteen_binDec_five_thirteen,d0,d1,List.append_assoc]

private theorem m0EvenFourteenGeneric_inputPrefix_length (a : Nat) :
    (m0EvenFourteenGenericInputPrefix a).length = 3*a+10 := by
  simp [m0EvenFourteenGenericInputPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m0EvenFourteenGeneric_targetPrefix_length (a : Nat) :
    (m0EvenFourteenGenericTargetPrefix a).length = 3*a+10 := by
  simp [m0EvenFourteenGenericTargetPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m0EvenFourteenGeneric_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 5 ≤ L) (hbound : 32*k+14 < 2^L) :
    ∀ x, m0EvenFourteenGenericInside a h x = true →
      (s1Config L (32*k+14) 0 a 0 b h).tape x =
      (s1Config 5 14 0 a 0 b h).tape x := by
  have hsourceLeft := m0EvenFourteen_sourceLeftFacing L k a hL hbound
  have hbaseLeft := m0EvenFourteen_baseSourceLeftFacing a
  have hprefixLength := m0EvenFourteenGeneric_inputPrefix_length a
  intro x hx
  by_cases hleft : x ≤ h
  · let i : Nat := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i:Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int) = x := by omega
    have hthreshold : h-((3*a+9:Int)) ≤ x := by
      simpa [m0EvenFourteenGenericInside] using hx
    have hi : i ≤ 3*a+9 := by omega
    have hiPrefix :
        i < (m0EvenFourteenGenericInputPrefix a).length := by
      rw [hprefixLength]
      omega
    have hsrc := s1Config_left_cell L (32*k+14) 0 a 0 b h i
    have hbase := s1Config_left_cell 5 14 0 a 0 b h i
    rw [hcoord] at hsrc hbase
    rw [hsourceLeft] at hsrc
    rw [hbaseLeft] at hbase
    have hsrcBit := Agent6Q4Prefix.sideBit_append_left
      (m0EvenFourteenGenericInputPrefix a)
      (m0EvenFourteenGenericCommonTail L k) i hiPrefix
    have hbaseBit := Agent6Q4Prefix.sideBit_append_left
      (m0EvenFourteenGenericInputPrefix a)
      ([true] ++ d0 ++ d0 ++ d1 ++ lh) i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbase
    exact hsrc.trans hbase.symm
  · let i : Nat := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i:Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int) = x := by omega
    have hsrc := s1Config_right_cell L (32*k+14) 0 a 0 b h i
    have hbase := s1Config_right_cell 5 14 0 a 0 b h i
    rw [hcoord] at hsrc hbase
    exact hsrc.trans hbase.symm

/-- Lift the base 36+12a q4 prefix to arbitrary L>=5 and n=32*k+14. -/
theorem m0EvenFourteen_generic_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 5 ≤ L) (hbound : 32*k+14 < 2^L) (ha : 0<a) :
    run tm2 (36+12*a)
      (s1Config L (32*k+14) 0 a 0 b h) =
      some ⟨4,h,m0EvenFourteenGenericCutTape L k a b h⟩ := by
  let base : Config := ⟨3,h,(s1Config 5 14 0 a 0 b h).tape⟩
  let background := (s1Config L (32*k+14) 0 a 0 b h).tape
  have hinput := m0EvenFourteenGeneric_input_matches L k a b h hL hbound
  have hstart :
      frame (m0EvenFourteenGenericInside a h) background base =
        s1Config L (32*k+14) 0 a 0 b h := by
    apply config_ext_by_fields
    · rfl
    · rfl
    · funext x
      by_cases hx : m0EvenFourteenGenericInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 36+12*a → ∀ d,
        run tm2 j base = some d →
        m0EvenFourteenGenericInside a h d.head = true := by
    intro j hj d hd
    have hd' :
        run tm2 j (s1Config 5 14 0 a 0 b h) = some d := by
      simpa [base] using hd
    have hlow :=
      m0EvenFourteen_q4_prefix_head_bound a b h ha j hj d hd'
    simpa [m0EvenFourteenGenericInside] using hlow
  have hlift := run_frame tm2 (m0EvenFourteenGenericInside a h)
    background base (36+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (36+12*a) base =
        some (⟨4,h,m0EvenFourteenQ4CutTape a b h⟩ : Config) := by
    simpa [base] using m0EvenFourteen_q4_prefix_run a b h ha
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  simpa [m0EvenFourteenGenericCutTape,background] using hlift

private theorem m0EvenFourteenGeneric_cut_eq_base_inside
    (L k a b : Nat) (h x : Int)
    (hin : m0EvenFourteenGenericInside a h x = true) :
    m0EvenFourteenGenericCutTape L k a b h x =
      m0EvenFourteenQ4CutTape a b h x := by
  simp [m0EvenFourteenGenericCutTape,frame,hin]

private theorem m0EvenFourteenGeneric_cut_eq_input_outside
    (L k a b : Nat) (h x : Int)
    (hout : m0EvenFourteenGenericInside a h x = false) :
    m0EvenFourteenGenericCutTape L k a b h x =
      (s1Config L (32*k+14) 0 a 0 b h).tape x := by
  simp [m0EvenFourteenGenericCutTape,frame,hout]

/-- Exact generic target left-facing stream at the q4 cut. -/
theorem m0EvenFourteen_generic_q4_prefix_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 5 ≤ L) (hbound : 32*k+14 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m0EvenFourteenGenericCutTape L k a b h (h-(i:Int)) =
        sideBit (m0EvenFourteenGenericLeftFacing L k a) i := by
  have hsourceLeft := m0EvenFourteen_sourceLeftFacing L k a hL hbound
  have hbaseCutLeft := m0EvenFourteen_baseCutLeftFacing a
  have hinputPrefixLength := m0EvenFourteenGeneric_inputPrefix_length a
  have htargetPrefixLength := m0EvenFourteenGeneric_targetPrefix_length a
  intro i
  by_cases hi : i ≤ 3*a+9
  · have hin :
      m0EvenFourteenGenericInside a h (h-(i:Int)) = true := by
      simp [m0EvenFourteenGenericInside]
      omega
    rw [m0EvenFourteenGeneric_cut_eq_base_inside L k a b h
      (h-(i:Int)) hin]
    rw [m0EvenFourteen_q4_prefix_leftFacing a b h ha i]
    rw [hbaseCutLeft]
    simp only [m0EvenFourteenGenericLeftFacing]
    have hbaseBit := Agent6Q4Prefix.sideBit_append_left
      (m0EvenFourteenGenericTargetPrefix a)
      ([true] ++ d0 ++ d0 ++ d1 ++ lh) i
      (by rw [htargetPrefixLength]; omega)
    have htargetBit := Agent6Q4Prefix.sideBit_append_left
      (m0EvenFourteenGenericTargetPrefix a)
      (m0EvenFourteenGenericCommonTail L k) i
      (by rw [htargetPrefixLength]; omega)
    rw [hbaseBit,htargetBit]
  · have hout :
      m0EvenFourteenGenericInside a h (h-(i:Int)) = false := by
      simp [m0EvenFourteenGenericInside]
      omega
    rw [m0EvenFourteenGeneric_cut_eq_input_outside L k a b h
      (h-(i:Int)) hout]
    rw [s1Config_left_cell L (32*k+14) 0 a 0 b h i]
    rw [hsourceLeft]
    simp only [m0EvenFourteenGenericInputLeftFacing,
      m0EvenFourteenGenericLeftFacing]
    have hsourceBit := Agent6Q4Prefix.sideBit_append_right
      (m0EvenFourteenGenericInputPrefix a)
      (m0EvenFourteenGenericCommonTail L k) i
      (by rw [hinputPrefixLength]; omega)
    have htargetBit := Agent6Q4Prefix.sideBit_append_right
      (m0EvenFourteenGenericTargetPrefix a)
      (m0EvenFourteenGenericCommonTail L k) i
      (by rw [htargetPrefixLength]; omega)
    rw [hsourceBit,htargetBit]
    simp [hinputPrefixLength,htargetPrefixLength]

private theorem m0EvenFourteenGeneric_q4RightShape_congr
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

private theorem m0EvenFourteenGeneric_q4_rightShape
    (L k a b : Nat) (h : Int) (ha : 0<a) :
    q4RightShape (m0EvenFourteenGenericCutTape L k a b h) h b := by
  apply m0EvenFourteenGeneric_q4RightShape_congr
    (m0EvenFourteenQ4CutTape a b h)
    (m0EvenFourteenGenericCutTape L k a b h) h b
  · intro x hx
    have hin : m0EvenFourteenGenericInside a h x = true := by
      simp [m0EvenFourteenGenericInside]
      omega
    symm
    exact m0EvenFourteenGeneric_cut_eq_base_inside L k a b h x hin
  · exact m0EvenFourteen_q4_prefix_rightShape a b h ha

private theorem m0EvenFourteenGeneric_q4_far_tail
    (L k a b : Nat) (h : Int) (ha : 0<a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m0EvenFourteenGenericCutTape L k a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hin :
      m0EvenFourteenGenericInside a h (h+1+(i:Int)) = true := by
    simp [m0EvenFourteenGenericInside]
    omega
  rw [m0EvenFourteenGeneric_cut_eq_base_inside L k a b h
    (h+1+(i:Int)) hin]
  exact m0EvenFourteen_q4_prefix_far_tail a b h ha i hi

private theorem m0EvenFourteenGeneric_suffix_target_left
    (L k a b : Nat) (hL : 5≤L)
    (hbound : 32*k+14 < 2^L) (ha : 0<a) :
    s1LeftFacing L (32*k+13) 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m0EvenFourteenGenericLeftFacing L k a).drop 1 := by
  have hbinTarget := m0EvenFourteen_binDec_target L k hL hbound
  have hbinPow := binDec_pow2_sub_one (a-1) b
  have hlen : a-1+b+2 = a+b+1 := by omega
  have hexp : a-1+2 = a+1 := by omega
  have hbin : binDec (a+b+1) (2^b-1) =
      d0pow b ++ d1pow (a+1) := by
    simpa [hlen,hexp] using hbinPow
  unfold s1LeftFacing
  rw [hbin,hbinTarget]
  rw [← hexp]
  rw [d1pow_add_right (a-1) 2]
  simp [m0EvenFourteenGenericLeftFacing,
    m0EvenFourteenGenericTargetPrefix,
    m0EvenFourteenGenericCommonTail,
    List.drop,List.append_assoc,d0,d1]

private theorem m0EvenFourteenGeneric_resetPrefixCost
    (k a b : Nat) :
    resetPrefixCost 0 (32*k+14) a b =
      (36+12*a)+(39+3*b) := by
  have hvOdd : v2 (16*k+7) = 0 := by
    exact v2_of_odd (16*k+7) (by omega)
  have hdiv : (32*k+14)/2 = 16*k+7 := by omega
  have hvEven := v2_of_even (32*k+14) (by omega) (by omega)
  have hv : v2 (32*k+14) = 1 := by
    simpa [hdiv,hvOdd] using hvEven
  simp [resetPrefixCost,hv]
  omega

/-- Full source-level q4 reset prefix for arbitrary L>=5 and n=32*k+14. -/
theorem m0EvenFourteen_generic_q4_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 5≤L) (hbound : 32*k+14 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 0 (32*k+14) a b)
      (s1Config L (32*k+14) 0 a 0 b h) =
      some (s1Config L (32*k+13) 2 (a+b+1) (2^b-1) 0
        (h+5+3*b)) := by
  let Tq := m0EvenFourteenGenericCutTape L k a b h
  have hprefix := m0EvenFourteen_generic_q4_prefix_source
    L k a b h hL hbound ha
  have hleft := m0EvenFourteen_generic_q4_prefix_leftFacing
    L k a b h hL hbound ha
  have hshape := m0EvenFourteenGeneric_q4_rightShape L k a b h ha
  have htail := m0EvenFourteenGeneric_q4_far_tail L k a b h ha
  have happend := m0EvenFourteenGeneric_suffix_target_left
    L k a b hL hbound ha
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    L (32*k+13) 2 (a+b+1) (2^b-1)
    (m0EvenFourteenGenericLeftFacing L k a)
    hshape htail hleft happend
  have hsum := m0EvenFourteenGeneric_resetPrefixCost k a b
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

/-- Complete original-TM2 m=0 counted increment for n=32*k+14. -/
theorem m0EvenFourteen_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 5≤L) (hbound : 32*k+14 < 2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 0 (32*k+14) a b)
      (s1Config L (32*k+14) 0 a 0 b h) =
      some (s1Config L (32*k+13) 2 (a+b+1) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m0EvenFourteen_generic_q4_reset_prefix_source
    L k a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 0 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (32*k+13) 2 (a+b+1) b (h+5+3*b)
    (s1Config L (32*k+14) 0 a 0 b h)
    (resetPrefixCost 0 (32*k+14) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms m0EvenFourteen_generic_q4_prefix_source
#print axioms m0EvenFourteen_generic_q4_prefix_leftFacing
#print axioms m0EvenFourteen_generic_q4_reset_prefix_source
#print axioms m0EvenFourteen_counted_increment_source

end BB6Coverage.Agent48M0EvenFourteenGenericSource
