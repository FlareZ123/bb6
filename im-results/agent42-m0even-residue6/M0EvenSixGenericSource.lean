import M0EvenSixQ4Prefix
import M0EvenSixHeadBound
import S1CountedDrain
import Q4RightEndpoint
import Lean.Elab.Tactic.Omega

/-!
# Generic original-table m=0,n=8*q+6 increment

Lift the base L=3,n=6 q4 prefix to arbitrary L>=3 and n=8*q+6.
The frame reads only the first 3*a+11 left-facing cells. The source
and target streams then share the exact tail
`d0 ++ binDec (L-3) q ++ lh`.
The q4 suffix and counted all-ones drain complete the increment.
-/

namespace BB6Coverage.Agent42M0EvenSixGenericSource

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent42M0EvenSixQ4Bridge
open BB6Coverage.Agent42M0EvenSixQ4Prefix
open BB6Coverage.Agent42M0EvenSixHeadBound
open BB6Coverage.Agent48CountedInc0
open BB6ChampionArithmetic
open BB6Coverage.Agent24Q4Endpoint

set_option maxHeartbeats 4000000

private def m0EvenSixGenericInside (a : Nat) (h : Int) : Int → Bool :=
  fun x => decide (h-((3*a+10:Int)) ≤ x)

private def m0EvenSixGenericInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d0

private def m0EvenSixGenericTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ d0 ++ d1

private def m0EvenSixGenericCommonTail (L q : Nat) : List Bool :=
  d0 ++ binDec (L-3) q ++ lh

private def m0EvenSixGenericInputLeftFacing (L q a : Nat) : List Bool :=
  m0EvenSixGenericInputPrefix a ++
    m0EvenSixGenericCommonTail L q

def m0EvenSixGenericLeftFacing (L q a : Nat) : List Bool :=
  m0EvenSixGenericTargetPrefix a ++
    m0EvenSixGenericCommonTail L q

def m0EvenSixGenericCutTape (L q a b : Nat) (h : Int) : Int → Bool :=
  (frame (m0EvenSixGenericInside a h)
    (s1Config L (8*q+6) 0 a 0 b h).tape
    (⟨4,h,m0EvenSixQ4CutTape a b h⟩ : Config)).tape

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

private theorem m0EvenSix_binDec_source
    (L q : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+6 < 2^L) :
    binDec L (8*q+6) =
      d1 ++ d0 ++ d0 ++ binDec (L-3) q := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    calc
      2^(L) = 2^((L-3)+3) := congrArg (fun x => 2^x) (by omega)
      _ = _ := by rw [Nat.pow_add]; omega
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    calc
      2^(L-1) = 2^((L-3)+2) := congrArg (fun x => 2^x) (by omega)
      _ = _ := by rw [Nat.pow_add]; omega
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    calc
      2^(L-2) = 2^((L-3)+1) := congrArg (fun x => 2^x) (by omega)
      _ = _ := by rw [Nat.pow_add]; omega
  have hq : q < 2^(L-3) := by
    rw [hpow3] at hbound
    omega
  have hq1 : 4*q+3 < 2^(L-1) := by
    rw [hpow2]
    omega
  have hq2 : 2*q+1 < 2^(L-2) := by
    rw [hpow1]
    omega
  have h1 : binDec L (8*q+6) =
      d1 ++ binDec (L-1) (4*q+3) := by
    rw [show L = (L-1)+1 by omega,
      show 8*q+6 = 2*(4*q+3) by omega]
    exact binDec_even (L-1) (4*q+3) hq1
  have h2 : binDec (L-1) (4*q+3) =
      d0 ++ binDec (L-2) (2*q+1) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*q+3 = 2*(2*q+1)+1 by omega]
    exact binDec_odd (L-2) (2*q+1) hq2
  have h3 : binDec (L-2) (2*q+1) =
      d0 ++ binDec (L-3) q := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_odd (L-3) q hq
  rw [h1,h2,h3]
  simp [List.append_assoc]

private theorem m0EvenSix_binDec_target
    (L q : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+6 < 2^L) :
    binDec L (8*q+5) =
      d0 ++ d1 ++ d0 ++ binDec (L-3) q := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    calc
      2^(L) = 2^((L-3)+3) := congrArg (fun x => 2^x) (by omega)
      _ = _ := by rw [Nat.pow_add]; omega
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    calc
      2^(L-1) = 2^((L-3)+2) := congrArg (fun x => 2^x) (by omega)
      _ = _ := by rw [Nat.pow_add]; omega
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    calc
      2^(L-2) = 2^((L-3)+1) := congrArg (fun x => 2^x) (by omega)
      _ = _ := by rw [Nat.pow_add]; omega
  have hq : q < 2^(L-3) := by
    rw [hpow3] at hbound
    omega
  have hq1 : 4*q+2 < 2^(L-1) := by
    rw [hpow2]
    omega
  have hq2 : 2*q+1 < 2^(L-2) := by
    rw [hpow1]
    omega
  have h1 : binDec L (8*q+5) =
      d0 ++ binDec (L-1) (4*q+2) := by
    rw [show L = (L-1)+1 by omega,
      show 8*q+5 = 2*(4*q+2)+1 by omega]
    exact binDec_odd (L-1) (4*q+2) hq1
  have h2 : binDec (L-1) (4*q+2) =
      d1 ++ binDec (L-2) (2*q+1) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*q+2 = 2*(2*q+1) by omega]
    exact binDec_even (L-2) (2*q+1) hq2
  have h3 : binDec (L-2) (2*q+1) =
      d0 ++ binDec (L-3) q := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_odd (L-3) q hq
  rw [h1,h2,h3]
  simp [List.append_assoc]

private theorem m0EvenSix_sourceLeftFacing
    (L q a : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+6 < 2^L) :
    s1LeftFacing L (8*q+6) 0 a 0 =
      m0EvenSixGenericInputLeftFacing L q a := by
  have hbin := m0EvenSix_binDec_source L q hL hbound
  simp [s1LeftFacing,m0EvenSixGenericInputLeftFacing,
    m0EvenSixGenericInputPrefix,m0EvenSixGenericCommonTail,
    hbin,binDec_zero,d0,d1,List.append_assoc]

private theorem m0EvenSix_baseSourceLeftFacing (a : Nat) :
    s1LeftFacing 3 6 0 a 0 =
      m0EvenSixGenericInputPrefix a ++ (d0 ++ lh) := by
  simp [s1LeftFacing,m0EvenSixGenericInputPrefix,
    m0EvenSixGenericCommonTail,
    m0Even_binDec_three_six,binDec_zero,d0,d1,
    List.append_assoc]

private theorem m0EvenSix_baseCutLeftFacing (a : Nat) :
    m0EvenSixQ4LeftFacing a =
      m0EvenSixGenericTargetPrefix a ++ (d0 ++ lh) := by
  simp [m0EvenSixQ4LeftFacing,m0EvenSixGenericTargetPrefix,
    m0Even_binDec_three_five,d0,d1,List.append_assoc]

private theorem m0EvenSixGeneric_inputPrefix_length (a : Nat) :
    (m0EvenSixGenericInputPrefix a).length = 3*a+11 := by
  simp [m0EvenSixGenericInputPrefix,d1pow_length,markerWord,d0,d1]

private theorem m0EvenSixGeneric_targetPrefix_length (a : Nat)
    (ha : 0<a) :
    (m0EvenSixGenericTargetPrefix a).length = 3*a+11 := by
  simp [m0EvenSixGenericTargetPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m0EvenSixGeneric_input_matches
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+6 < 2^L) :
    ∀ x, m0EvenSixGenericInside a h x = true →
      (s1Config L (8*q+6) 0 a 0 b h).tape x =
      (s1Config 3 6 0 a 0 b h).tape x := by
  have hsourceLeft := m0EvenSix_sourceLeftFacing L q a hL hbound
  have hbaseLeft := m0EvenSix_baseSourceLeftFacing a
  have hprefixLength := m0EvenSixGeneric_inputPrefix_length a
  intro x hx
  by_cases hleft : x ≤ h
  · let i : Nat := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i:Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int) = x := by omega
    have hthreshold : h-((3*a+10:Int)) ≤ x := by
      simpa [m0EvenSixGenericInside] using hx
    have hi : i ≤ 3*a+10 := by omega
    have hiPrefix :
        i < (m0EvenSixGenericInputPrefix a).length := by
      rw [hprefixLength]
      omega
    have hsrc := s1Config_left_cell L (8*q+6) 0 a 0 b h i
    have hbase := s1Config_left_cell 3 6 0 a 0 b h i
    rw [hcoord] at hsrc hbase
    rw [hsourceLeft] at hsrc
    rw [hbaseLeft] at hbase
    have hsrcBit := Agent6Q4Prefix.sideBit_append_left
      (m0EvenSixGenericInputPrefix a)
      (m0EvenSixGenericCommonTail L q) i hiPrefix
    have hbaseBit := Agent6Q4Prefix.sideBit_append_left
      (m0EvenSixGenericInputPrefix a)
      (d0 ++ lh) i hiPrefix
    change _ = sideBit (m0EvenSixGenericInputPrefix a ++ m0EvenSixGenericCommonTail L q) i at hsrc
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbase
    exact hsrc.trans hbase.symm
  · let i : Nat := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i:Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int) = x := by omega
    have hsrc := s1Config_right_cell L (8*q+6) 0 a 0 b h i
    have hbase := s1Config_right_cell 3 6 0 a 0 b h i
    rw [hcoord] at hsrc hbase
    exact hsrc.trans hbase.symm

/-- Lift the base 36+12a q4 prefix to arbitrary L>=3 and n=8*q+6. -/
theorem m0EvenSix_generic_q4_prefix_source
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+6 < 2^L) (ha : 0<a) :
    run tm2 (36+12*a)
      (s1Config L (8*q+6) 0 a 0 b h) =
      some ⟨4,h,m0EvenSixGenericCutTape L q a b h⟩ := by
  let base : Config := s1Config 3 6 0 a 0 b h
  let background := (s1Config L (8*q+6) 0 a 0 b h).tape
  have hinput := m0EvenSixGeneric_input_matches L q a b h hL hbound
  have hstart :
      frame (m0EvenSixGenericInside a h) background base =
        s1Config L (8*q+6) 0 a 0 b h := by
    apply config_ext_by_fields
    · rfl
    · rfl
    · funext x
      by_cases hx : m0EvenSixGenericInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 36+12*a → ∀ d,
        run tm2 j base = some d →
        m0EvenSixGenericInside a h d.head = true := by
    intro j hj d hd
    have hd' :
        run tm2 j (s1Config 3 6 0 a 0 b h) = some d := by
      simpa [base] using hd
    have hlow :=
      m0EvenSix_q4_prefix_head_bound a b h ha j hj d hd'
    simpa [m0EvenSixGenericInside] using hlow
  have hlift := run_frame tm2 (m0EvenSixGenericInside a h)
    background base (36+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (36+12*a) base =
        some (⟨4,h,m0EvenSixQ4CutTape a b h⟩ : Config) := by
    have heq : base = ⟨3,h,(s1Config 3 6 0 a 0 b h).tape⟩ := by
      apply config_ext_by_fields <;> simp [base]
    rw [heq]
    exact m0EvenSix_q4_prefix_run a b h ha
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  have heq : frame (m0EvenSixGenericInside a h) background (⟨4,h,m0EvenSixQ4CutTape a b h⟩ : Config) = ⟨4,h,m0EvenSixGenericCutTape L q a b h⟩ := by
    apply config_ext_by_fields <;> rfl
  rw [heq] at hlift
  exact hlift

private theorem m0EvenSixGeneric_cut_eq_base_inside
    (L q a b : Nat) (h x : Int)
    (hin : m0EvenSixGenericInside a h x = true) :
    m0EvenSixGenericCutTape L q a b h x =
      m0EvenSixQ4CutTape a b h x := by
  simp [m0EvenSixGenericCutTape,frame,hin]

private theorem m0EvenSixGeneric_cut_eq_input_outside
    (L q a b : Nat) (h x : Int)
    (hout : m0EvenSixGenericInside a h x = false) :
    m0EvenSixGenericCutTape L q a b h x =
      (s1Config L (8*q+6) 0 a 0 b h).tape x := by
  simp [m0EvenSixGenericCutTape,frame,hout]

/-- Exact generic target left-facing stream at the q4 cut. -/
theorem m0EvenSix_generic_q4_prefix_leftFacing
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+6 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m0EvenSixGenericCutTape L q a b h (h-(i:Int)) =
        sideBit (m0EvenSixGenericLeftFacing L q a) i := by
  have hsourceLeft := m0EvenSix_sourceLeftFacing L q a hL hbound
  have hbaseCutLeft := m0EvenSix_baseCutLeftFacing a
  have hinputPrefixLength := m0EvenSixGeneric_inputPrefix_length a
  have htargetPrefixLength := m0EvenSixGeneric_targetPrefix_length a ha
  intro i
  by_cases hi : i ≤ 3*a+10
  · have hin :
      m0EvenSixGenericInside a h (h-(i:Int)) = true := by
      simp [m0EvenSixGenericInside]
      omega
    rw [m0EvenSixGeneric_cut_eq_base_inside L q a b h
      (h-(i:Int)) hin]
    rw [m0EvenSix_q4_prefix_leftFacing a b h ha i]
    rw [hbaseCutLeft]
    simp only [m0EvenSixGenericLeftFacing]
    have hbaseBit := Agent6Q4Prefix.sideBit_append_left
      (m0EvenSixGenericTargetPrefix a)
      (d0 ++ lh) i
      (by rw [htargetPrefixLength]; omega)
    have htargetBit := Agent6Q4Prefix.sideBit_append_left
      (m0EvenSixGenericTargetPrefix a)
      (m0EvenSixGenericCommonTail L q) i
      (by rw [htargetPrefixLength]; omega)
    rw [hbaseBit,htargetBit]
  · have hout :
      m0EvenSixGenericInside a h (h-(i:Int)) = false := by
      simp [m0EvenSixGenericInside]
      omega
    rw [m0EvenSixGeneric_cut_eq_input_outside L q a b h
      (h-(i:Int)) hout]
    rw [s1Config_left_cell L (8*q+6) 0 a 0 b h i]
    rw [hsourceLeft]
    simp only [m0EvenSixGenericInputLeftFacing,
      m0EvenSixGenericLeftFacing]
    have hsourceBit := Agent6Q4Prefix.sideBit_append_right
      (m0EvenSixGenericInputPrefix a)
      (m0EvenSixGenericCommonTail L q) i
      (by rw [hinputPrefixLength]; omega)
    have htargetBit := Agent6Q4Prefix.sideBit_append_right
      (m0EvenSixGenericTargetPrefix a)
      (m0EvenSixGenericCommonTail L q) i
      (by rw [htargetPrefixLength]; omega)
    rw [hsourceBit,htargetBit]
    simp [hinputPrefixLength,htargetPrefixLength]

private theorem m0EvenSixGeneric_q4RightShape_congr
    (T U : Int → Bool) (h : Int) (b : Nat)
    (heq : ∀ x, h ≤ x → T x = U x)
    (hT : Agent8Q4Suffix.q4RightShape T h b) :
    Agent8Q4Suffix.q4RightShape U h b := by
  unfold Agent8Q4Suffix.q4RightShape at *
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

private theorem m0EvenSixGeneric_q4_rightShape
    (L q a b : Nat) (h : Int) (ha : 0<a) :
    Agent8Q4Suffix.q4RightShape (m0EvenSixGenericCutTape L q a b h) h b := by
  apply m0EvenSixGeneric_q4RightShape_congr
    (m0EvenSixQ4CutTape a b h)
    (m0EvenSixGenericCutTape L q a b h) h b
  · intro x hx
    have hin : m0EvenSixGenericInside a h x = true := by
      simp [m0EvenSixGenericInside]
      omega
    symm
    exact m0EvenSixGeneric_cut_eq_base_inside L q a b h x hin
  · exact m0EvenSix_q4_prefix_rightShape a b h ha

private theorem m0EvenSixGeneric_q4_far_tail
    (L q a b : Nat) (h : Int) (ha : 0<a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m0EvenSixGenericCutTape L q a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hin :
      m0EvenSixGenericInside a h (h+1+(i:Int)) = true := by
    simp [m0EvenSixGenericInside]
    omega
  rw [m0EvenSixGeneric_cut_eq_base_inside L q a b h
    (h+1+(i:Int)) hin]
  exact m0EvenSix_q4_prefix_far_tail a b h ha i hi

private theorem m0EvenSixGeneric_suffix_target_left
    (L q a b : Nat) (hL : 3≤L)
    (hbound : 8*q+6 < 2^L) (ha : 0<a) :
    s1LeftFacing L (8*q+5) 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m0EvenSixGenericLeftFacing L q a).drop 1 := by
  have hbinTarget := m0EvenSix_binDec_target L q hL hbound
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
  simp [m0EvenSixGenericLeftFacing,
    m0EvenSixGenericTargetPrefix,
    m0EvenSixGenericCommonTail,
    List.drop,List.append_assoc,d0,d1]

private theorem m0EvenSixGeneric_resetPrefixCost
    (q a b : Nat) :
    resetPrefixCost 0 (8*q+6) a b =
      (36+12*a)+(39+3*b) := by
  have hvOdd : v2 (4*q+3) = 0 := by
    exact v2_of_odd (4*q+3) (by omega)
  have hdiv : (8*q+6)/2 = 4*q+3 := by omega
  have hvEven := v2_of_even (8*q+6) (by omega) (by omega)
  have hv : v2 (8*q+6) = 1 := by
    simpa [hdiv,hvOdd] using hvEven
  simp [resetPrefixCost,hv]
  omega

/-- Full source-level q4 reset prefix for arbitrary L>=3 and n=8*q+6. -/
theorem m0EvenSix_generic_q4_reset_prefix_source
    (L q a b : Nat) (h : Int)
    (hL : 3≤L) (hbound : 8*q+6 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 0 (8*q+6) a b)
      (s1Config L (8*q+6) 0 a 0 b h) =
      some (s1Config L (8*q+5) 2 (a+b+1) (2^b-1) 0
        (h+5+3*b)) := by
  let Tq := m0EvenSixGenericCutTape L q a b h
  have hprefix := m0EvenSix_generic_q4_prefix_source
    L q a b h hL hbound ha
  have hleft := m0EvenSix_generic_q4_prefix_leftFacing
    L q a b h hL hbound ha
  have hshape := m0EvenSixGeneric_q4_rightShape L q a b h ha
  have htail := m0EvenSixGeneric_q4_far_tail L q a b h ha
  have happend := m0EvenSixGeneric_suffix_target_left
    L q a b hL hbound ha
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    L (8*q+5) 2 (a+b+1) (2^b-1)
    (m0EvenSixGenericLeftFacing L q a)
    hshape htail hleft happend
  have hsum := m0EvenSixGeneric_resetPrefixCost q a b
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

/-- Complete original-TM2 m=0 counted increment for n=8*q+6. -/
theorem m0EvenSix_counted_increment_source
    (L q a b : Nat) (h : Int)
    (hL : 3≤L) (hbound : 8*q+6 < 2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 0 (8*q+6) a b)
      (s1Config L (8*q+6) 0 a 0 b h) =
      some (s1Config L (8*q+5) 2 (a+b+1) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m0EvenSix_generic_q4_reset_prefix_source
    L q a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 0 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*q+5) 2 (a+b+1) b (h+5+3*b)
    (s1Config L (8*q+6) 0 a 0 b h)
    (resetPrefixCost 0 (8*q+6) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms m0EvenSix_generic_q4_prefix_source
#print axioms m0EvenSix_generic_q4_prefix_leftFacing
#print axioms m0EvenSix_generic_q4_reset_prefix_source
#print axioms m0EvenSix_counted_increment_source

end BB6Coverage.Agent42M0EvenSixGenericSource
