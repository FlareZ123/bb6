import M0OddQ4Prefix
import M0OddHeadBound
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Generic original-table source increment for every odd m=0 counter

Lift the base m=0,n=5 q4 prefix to arbitrary odd n=2*k+1 by a
half-line frame.  The source and base left-facing words share a prefix
of length 3*a+8; the base head bound keeps the entire q4 run inside
that prefix.  The cut's left stream has the generic high-order tail
binDec (L-1) k, so the same q4 suffix and counted drain finish every
odd-n increment.

This is an intermediate source theorem, not a complete BB(6) itinerary.
-/

namespace BB6Coverage.Agent48M0OddGenericSource

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent24M0OddQ4Prefix
open BB6Coverage.Agent48M0OddHeadBound
open BB6Coverage.Agent48CountedInc0
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

private def m0OddGenericInside (a : Nat) (h : Int) : Int → Bool :=
  fun x => decide (h-((3*a+7:Int)) ≤ x)

private def m0OddGenericInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 0 ++ d0 ++ d0

private def m0OddGenericTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ d1

def m0OddGenericLeftFacing (L k a : Nat) : List Bool :=
  m0OddGenericTargetPrefix a ++ (binDec (L-1) k ++ lh)

def m0OddGenericCutTape (L k a b : Nat) (h : Int) : Int → Bool :=
  (frame (m0OddGenericInside a h)
    (s1Config L (2*k+1) 0 a 0 b h).tape
    (⟨4,h,m0OddQ4CutTape a b h⟩ : Config)).tape

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

private theorem m0OddGeneric_quotient_bound (L k : Nat)
    (hL : 0 < L) (hbound : 2*k+1 < 2^L) :
    k < 2^(L-1) := by
  have hpow : 2^L = 2*2^(L-1) := by
    calc
      2^L = 2^((L-1)+1) := congrArg (fun x => 2^x) (by omega)
      _ = 2*2^(L-1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow] at hbound
  omega

private theorem m0OddGeneric_binDec_three_five :
    binDec 3 5 = d0 ++ d1 ++ d0 := by
  have h1 : binDec 3 5 = d0 ++ binDec 2 2 := by
    simpa using binDec_odd 2 2 (by decide)
  have h2 : binDec 2 2 = d1 ++ binDec 1 1 := by
    simpa using binDec_even 1 1 (by decide)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private theorem m0OddGeneric_binDec_three_four :
    binDec 3 4 = d1 ++ d1 ++ d0 := by
  have h1 : binDec 3 4 = d1 ++ binDec 2 2 := by
    simpa using binDec_even 2 2 (by decide)
  have h2 : binDec 2 2 = d1 ++ binDec 1 1 := by
    simpa using binDec_even 1 1 (by decide)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private theorem m0OddGeneric_inputPrefix_length (a : Nat) :
    (m0OddGenericInputPrefix a).length = 3*a+8 := by
  simp [m0OddGenericInputPrefix,d1pow_length,markerWord,d0,d1]

private theorem m0OddGeneric_targetPrefix_length (a : Nat) (ha : 0<a) :
    (m0OddGenericTargetPrefix a).length = 3*a+8 := by
  simp [m0OddGenericTargetPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m0OddGeneric_sourceLeftFacing
    (L k a : Nat) (hL : 0 < L) (hbound : 2*k+1 < 2^L) :
    s1LeftFacing L (2*k+1) 0 a 0 =
      m0OddGenericInputPrefix a ++ (binDec (L-1) k ++ lh) := by
  have hk := m0OddGeneric_quotient_bound L k hL hbound
  have hbin : binDec L (2*k+1) = d0 ++ binDec (L-1) k := by
    rw [show L = (L-1)+1 by omega]
    exact binDec_odd (L-1) k hk
  simp [s1LeftFacing,m0OddGenericInputPrefix,hbin,binDec_zero,
    List.append_assoc]

private theorem m0OddGeneric_baseSourceLeftFacing (a : Nat) :
    s1LeftFacing 3 5 0 a 0 =
      m0OddGenericInputPrefix a ++ (d1 ++ d0 ++ lh) := by
  simp [s1LeftFacing,m0OddGenericInputPrefix,
    m0OddGeneric_binDec_three_five,binDec_zero,List.append_assoc]

/-- Every odd-n source agrees with the n=5 base source on the entire
half-line that the base q4 prefix can read. -/
private theorem m0OddGeneric_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 0 < L) (hbound : 2*k+1 < 2^L) :
    ∀ x, m0OddGenericInside a h x = true →
      (s1Config L (2*k+1) 0 a 0 b h).tape x =
      (s1Config 3 5 0 a 0 b h).tape x := by
  have hsourceLeft := m0OddGeneric_sourceLeftFacing L k a hL hbound
  have hbaseLeft := m0OddGeneric_baseSourceLeftFacing a
  have hprefixLength := m0OddGeneric_inputPrefix_length a
  intro x hx
  by_cases hleft : x ≤ h
  · let i : Nat := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i:Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int) = x := by omega
    have hthreshold : h-((3*a+7:Int)) ≤ x := by
      simpa [m0OddGenericInside] using hx
    have hi : i ≤ 3*a+7 := by omega
    have hiPrefix : i < (m0OddGenericInputPrefix a).length := by
      rw [hprefixLength]
      omega
    have hsrc := s1Config_left_cell L (2*k+1) 0 a 0 b h i
    have hbase := s1Config_left_cell 3 5 0 a 0 b h i
    rw [hcoord] at hsrc hbase
    rw [hsourceLeft] at hsrc
    rw [hbaseLeft] at hbase
    have hsrcBit := Agent6Q4Prefix.sideBit_append_left
      (m0OddGenericInputPrefix a) (binDec (L-1) k ++ lh) i hiPrefix
    have hbaseBit := Agent6Q4Prefix.sideBit_append_left
      (m0OddGenericInputPrefix a) (d1 ++ d0 ++ lh) i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbase
    exact hsrc.trans hbase.symm
  · let i : Nat := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i:Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int) = x := by omega
    have hsrc := s1Config_right_cell L (2*k+1) 0 a 0 b h i
    have hbase := s1Config_right_cell 3 5 0 a 0 b h i
    rw [hcoord] at hsrc hbase
    exact hsrc.trans hbase.symm

/-- Lift the base 24+12a q4 prefix to every odd n=2*k+1. -/
theorem m0Odd_generic_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 0 < L) (hbound : 2*k+1 < 2^L) (ha : 0<a) :
    run tm2 (24+12*a)
      (s1Config L (2*k+1) 0 a 0 b h) =
      some ⟨4,h,m0OddGenericCutTape L k a b h⟩ := by
  let base : Config := s1Config 3 5 0 a 0 b h
  let background := (s1Config L (2*k+1) 0 a 0 b h).tape
  have hinput := m0OddGeneric_input_matches L k a b h hL hbound
  have hstart :
      frame (m0OddGenericInside a h) background base =
        s1Config L (2*k+1) 0 a 0 b h := by
    apply config_ext_by_fields
    · rfl
    · rfl
    · funext x
      by_cases hx : m0OddGenericInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 24+12*a → ∀ d,
        run tm2 j base = some d →
        m0OddGenericInside a h d.head = true := by
    intro j hj d hd
    have hd' :
        run tm2 j (s1Config 3 5 0 a 0 b h) = some d := by
      simpa [base] using hd
    have hlow :=
      m0Odd_q4_prefix_head_bound_sharp a b h ha j hj d hd'
    have hlowWeak : h-((3*a+7:Int)) ≤ d.head := by omega
    simpa [m0OddGenericInside] using hlowWeak
  have hlift := run_frame tm2 (m0OddGenericInside a h)
    background base (24+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (24+12*a) base =
        some (⟨4,h,m0OddQ4CutTape a b h⟩ : Config) := by
    have heq : base = ⟨3,h,(s1Config 3 5 0 a 0 b h).tape⟩ := by
      apply config_ext_by_fields <;> simp [base]
    rw [heq]
    exact m0Odd_q4_prefix_run a b h ha
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  have heq : frame (m0OddGenericInside a h) background (⟨4,h,m0OddQ4CutTape a b h⟩ : Config) = ⟨4,h,m0OddGenericCutTape L k a b h⟩ := by
    apply config_ext_by_fields <;> rfl
  rw [heq] at hlift
  exact hlift

private theorem m0OddGeneric_cut_eq_base_inside
    (L k a b : Nat) (h x : Int)
    (hin : m0OddGenericInside a h x = true) :
    m0OddGenericCutTape L k a b h x = m0OddQ4CutTape a b h x := by
  simp [m0OddGenericCutTape,frame,hin]

private theorem m0OddGeneric_cut_eq_input_outside
    (L k a b : Nat) (h x : Int)
    (hout : m0OddGenericInside a h x = false) :
    m0OddGenericCutTape L k a b h x =
      (s1Config L (2*k+1) 0 a 0 b h).tape x := by
  simp [m0OddGenericCutTape,frame,hout]

private theorem m0OddGeneric_baseCutLeftFacing (a : Nat) :
    m0OddQ4LeftFacing a =
      m0OddGenericTargetPrefix a ++ (d1 ++ d0 ++ lh) := by
  simp [m0OddQ4LeftFacing,m0OddGenericTargetPrefix,
    m0OddGeneric_binDec_three_four,List.append_assoc]

/-- The q4 cut tape has the exact generic target left stream for every
odd input n=2*k+1, including the untouched high-order binary tail. -/
theorem m0Odd_generic_q4_prefix_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 0 < L) (hbound : 2*k+1 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m0OddGenericCutTape L k a b h (h-(i:Int)) =
        sideBit (m0OddGenericLeftFacing L k a) i := by
  have hsourceLeft := m0OddGeneric_sourceLeftFacing L k a hL hbound
  have hbaseLeft := m0OddGeneric_baseCutLeftFacing a
  have hinputPrefixLength := m0OddGeneric_inputPrefix_length a
  have htargetPrefixLength := m0OddGeneric_targetPrefix_length a ha
  intro i
  by_cases hi : i ≤ 3*a+7
  · have hin :
      m0OddGenericInside a h (h-(i:Int)) = true := by
      simp [m0OddGenericInside]
      omega
    rw [m0OddGeneric_cut_eq_base_inside L k a b h
      (h-(i:Int)) hin]
    rw [m0Odd_q4_prefix_leftFacing a b h ha i]
    rw [hbaseLeft]
    simp only [m0OddGenericLeftFacing]
    have hbaseBit := Agent6Q4Prefix.sideBit_append_left
      (m0OddGenericTargetPrefix a) (d1 ++ d0 ++ lh) i
      (by rw [htargetPrefixLength]; omega)
    have htargetBit := Agent6Q4Prefix.sideBit_append_left
      (m0OddGenericTargetPrefix a) (binDec (L-1) k ++ lh) i
      (by rw [htargetPrefixLength]; omega)
    rw [hbaseBit,htargetBit]
  · have hout :
      m0OddGenericInside a h (h-(i:Int)) = false := by
      simp [m0OddGenericInside]
      omega
    rw [m0OddGeneric_cut_eq_input_outside L k a b h
      (h-(i:Int)) hout]
    rw [s1Config_left_cell L (2*k+1) 0 a 0 b h i]
    rw [hsourceLeft]
    simp only [m0OddGenericLeftFacing]
    have hsourceBit := Agent6Q4Prefix.sideBit_append_right
      (m0OddGenericInputPrefix a) (binDec (L-1) k ++ lh) i
      (by rw [hinputPrefixLength]; omega)
    have htargetBit := Agent6Q4Prefix.sideBit_append_right
      (m0OddGenericTargetPrefix a) (binDec (L-1) k ++ lh) i
      (by rw [htargetPrefixLength]; omega)
    rw [hsourceBit,htargetBit]
    simp [hinputPrefixLength,htargetPrefixLength]

private theorem m0OddGeneric_q4RightShape_congr
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

private theorem m0OddGeneric_q4_rightShape
    (L k a b : Nat) (h : Int) (ha : 0<a) :
    Agent8Q4Suffix.q4RightShape (m0OddGenericCutTape L k a b h) h b := by
  apply m0OddGeneric_q4RightShape_congr
    (m0OddQ4CutTape a b h) (m0OddGenericCutTape L k a b h) h b
  · intro x hx
    have hin : m0OddGenericInside a h x = true := by
      simp [m0OddGenericInside]
      omega
    symm
    exact m0OddGeneric_cut_eq_base_inside L k a b h x hin
  · exact m0Odd_q4_prefix_rightShape a b h ha

private theorem m0OddGeneric_q4_far_tail
    (L k a b : Nat) (h : Int) (ha : 0<a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m0OddGenericCutTape L k a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hin :
      m0OddGenericInside a h (h+1+(i:Int)) = true := by
    simp [m0OddGenericInside]
    omega
  rw [m0OddGeneric_cut_eq_base_inside L k a b h
    (h+1+(i:Int)) hin]
  exact m0Odd_q4_prefix_far_tail a b h ha i hi

private theorem m0OddGeneric_suffix_target_left
    (L k a b : Nat) (hL : 0<L)
    (hbound : 2*k+1 < 2^L) (ha : 0<a) :
    s1LeftFacing L (2*k) 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m0OddGenericLeftFacing L k a).drop 1 := by
  have hk := m0OddGeneric_quotient_bound L k hL hbound
  have hbinPow := binDec_pow2_sub_one (a-1) b
  have hlen : a-1+b+2 = a+b+1 := by omega
  have hexp : a-1+2 = a+1 := by omega
  have hbin : binDec (a+b+1) (2^b-1) =
      d0pow b ++ d1pow (a+1) := by
    simpa [hlen,hexp] using hbinPow
  have hbinEven : binDec L (2*k) =
      d1 ++ binDec (L-1) k := by
    rw [show L = (L-1)+1 by omega]
    exact binDec_even (L-1) k hk
  unfold s1LeftFacing
  rw [hbin,hbinEven]
  rw [← hexp]
  rw [d1pow_add_right (a-1) 2]
  simp [m0OddGenericLeftFacing,m0OddGenericTargetPrefix,
    List.drop,List.append_assoc]

/-- Full source-level m=0 q4 reset prefix for every odd n. -/
theorem m0Odd_generic_q4_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 0<L) (hbound : 2*k+1 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 0 (2*k+1) a b)
      (s1Config L (2*k+1) 0 a 0 b h) =
      some (s1Config L (2*k) 2 (a+b+1) (2^b-1) 0
        (h+5+3*b)) := by
  let Tq := m0OddGenericCutTape L k a b h
  have hprefix := m0Odd_generic_q4_prefix_source L k a b h hL hbound ha
  have hleft := m0Odd_generic_q4_prefix_leftFacing
    L k a b h hL hbound ha
  have hshape := m0OddGeneric_q4_rightShape L k a b h ha
  have htail := m0OddGeneric_q4_far_tail L k a b h ha
  have happend := m0OddGeneric_suffix_target_left L k a b hL hbound ha
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    L (2*k) 2 (a+b+1) (2^b-1)
    (m0OddGenericLeftFacing L k a)
    hshape htail hleft happend
  have hsum : resetPrefixCost 0 (2*k+1) a b =
      (24+12*a)+(39+3*b) := by
    have hv : v2 (2*k+1) = 0 := by
      exact v2_of_odd (2*k+1) (by omega)
    simp [resetPrefixCost,hv]
    omega
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

/-- Complete original-TM2 m=0 counted increment for every odd n. -/
theorem m0Odd_counted_increment_source_k
    (L k a b : Nat) (h : Int)
    (hL : 0<L) (hbound : 2*k+1 < 2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 0 (2*k+1) a b)
      (s1Config L (2*k+1) 0 a 0 b h) =
      some (s1Config L (2*k) 2 (a+b+1) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m0Odd_generic_q4_reset_prefix_source
    L k a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 0 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (2*k) 2 (a+b+1) b (h+5+3*b)
    (s1Config L (2*k+1) 0 a 0 b h)
    (resetPrefixCost 0 (2*k+1) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

/-- Generic all-odd-n source increment, including the residue-1/5/7
families as instances of one original-table theorem. -/
theorem m0Odd_counted_increment_source
    (L n a b : Nat) (h : Int)
    (hL : 0<L) (hn : n%2=1)
    (hbound : n < 2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 0 n a b)
      (s1Config L n 0 a 0 b h) =
      some (s1Config L (n-1) 2 (a+b+1) 0 (2^b-1)
        (h+5+3*b)) := by
  have hk : n = 2*(n/2)+1 := by omega
  obtain ⟨k,hk⟩ : ∃ k, n = 2*k+1 := ⟨n/2,hk⟩
  subst n
  have hbound' : 2*k+1 < 2^L := by simpa using hbound
  have hrow := m0Odd_counted_increment_source_k
    L k a b h hL hbound' ha
  simpa using hrow

#print axioms m0Odd_generic_q4_prefix_source
#print axioms m0Odd_generic_q4_prefix_leftFacing
#print axioms m0Odd_generic_q4_reset_prefix_source
#print axioms m0Odd_counted_increment_source_k
#print axioms m0Odd_counted_increment_source

end BB6Coverage.Agent48M0OddGenericSource
