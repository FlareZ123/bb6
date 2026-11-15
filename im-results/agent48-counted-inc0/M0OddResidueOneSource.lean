import M0OddResidueFive
import M1EvenResidueTwoInputFrame
import Lean.Elab.Tactic.Omega

/-!
# Source composition for the m=0, n=8*k+1 row

The base m=0,n=5 q4 prefix reads only the half-line x >= h-3a-6.
Every n=8*k+1 source agrees with the base n=5 source on that half-line.
We therefore lift the existing prefix with run_frame, preserve the
unread high-order tail, and compose the generic q4 suffix and counted drain.

Status: written source candidate; not yet compiled or axiom-audited.
-/

namespace BB6Coverage.Agent48M0OddResidueOneSource

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent24M0OddQ4Prefix
open BB6Coverage.Agent24M0OddResidueFive
open BB6Coverage.Agent8M1EvenResidueTwoInputFrameGeneral
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

/-- Low three blocks of every admissible n=8*k. -/
theorem binDec_residue0 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k < 2^L) :
    binDec L (8*k) = d1 ++ d1 ++ d1 ++ binDec (L-3) k := by
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
  have hq1 : 4*k < 2^(L-1) := by
    rw [hpow2]
    omega
  have hq2 : 2*k < 2^(L-2) := by
    rw [hpow1]
    omega
  have h1 : binDec L (8*k) =
      d1 ++ binDec (L-1) (4*k) := by
    rw [show L = (L-1)+1 by omega,
      show 8*k = 2*(4*k) by omega]
    exact binDec_even (L-1) (4*k) hq1
  have h2 : binDec (L-1) (4*k) =
      d1 ++ binDec (L-2) (2*k) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*k = 2*(2*k) by omega]
    exact binDec_even (L-2) (2*k) hq2
  have h3 : binDec (L-2) (2*k) =
      d1 ++ binDec (L-3) k := by
    rw [show L-2 = (L-3)+1 by omega,
      show 2*k = 2*k by rfl]
    exact binDec_even (L-3) k hk
  rw [h1,h2,h3]
  simp [List.append_assoc]

/-- The common source head prefix through the first low-order d0 block. -/
private def m0OddResidueOneSourceHeadPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 0 ++ d0

/-- The canonical m=2 target head prefix after the base q4 prefix. -/
private def m0OddResidueOneTargetHeadPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0

private def m0OddResidueOneTargetPrefix (a : Nat) : List Bool :=
  m0OddResidueOneTargetHeadPrefix a ++ d1 ++ d1 ++ d1

/-- Complete left-facing target word at the n=8*k+1 q4 cut. -/
def m0OddResidueOneLeftFacing (L k a : Nat) : List Bool :=
  m0OddResidueOneTargetPrefix a ++ (binDec (L-3) k ++ lh)

/-- The prefix's exact read half-line is x >= h-3a-6. -/
def m0OddResidueOneInside (a : Nat) (h : Int) : Int → Bool :=
  fun x => decide (h-((3*a:Int))-6 ≤ x)

/-- The n=8*k+1 cut preserves its own unread left tail and reuses the
base n=5 q4 cut on the readable half-line. -/
def m0OddResidueOneCutTape
    (L k a b : Nat) (h : Int) : Int → Bool :=
  (frame (m0OddResidueOneInside a h)
    (s1Config L (8*k+1) 0 a 0 b h).tape
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

private theorem residueOne_quotient_bound (L k : Nat)
    (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) :
    k < 2^(L-3) := by
  have hpow : 2^L = 8*2^(L-3) := by
    rw [show L=(L-3)+3 by omega, Nat.pow_add]
    norm_num
    ring
  rw [hpow] at hbound
  omega

/-- n=8*k+1 and the base n=5 source agree on every cell the base
q4 prefix can visit. -/
private theorem m0OddResidueOne_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) :
    ∀ x, m0OddResidueOneInside a h x = true →
      (s1Config L (8*k+1) 0 a 0 b h).tape x =
      (s1Config 3 5 0 a 0 b h).tape x := by
  have hk := residueOne_quotient_bound L k hL hbound
  have hbin1 := binDec_residue_one L k hL hk
  have hbin35 : binDec 3 5 = d0 ++ d1 ++ d0 := by
    have hh := binDec_residue5 3 0 (by omega) (by decide)
    simpa [binDec_zero,d1pow] using hh
  let P : List Bool := m0OddResidueOneSourceHeadPrefix a ++ d0
  have hsourceLeft :
      s1LeftFacing L (8*k+1) 0 a 0 =
        P ++ (d1 ++ d1 ++ binDec (L-3) k ++ lh) := by
    simp [s1LeftFacing,m0OddResidueOneSourceHeadPrefix,
      binDec_zero,hbin1,P,List.append_assoc]
  have hbaseLeft :
      s1LeftFacing 3 5 0 a 0 =
        P ++ (d1 ++ d0 ++ lh) := by
    simp [s1LeftFacing,m0OddResidueOneSourceHeadPrefix,
      binDec_zero,hbin35,P,List.append_assoc]
  have hprefixLength : P.length = 3*a+8 := by
    simp [P,m0OddResidueOneSourceHeadPrefix,
      d1pow_length,markerWord,d0,d1]
  intro x hx
  by_cases hleft : x ≤ h
  · let i : Nat := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i : Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int) = x := by omega
    have hthreshold : h-((3*a:Int))-6 ≤ x := by
      simpa [m0OddResidueOneInside] using hx
    have hi : i ≤ 3*a+6 := by omega
    have hiPrefix : i < P.length := by
      rw [hprefixLength]
      omega
    have hsrc := s1Config_left_cell L (8*k+1) 0 a 0 b h i
    have hbase := s1Config_left_cell 3 5 0 a 0 b h i
    rw [hcoord] at hsrc hbase
    rw [hsourceLeft] at hsrc
    rw [hbaseLeft] at hbase
    have hsrcBit := sideBit_append_left P
      (d1 ++ d1 ++ binDec (L-3) k ++ lh) i hiPrefix
    have hbaseBit := sideBit_append_left P (d1 ++ d0 ++ lh) i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbase
    exact hsrc.trans hbase.symm
  · let i : Nat := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i : Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int) = x := by omega
    have hsrc := s1Config_right_cell L (8*k+1) 0 a 0 b h i
    have hbase := s1Config_right_cell 3 5 0 a 0 b h i
    rw [hcoord] at hsrc hbase
    exact hsrc.trans hbase.symm

/-- Lift the existing 24+12a n=5 q4 prefix to every n=8*k+1. -/
theorem m0Odd_residue1_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) (ha : 0<a) :
    run tm2 (24+12*a)
      (s1Config L (8*k+1) 0 a 0 b h) =
      some ⟨4,h,m0OddResidueOneCutTape L k a b h⟩ := by
  let base : Config := ⟨3,h,(s1Config 3 5 0 a 0 b h).tape⟩
  let background := (s1Config L (8*k+1) 0 a 0 b h).tape
  have hinput := m0OddResidueOne_input_matches L k a b h hL hbound
  have hstart :
      frame (m0OddResidueOneInside a h) background base =
        s1Config L (8*k+1) 0 a 0 b h := by
    apply config_ext_by_fields
    · rfl
    · rfl
    · funext x
      by_cases hx : m0OddResidueOneInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 24+12*a → ∀ d,
        run tm2 j base = some d →
        m0OddResidueOneInside a h d.head = true := by
    intro j hj d hd
    have hd' :
        run tm2 j (s1Config 3 5 0 a 0 b h) = some d := by
      simpa [base] using hd
    have hlow :=
      m0Odd_q4_prefix_head_bound_sharp a b h ha j hj d hd'
    simpa [m0OddResidueOneInside] using hlow
  have hlift := run_frame tm2 (m0OddResidueOneInside a h)
    background base (24+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (24+12*a) base =
        some (⟨4,h,m0OddQ4CutTape a b h⟩ : Config) := by
    simpa [base] using m0Odd_q4_prefix_run a b h ha
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  simpa [m0OddResidueOneCutTape,background] using hlift

private theorem m0OddResidueOne_cut_eq_base
    (L k a b : Nat) (h x : Int)
    (hin : m0OddResidueOneInside a h x = true) :
    m0OddResidueOneCutTape L k a b h x =
      m0OddQ4CutTape a b h x := by
  simp [m0OddResidueOneCutTape,frame,hin]

private theorem m0OddResidueOne_cut_eq_input
    (L k a b : Nat) (h x : Int)
    (hout : m0OddResidueOneInside a h x = false) :
    m0OddResidueOneCutTape L k a b h x =
      (s1Config L (8*k+1) 0 a 0 b h).tape x := by
  simp [m0OddResidueOneCutTape,frame,hout]

private theorem sideBit_residue1_eq_residue0_after2
    (tail : List Bool) (j : Nat) (hj : 2 ≤ j) :
    sideBit (d0 ++ d1 ++ d1 ++ tail) j =
      sideBit (d1 ++ d1 ++ d1 ++ tail) j := by
  by_cases hj2 : j = 2
  · subst j
    simp [sideBit,d0,d1]
  · have hj3 : 3 ≤ j := by omega
    calc
      sideBit (d0 ++ d1 ++ d1 ++ tail) j =
          sideBit (d1 ++ d1 ++ tail) (j-3) := by
            exact sideBit_append_right d0 (d1 ++ d1 ++ tail) j
              (by simp [d0]; omega)
      _ = sideBit (d1 ++ d1 ++ d1 ++ tail) j := by
            symm
            exact sideBit_append_right d1 (d1 ++ d1 ++ tail) j
              (by simp [d1]; omega)

/-- The n=8*k+1 cut has exactly the left-facing stream of the
marker-two n=8*k successor. -/
private theorem m0OddResidueOne_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) :
    ∀ i, m0OddResidueOneCutTape L k a b h (h-(i:Int)) =
      sideBit (m0OddResidueOneLeftFacing L k a) i := by
  have hk := residueOne_quotient_bound L k hL hbound
  have hbound0 : 8*k < 2^L := by omega
  have hbin0 := binDec_residue0 L k hL hbound0
  have hbin1 := binDec_residue_one L k hL hk
  have hbin34 : binDec 3 4 = d1 ++ d1 ++ d0 := by
    have h1 : binDec 3 4 = d1 ++ binDec 2 2 := by
      simpa using binDec_even 2 2 (by decide)
    have h2 : binDec 2 2 = d1 ++ binDec 1 1 := by
      simpa using binDec_even 1 1 (by decide)
    have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
      simpa using binDec_odd 0 0 (by decide)
    simp [h1,h2,h3,binDec_zero,d1pow]
  let P : List Bool :=
    m0OddResidueOneTargetHeadPrefix a ++ d1 ++ d1
  let sourceBoundary : List Bool := m0OddResidueOneSourceHeadPrefix a
  let targetBoundary : List Bool := m0OddResidueOneTargetHeadPrefix a
  have hbaseLeft :
      m0OddQ4LeftFacing a = P ++ (d0 ++ lh) := by
    simp [m0OddQ4LeftFacing,m0OddResidueOneTargetHeadPrefix,
      P,hbin34,List.append_assoc]
  have htargetLeft :
      m0OddResidueOneLeftFacing L k a =
        P ++ (d1 ++ binDec (L-3) k ++ lh) := by
    simp [m0OddResidueOneLeftFacing,m0OddResidueOneTargetPrefix,
      m0OddResidueOneTargetHeadPrefix,P,hbin0,List.append_assoc]
  have hinputLeft :
      s1LeftFacing L (8*k+1) 0 a 0 =
        sourceBoundary ++
          (d0 ++ d1 ++ d1 ++ binDec (L-3) k ++ lh) := by
    simp [s1LeftFacing,m0OddResidueOneSourceHeadPrefix,
      sourceBoundary,binDec_zero,hbin1,List.append_assoc]
  have htargetLeftOutside :
      m0OddResidueOneLeftFacing L k a =
        targetBoundary ++
          (d1 ++ d1 ++ d1 ++ binDec (L-3) k ++ lh) := by
    simp [m0OddResidueOneLeftFacing,m0OddResidueOneTargetPrefix,
      m0OddResidueOneTargetHeadPrefix,targetBoundary,hbin0,List.append_assoc]
  have hprefixLength : P.length = 3*a+11 := by
    simp [P,m0OddResidueOneTargetHeadPrefix,
      d1pow_length,markerWord,d0,d1]
    omega
  have hsourceBoundaryLength : sourceBoundary.length = 3*a+5 := by
    simp [sourceBoundary,m0OddResidueOneSourceHeadPrefix,
      d1pow_length,markerWord,d0]
  have htargetBoundaryLength : targetBoundary.length = 3*a+5 := by
    simp [targetBoundary,m0OddResidueOneTargetHeadPrefix,
      d1pow_length,markerWord,d0]
    omega
  intro i
  by_cases hi : i ≤ 3*a+6
  · have hin : m0OddResidueOneInside a h (h-(i:Int)) = true := by
      simp [m0OddResidueOneInside]
      omega
    rw [m0OddResidueOne_cut_eq_base L k a b h (h-(i:Int)) hin]
    rw [m0Odd_q4_prefix_leftFacing a b h i]
    rw [hbaseLeft,htargetLeft]
    have hbaseBit := sideBit_append_left P (d0 ++ lh) i
      (by rw [hprefixLength]; omega)
    have htargetBit :=
      sideBit_append_left P (d1 ++ binDec (L-3) k ++ lh) i
        (by rw [hprefixLength]; omega)
    rw [hbaseBit,htargetBit]
  · have hout : m0OddResidueOneInside a h (h-(i:Int)) = false := by
      simp [m0OddResidueOneInside]
      omega
    rw [m0OddResidueOne_cut_eq_input L k a b h (h-(i:Int)) hout]
    rw [s1Config_left_cell L (8*k+1) 0 a 0 b h i]
    rw [hinputLeft,htargetLeftOutside]
    have hinputBit := sideBit_append_right sourceBoundary
      (d0 ++ d1 ++ d1 ++ binDec (L-3) k ++ lh) i
      (by rw [hsourceBoundaryLength]; omega)
    have htargetBit := sideBit_append_right targetBoundary
      (d1 ++ d1 ++ d1 ++ binDec (L-3) k ++ lh) i
      (by rw [htargetBoundaryLength]; omega)
    rw [hinputBit,htargetBit]
    have hj : 2 ≤ i-(3*a+5) := by omega
    exact sideBit_residue1_eq_residue0_after2
      (binDec (L-3) k ++ lh) (i-(3*a+5)) hj

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

private theorem m0OddResidueOne_rightShape
    (L k a b : Nat) (h : Int) :
    q4RightShape (m0OddResidueOneCutTape L k a b h) h b := by
  apply q4RightShape_congr (m0OddQ4CutTape a b h)
    (m0OddResidueOneCutTape L k a b h) h b
  · intro x hx
    have hin : m0OddResidueOneInside a h x = true := by
      simp [m0OddResidueOneInside]
      omega
    symm
    exact m0OddResidueOne_cut_eq_base L k a b h x hin
  · exact m0Odd_q4_prefix_rightShape a b h

private theorem m0OddResidueOne_far_tail
    (L k a b : Nat) (h : Int) :
    ∀ i, 9+3*b ≤ i →
      m0OddResidueOneCutTape L k a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hin : m0OddResidueOneInside a h (h+1+(i:Int)) = true := by
    simp [m0OddResidueOneInside]
    omega
  rw [m0OddResidueOne_cut_eq_base L k a b h
    (h+1+(i:Int)) hin]
  exact m0Odd_q4_prefix_far_tail a b h i hi

/-- The generic q4 suffix target is the exact marker-two successor. -/
private theorem m0OddResidueOne_target_left
    (L k a b : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+1 < 2^L) (ha : 0<a) :
    s1LeftFacing L (8*k) 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m0OddResidueOneLeftFacing L k a).drop 1 := by
  have hbinPow := binDec_pow2_sub_one (a-1) b
  have hlen : a-1+b+2 = a+b+1 := by omega
  have hexp : a-1+2 = a+1 := by omega
  have hbin : binDec (a+b+1) (2^b-1) =
      d0pow b ++ d1pow (a+1) := by
    simpa [hlen,hexp] using hbinPow
  have hbin0 := binDec_residue0 L k hL (by omega)
  unfold s1LeftFacing
  rw [hbin,hbin0]
  rw [← hexp]
  rw [d1pow_add_right (a-1) 2]
  simp [m0OddResidueOneLeftFacing,m0OddResidueOneTargetPrefix,
    m0OddResidueOneTargetHeadPrefix,List.drop,List.append_assoc]

/-- Full reset prefix for m=0,n=8*k+1, ending at marker-two n=8*k. -/
theorem m0Odd_residue1_q4_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 0 (8*k+1) a b)
      (s1Config L (8*k+1) 0 a 0 b h) =
      some (s1Config L (8*k) 2 (a+b+1) (2^b-1) 0
        (h+5+3*b)) := by
  let Tq := m0OddResidueOneCutTape L k a b h
  have hprefix := m0Odd_residue1_q4_prefix_source L k a b h hL hbound ha
  have hleft := m0OddResidueOne_leftFacing L k a b h hL hbound
  have hshape := m0OddResidueOne_rightShape L k a b h
  have htail := m0OddResidueOne_far_tail L k a b h
  have happend := m0OddResidueOne_target_left L k a b hL hbound ha
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    L (8*k) 2 (a+b+1) (2^b-1)
    (m0OddResidueOneLeftFacing L k a)
    hshape htail hleft happend
  have hsum : resetPrefixCost 0 (8*k+1) a b =
      (24+12*a)+(39+3*b) := by
    have hv : v2 (8*k+1) = 0 := by
      exact v2_of_odd (8*k+1) (by omega)
    simp [resetPrefixCost,hv]
    omega
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

/-- Complete original-TM2 m=0,n=8*k+1 increment, including the
exact geometric all-ones drain. -/
theorem m0Odd_residue1_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 0 (8*k+1) a b)
      (s1Config L (8*k+1) 0 a 0 b h) =
      some (s1Config L (8*k) 2 (a+b+1) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m0Odd_residue1_q4_reset_prefix_source
    L k a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 0 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*k) 2 (a+b+1) b (h+5+3*b)
    (s1Config L (8*k+1) 0 a 0 b h)
    (resetPrefixCost 0 (8*k+1) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms binDec_residue0
#print axioms m0Odd_residue1_q4_prefix_source
#print axioms m0Odd_residue1_q4_reset_prefix_source
#print axioms m0Odd_residue1_counted_increment_source

end BB6Coverage.Agent48M0OddResidueOneSource
