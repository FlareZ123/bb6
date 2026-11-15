import M1EvenResidueFourQ4PrefixRun
import M1EvenQ4Prefix
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Uniform m=1, n=8*k+4 original-source counted increment candidate

Lift the base n=4 q4 prefix through its untouched high-order binary tail,
then use the existing generic q4 suffix after its first four guard moves
and the counted all-ones drain.
-/

namespace BB6Coverage.Agent41M1EvenResidueFour

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent48CountedInc0
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

/-- Low-three-bit decomposition for every admissible n=8*k+4. -/
theorem m1EvenResidueFour_binDec_residue4 (L k : Nat) (hL : 3 ≤ L)
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

/-- Low-three-bit decomposition for the successor n-1=8*k+3. -/
theorem m1EvenResidueFour_binDec_residue3 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+3 < 2^L) :
    binDec L (8*k+3) = d0 ++ d0 ++ d1 ++ binDec (L-3) k := by
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
  have hq1 : 4*k+1 < 2^(L-1) := by
    rw [hpow2]
    omega
  have hq2 : 2*k < 2^(L-2) := by
    rw [hpow1]
    omega
  have h1 : binDec L (8*k+3) =
      d0 ++ binDec (L-1) (4*k+1) := by
    rw [show L = (L-1)+1 by omega,
      show 8*k+3 = 2*(4*k+1)+1 by omega]
    exact binDec_odd (L-1) (4*k+1) hq1
  have h2 : binDec (L-1) (4*k+1) =
      d0 ++ binDec (L-2) (2*k) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*k+1 = 2*(2*k)+1 by omega]
    exact binDec_odd (L-2) (2*k) hq2
  have h3 : binDec (L-2) (2*k) =
      d1 ++ binDec (L-3) k := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_even (L-3) k hk
  rw [h1,h2,h3]
  simp [List.append_assoc]

/-- Source prefix through all three low-order blocks of binDec(8*k+4). -/
def m1EvenResidueFourInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 1 ++ d0 ++ d1 ++ d1 ++ d0

/-- Target q4-cut prefix through all three low-order blocks of binDec(8*k+3). -/
def m1EvenResidueFourTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ d0 ++ d0 ++ d1

def m1EvenResidueFourLeftFacing (L k a : Nat) : List Bool :=
  m1EvenResidueFourTargetPrefix a ++ (binDec (L-3) k ++ lh)

/-- Half-line read by the base q4 prefix; every base head is in this region. -/
def m1EvenResidueFourReadInside (a : Nat) (h x : Int) : Bool :=
  decide (h-((3*a+14:Int)) ≤ x)

private theorem m1EvenResidueFour_inputPrefix_length (a : Nat) :
    (m1EvenResidueFourInputPrefix a).length = 3*a+15 := by
  simp [m1EvenResidueFourInputPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m1EvenResidueFour_targetPrefix_length (a : Nat) :
    (m1EvenResidueFourTargetPrefix a).length = 3*a+15 := by
  simp [m1EvenResidueFourTargetPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m1EvenResidueFour_source_left
    (L k a : Nat) (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) :
    s1LeftFacing L (8*k+4) 1 a 0 =
      m1EvenResidueFourInputPrefix a ++ (binDec (L-3) k ++ lh) := by
  rw [s1LeftFacing,m1EvenResidueFour_binDec_residue4 L k hL hbound]
  simp [m1EvenResidueFourInputPrefix,binDec_zero,List.append_assoc]

private theorem m1EvenResidueFour_base_input_left (a : Nat) :
    s1LeftFacing 3 4 1 a 0 =
      m1EvenResidueFourInputPrefix a ++ lh := by
  have hbin := m1EvenResidueFour_binDec_residue4 3 0 (by omega) (by decide)
  simpa [s1LeftFacing,m1EvenResidueFourInputPrefix,binDec_zero,
    binDec_zero,List.append_assoc] using hbin

private theorem m1EvenResidueFour_base_target_left (a : Nat) :
    m1EvenResidueFourQ4LeftFacing a =
      m1EvenResidueFourTargetPrefix a ++ lh := by
  simp [m1EvenResidueFourQ4LeftFacing,m1EvenResidueFourTargetPrefix,
    d0,d1,List.append_assoc]

private theorem m1EvenResidueFour_target_left
    (L k a : Nat) (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) :
    m1EvenResidueFourLeftFacing L k a =
      m1EvenResidueFourTargetPrefix a ++ (binDec (L-3) k ++ lh) := by
  rfl

/-- The large source and base n=4 source tapes agree on the entire
half-line read by the base run. -/
private theorem m1EvenResidueFour_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) :
    ∀ x, m1EvenResidueFourReadInside a h x = true →
      (s1Config L (8*k+4) 1 a 0 b h).tape x =
        (s1Config 3 4 1 a 0 b h).tape x := by
  intro x hinside
  by_cases hx : x ≤ h
  · let i : Nat := Int.toNat (h-x)
    have hcoord : x = h-(i:Int) := by
      dsimp [i]
      omega
    have hi : i ≤ 3*a+14 := by
      have hineq : h-((3*a+14:Int)) ≤ x := by
        simpa [m1EvenResidueFourReadInside] using hinside
      rw [hcoord] at hineq
      omega
    have hsource := s1Config_left_cell L (8*k+4) 1 a 0 b h i
    have hbase := s1Config_left_cell 3 4 1 a 0 b h i
    have hsourceBits :
        sideBit (s1LeftFacing L (8*k+4) 1 a 0) i =
          sideBit (m1EvenResidueFourInputPrefix a) i := by
      rw [m1EvenResidueFour_source_left L k a hL hbound]
      rw [Agent6Q4Prefix.sideBit_append_left
        (m1EvenResidueFourInputPrefix a) (binDec (L-3) k ++ lh) i (by
          rw [m1EvenResidueFour_inputPrefix_length]
          omega)]
    have hbaseBits :
        sideBit (s1LeftFacing 3 4 1 a 0) i =
          sideBit (m1EvenResidueFourInputPrefix a) i := by
      rw [m1EvenResidueFour_base_input_left]
      rw [Agent6Q4Prefix.sideBit_append_left
        (m1EvenResidueFourInputPrefix a) lh i (by
          rw [m1EvenResidueFour_inputPrefix_length]
          omega)]
    calc
      (s1Config L (8*k+4) 1 a 0 b h).tape x =
          sideBit (s1LeftFacing L (8*k+4) 1 a 0) i := by
            simpa [hcoord] using hsource
      _ = sideBit (m1EvenResidueFourInputPrefix a) i := hsourceBits
      _ = (s1Config 3 4 1 a 0 b h).tape x := by
            rw [hbaseBits]
            simpa [hcoord] using hbase.symm
  · let i : Nat := Int.toNat (x-h-1)
    have hcoord : x = h+1+(i:Int) := by
      dsimp [i]
      omega
    have hsource := s1Config_right_cell L (8*k+4) 1 a 0 b h i
    have hbase := s1Config_right_cell 3 4 1 a 0 b h i
    simpa [hcoord] using hsource.trans hbase.symm

/-- Lift the base q4 cut tape to arbitrary width by framing the base
configuration over the half-line it reads. -/
def m1EvenResidueFourLiftedCutTape
    (L k a b : Nat) (h : Int) : Int → Bool :=
  (frameAt (s1Config L (8*k+4) 1 a 0 b h).tape h
    (m1EvenResidueFourReadInside a h)
    (m1EvenResidueFourCutTape a b h)).tape

private theorem m1EvenResidueFour_cut_eq_base_inside
    (L k a b : Nat) (h x : Int)
    (hin : m1EvenResidueFourReadInside a h x = true) :
    m1EvenResidueFourLiftedCutTape L k a b h x =
      m1EvenResidueFourCutTape a b h x := by
  have hf := frameAt_tape_inside
    (s1Config L (8*k+4) 1 a 0 b h).tape h
    (m1EvenResidueFourReadInside a h)
    (m1EvenResidueFourCutTape a b h) x hin
  simpa [m1EvenResidueFourLiftedCutTape] using hf

private theorem m1EvenResidueFour_cut_eq_input
    (L k a b : Nat) (h x : Int)
    (hout : m1EvenResidueFourReadInside a h x = false) :
    m1EvenResidueFourLiftedCutTape L k a b h x =
      (s1Config L (8*k+4) 1 a 0 b h).tape x := by
  have hf := frameAt_tape_outside
    (s1Config L (8*k+4) 1 a 0 b h).tape h
    (m1EvenResidueFourReadInside a h)
    (m1EvenResidueFourCutTape a b h) x hout
  simpa [m1EvenResidueFourLiftedCutTape] using hf

/-- The original source run to the q4 cut lifts from the base n=4 run. -/
theorem m1EvenResidueFour_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    run tm2 (56+12*a) (s1Config L (8*k+4) 1 a 0 b h) =
      some ⟨4,h+4,m1EvenResidueFourLiftedCutTape L k a b h⟩ := by
  let base := s1Config 3 4 1 a 0 b h
  let background := s1Config L (8*k+4) 1 a 0 b h
  let Tq := m1EvenResidueFourCutTape a b h
  have hstart : ∀ x, m1EvenResidueFourReadInside a h x = true →
      background.tape x = base.tape x := by
    intro x hx
    exact m1EvenResidueFour_input_matches L k a b h hL hbound x hx
  have hheads :
      ∀ j, j < 56+12*a → ∀ d,
        run tm2 j base = some d →
        m1EvenResidueFourReadInside a h d.head = true := by
    intro j hj d hd
    have hlow := m1EvenResidueFour_q4_prefix_head_bound a b h j hj d hd
    simp [m1EvenResidueFourReadInside]
    omega
  have hlift := run_frame tm2 (m1EvenResidueFourReadInside a h)
    background base (56+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (56+12*a) base =
        some (⟨4,h+4,Tq⟩ : Config) := by
    have hrun := m1EvenResidueFour_q4_prefix_run a b h
    simpa [base,Tq] using hrun
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  simpa [m1EvenResidueFourLiftedCutTape,background] using hlift

/-- The lifted cut agrees with the target left word on the common base
prefix and on the untouched shared high-order tail. -/
theorem m1EvenResidueFour_q4_prefix_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m1EvenResidueFourLiftedCutTape L k a b h (h-(i:Int)) =
        sideBit (m1EvenResidueFourLeftFacing L k a) i := by
  intro i
  by_cases hi : i ≤ 3*a+14
  · have hin : m1EvenResidueFourReadInside a h (h-(i:Int)) = true := by
      simp [m1EvenResidueFourReadInside]
      omega
    have hcut := m1EvenResidueFour_cut_eq_base_inside L k a b h
      (h-(i:Int)) hin
    have hbase := m1EvenResidueFour_q4_prefix_leftFacing a b h ha i
    have hbaseBits :
        sideBit (m1EvenResidueFourQ4LeftFacing a) i =
          sideBit (m1EvenResidueFourLeftFacing L k a) i := by
      rw [m1EvenResidueFour_base_target_left,
        m1EvenResidueFourLeftFacing]
      rw [Agent6Q4Prefix.sideBit_append_left
        (m1EvenResidueFourTargetPrefix a) lh i (by
          rw [m1EvenResidueFour_targetPrefix_length]
          omega)]
      rw [Agent6Q4Prefix.sideBit_append_left
        (m1EvenResidueFourTargetPrefix a)
        (binDec (L-3) k ++ lh) i (by
          rw [m1EvenResidueFour_targetPrefix_length]
          omega)]
    exact hcut.trans (hbase.trans hbaseBits)
  · have hout : m1EvenResidueFourReadInside a h (h-(i:Int)) = false := by
      simp [m1EvenResidueFourReadInside]
      omega
    have hcut := m1EvenResidueFour_cut_eq_input L k a b h
      (h-(i:Int)) hout
    have hsourceCell :=
      s1Config_left_cell L (8*k+4) 1 a 0 b h i
    have hsourceBits :
        sideBit (s1LeftFacing L (8*k+4) 1 a 0) i =
          sideBit (binDec (L-3) k ++ lh) (i-(3*a+15)) := by
      rw [m1EvenResidueFour_source_left L k a hL hbound]
      rw [Agent6Q4Prefix.sideBit_append_right
        (m1EvenResidueFourInputPrefix a)
        (binDec (L-3) k ++ lh) i (by
          rw [m1EvenResidueFour_inputPrefix_length]
          omega)]
    have htargetBits :
        sideBit (m1EvenResidueFourLeftFacing L k a) i =
          sideBit (binDec (L-3) k ++ lh) (i-(3*a+15)) := by
      rw [m1EvenResidueFourLeftFacing]
      rw [Agent6Q4Prefix.sideBit_append_right
        (m1EvenResidueFourTargetPrefix a)
        (binDec (L-3) k ++ lh) i (by
          rw [m1EvenResidueFour_targetPrefix_length]
          omega)]
    rw [hsourceBits] at hsourceCell
    calc
      m1EvenResidueFourLiftedCutTape L k a b h (h-(i:Int)) =
          (s1Config L (8*k+4) 1 a 0 b h).tape (h-(i:Int)) := hcut
      _ = sideBit (binDec (L-3) k ++ lh) (i-(3*a+15)) := hsourceCell
      _ = sideBit (m1EvenResidueFourLeftFacing L k a) i :=
        htargetBits.symm

private theorem m1EvenResidueFour_q4_prefix_far_tail
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m1EvenResidueFourLiftedCutTape L k a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hin : m1EvenResidueFourReadInside a h (h+1+(i:Int)) = true := by
    simp [m1EvenResidueFourReadInside]
    omega
  rw [m1EvenResidueFour_cut_eq_base_inside L k a b h
    (h+1+(i:Int)) hin]
  exact m1EvenResidueFour_q4_prefix_far_tail a b h ha i hi

private theorem m1EvenResidueFour_q4_prefix_rightShape
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    q4RightShape (m1EvenResidueFourLiftedCutTape L k a b h) h b := by
  apply q4RightShape_congr
    (m1EvenResidueFourCutTape a b h)
    (m1EvenResidueFourLiftedCutTape L k a b h) h b
  · intro x hx
    have hin : m1EvenResidueFourReadInside a h x = true := by
      simp [m1EvenResidueFourReadInside]
      omega
    exact (m1EvenResidueFour_cut_eq_base_inside L k a b h x hin).symm
  · exact m1EvenResidueFour_q4_prefix_rightShape a b h ha

/-- Complete generalized q4 prefix interface for n=8*k+4, with head h+4
after the first four state-4 guard moves have already been consumed. -/
theorem m1EvenResidueFour_q4_prefix_data
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    ∃ Tq,
      run tm2 (56+12*a) (s1Config L (8*k+4) 1 a 0 b h) =
        some ⟨4,h+4,Tq⟩ ∧
      (∀ i : Nat, Tq (h-(i:Int)) =
        sideBit (m1EvenResidueFourLeftFacing L k a) i) ∧
      q4RightShape Tq h b ∧
      (∀ i : Nat, 9+3*b ≤ i → Tq (h+1+(i:Int)) = false) := by
  refine ⟨m1EvenResidueFourLiftedCutTape L k a b h, ?_, ?_, ?_, ?_⟩
  · exact m1EvenResidueFour_q4_prefix_source L k a b h hL hbound ha
  · exact m1EvenResidueFour_q4_prefix_leftFacing L k a b h hL hbound ha
  · exact m1EvenResidueFour_q4_prefix_rightShape L k a b h hL hbound ha
  · exact m1EvenResidueFour_q4_prefix_far_tail L k a b h hL hbound ha

/-- The generic q4 suffix reconstructs the canonical n-1=8*k+3 target. -/
private theorem m1EvenResidueFour_suffix_target_left
    (L k a b : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+4 < 2^L) :
    s1LeftFacing L (8*k+3) 0 (a+b+2) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m1EvenResidueFourLeftFacing L k a).drop 1 := by
  have hbinPow := binDec_pow2_sub_one a b
  have hbin : binDec (a+b+2) (2^b-1) =
      d0pow b ++ d1pow (a+2) := by
    simpa using hbinPow
  have hbound' : 8*k+3 < 2^L := by omega
  have hbin3 := m1EvenResidueFour_binDec_residue3 L k hL hbound'
  unfold s1LeftFacing
  rw [hbin,hbin3]
  rw [d1pow_add_right a 2]
  simp [m1EvenResidueFourLeftFacing,m1EvenResidueFourTargetPrefix,
    List.drop,List.append_assoc]

/-- Since v2(8*k+4)=2, the reset prefix has cost 91+12a+3b. -/
private theorem m1EvenResidueFour_resetPrefixCost_eq (k a b : Nat) :
    resetPrefixCost 1 (8*k+4) a b = 91+12*a+3*b := by
  have hvOdd : BB6ChampionArithmetic.v2 (2*k+1) = 0 :=
    v2_of_odd (2*k+1) (by omega)
  have hvMid : BB6ChampionArithmetic.v2 (4*k+2) = 1 := by
    have h := v2_of_even (4*k+2) (by omega)
    have hdiv : (4*k+2)/2 = 2*k+1 := by omega
    rw [hdiv,hvOdd] at h
    omega
  have hv : BB6ChampionArithmetic.v2 (8*k+4) = 2 := by
    have h := v2_of_even (8*k+4) (by omega)
    have hdiv : (8*k+4)/2 = 4*k+2 := by omega
    rw [hdiv,hvMid] at h
    omega
  simp [resetPrefixCost,hv]
  omega

/-- Closed primitive-transition cost for the full m=1 increment,
including the all-ones drain. -/
theorem m1EvenResidueFour_increment_cost_closed (k a b : Nat) :
    proposedIncrementCost 1 (8*k+4) a b + 9*b =
      6*4^b + 42*2^b + 12*a + 43 := by
  rw [proposedIncrementCost_decomp,
    m1EvenResidueFour_resetPrefixCost_eq]
  have h := drainCost_binary_additive b
  omega

/-- Full source-level m=1 reset prefix for every admissible n=8*k+4. -/
theorem m1EvenResidueFour_q4_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 1 (8*k+4) a b)
      (s1Config L (8*k+4) 1 a 0 b h) =
      some (s1Config L (8*k+3) 0 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  obtain ⟨Tq,hprefix,hleft,hshape,htail⟩ :=
    m1EvenResidueFour_q4_prefix_data L k a b h hL hbound ha
  have happend := m1EvenResidueFour_suffix_target_left L k a b hL hbound
  have hwhole := q4_suffix_run_to_s1Config Tq h b
    L (8*k+3) 0 (a+b+2) (2^b-1)
    (m1EvenResidueFourLeftFacing L k a)
    hshape htail hleft happend
  have hfirst := m1EvenQ4First4_at Tq h hshape.1
  have hnum : 39+3*b = 4+(35+3*b) := by omega
  rw [hnum,run_append,hfirst] at hwhole
  simp only [Option.bind_some] at hwhole
  have hsum :
      resetPrefixCost 1 (8*k+4) a b = (56+12*a)+(35+3*b) := by
    rw [m1EvenResidueFour_resetPrefixCost_eq]
    omega
  rw [hsum,run_append,hprefix]
  simp only [Option.bind_some]
  exact hwhole

/-- Complete original-TM2 m=1 counted increment for every n=8*k+4,
including the exact geometric all-ones drain. -/
theorem m1EvenResidueFour_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 1 (8*k+4) a b)
      (s1Config L (8*k+4) 1 a 0 b h) =
      some (s1Config L (8*k+3) 0 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m1EvenResidueFour_q4_reset_prefix_source
    L k a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 1 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*k+3) 0 (a+b+2) b (h+5+3*b)
    (s1Config L (8*k+4) 1 a 0 b h)
    (resetPrefixCost 1 (8*k+4) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms m1EvenResidueFour_binDec_residue4
#print axioms m1EvenResidueFour_binDec_residue3
#print axioms m1EvenResidueFour_increment_cost_closed
#print axioms m1EvenResidueFour_q4_prefix_source
#print axioms m1EvenResidueFour_q4_reset_prefix_source
#print axioms m1EvenResidueFour_counted_increment_source

end BB6Coverage.Agent41M1EvenResidueFour
