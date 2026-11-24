import M0EvenFourQ4Prefix
import M0EvenQ4Suffix
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Uniform m=0, n=8*k+4 original-source reset prefix

Lift the base n=4 q4 source prefix through its untouched high-order
binary tail. The resulting q4 suffix and counted drain give the complete
original-TM2 Rst0 increment for every admissible n=8*k+4.
-/

namespace BB6Coverage.Agent48M0EvenResidueFour

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent48M0EvenFourQ4Prefix
open BB6ChampionArithmetic
open BB6Coverage.Agent48CountedInc0

set_option maxHeartbeats 3000000

/-- Low-three-bit decomposition for every admissible n=8*k+4. -/
theorem binDec_residue4 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+4 < 2^L) :
    binDec L (8*k+4) = d1 ++ d1 ++ d0 ++ binDec (L-3) k := by
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
theorem binDec_residue3 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+3 < 2^L) :
    binDec L (8*k+3) = d0 ++ d0 ++ d1 ++ binDec (L-3) k := by
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

/-- The source prefix through the last bit touched by the n=4 bridge. -/
def m0EvenResidueFourInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d1 ++ [false,false]

/-- The matching marker-2 q4 target prefix. -/
def m0EvenResidueFourTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ d0 ++ d0 ++ [true,true]

def m0EvenResidueFourLeftFacing (L k a : Nat) : List Bool :=
  m0EvenResidueFourTargetPrefix a ++
    ([true] ++ binDec (L-3) k ++ lh)

private theorem m0EvenResidueFour_inputPrefix_length (a : Nat) :
    (m0EvenResidueFourInputPrefix a).length = 3*a+13 := by
  simp [m0EvenResidueFourInputPrefix,d1pow_length,markerWord,d0,d1]

private theorem m0EvenResidueFour_targetPrefix_length (a : Nat) (ha : 0<a) :
    (m0EvenResidueFourTargetPrefix a).length = 3*a+13 := by
  simp [m0EvenResidueFourTargetPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m0EvenResidueFour_source_left
    (L k a : Nat) (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) :
    s1LeftFacing L (8*k+4) 0 a 0 =
      m0EvenResidueFourInputPrefix a ++
        ([true] ++ binDec (L-3) k ++ lh) := by
  rw [s1LeftFacing,binDec_residue4 L k hL hbound]
  simp [m0EvenResidueFourInputPrefix,binDec_zero,d0,d1,List.append_assoc]

private theorem m0EvenResidueFour_base_input_left (a : Nat) :
    s1LeftFacing 3 4 0 a 0 =
      m0EvenResidueFourInputPrefix a ++ ([true] ++ lh) := by
  simp [s1LeftFacing,m0EvenResidueFourInputPrefix,binDec_zero,
    binDec_residue4 3 0 (by decide) (by decide),binDec_zero,d0,d1,d1pow,List.append_assoc]

private theorem m0EvenResidueFour_base_target_left (a : Nat) :
    m0EvenFourQ4LeftFacing a =
      m0EvenResidueFourTargetPrefix a ++ ([true] ++ lh) := by
  simp [m0EvenFourQ4LeftFacing,m0EvenResidueFourTargetPrefix,
    binDec_residue3 3 0 (by decide) (by decide),binDec_zero,d0,d1,d1pow,List.append_assoc]

private theorem m0EvenResidueFour_target_left
    (L k a : Nat) (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) :
    m0EvenResidueFourLeftFacing L k a =
      m0EvenResidueFourTargetPrefix a ++
        ([true] ++ binDec (L-3) k ++ lh) := by
  rfl

def m0EvenResidueFourInside (a : Nat) (h x : Int) : Bool :=
  decide (h-((3*a+12:Int)) ≤ x)

/-- The large source and base n=4 source tapes agree on the entire
half-line read by the base run. -/
private theorem m0EvenResidueFour_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) :
    ∀ x, m0EvenResidueFourInside a h x = true →
      (s1Config L (8*k+4) 0 a 0 b h).tape x =
        (s1Config 3 4 0 a 0 b h).tape x := by
  intro x hx
  by_cases hxleft : x ≤ h
  · let i : Nat := Int.toNat (h-x)
    have hcoord : x = h-(i:Int) := by
      dsimp [i]
      have hn : 0 ≤ h-x := by omega
      rw [Int.toNat_of_nonneg hn]
      omega
    have hi : i ≤ 3*a+12 := by
      have hinside := (show h-((3*a+12:Int)) ≤ x from by
        simpa [m0EvenResidueFourInside] using hx)
      have hcast : (i:Int) = h-x := Int.toNat_of_nonneg (by omega)
      omega
    have hcell := s1Config_left_cell L (8*k+4) 0 a 0 b h i
    have hbase := s1Config_left_cell 3 4 0 a 0 b h i
    have hsrc :
        s1LeftFacing L (8*k+4) 0 a 0 =
          m0EvenResidueFourInputPrefix a ++
            ([true] ++ binDec (L-3) k ++ lh) :=
      m0EvenResidueFour_source_left L k a hL hbound
    have hbaseLeft := m0EvenResidueFour_base_input_left a
    have hbits :
        sideBit (s1LeftFacing L (8*k+4) 0 a 0) i =
          sideBit (s1LeftFacing 3 4 0 a 0) i := by
      rw [hsrc,hbaseLeft]
      rw [Agent6Q4Prefix.sideBit_append_left
        (m0EvenResidueFourInputPrefix a)
        ([true] ++ binDec (L-3) k ++ lh) i (by
          rw [m0EvenResidueFour_inputPrefix_length]
          omega)]
      rw [Agent6Q4Prefix.sideBit_append_left
        (m0EvenResidueFourInputPrefix a) ([true] ++ lh) i (by
          rw [m0EvenResidueFour_inputPrefix_length]
          omega)]
    rw [← hcoord] at hcell hbase
    rw [hbits] at hcell
    exact hcell.trans hbase.symm
  · let i : Nat := Int.toNat (x-h-1)
    have hcoord : x = h+1+(i:Int) := by
      dsimp [i]
      have hn : 0 ≤ x-h-1 := by omega
      rw [Int.toNat_of_nonneg hn]
      omega
    have hcell := s1Config_right_cell L (8*k+4) 0 a 0 b h i
    have hbase := s1Config_right_cell 3 4 0 a 0 b h i
    have hbits :
        sideBit (s0RightFacing b) i = sideBit (s0RightFacing b) i := rfl
    rw [← hcoord] at hcell hbase
    simpa [s1PhysicalRight_source,sideBit,s0RightFacing] using
      hcell.trans hbase.symm

private theorem m0EvenResidueFour_config_ext (c d : Config)
    (hstate : c.state = d.state) (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  cases c
  cases d
  simp_all

/-- Frame the large source tape with the base n=4 q4 output on the
half-line that the base run reads. -/
def m0EvenResidueFourCutTape
    (L k a b : Nat) (h : Int) : Int → Bool :=
  (frame (m0EvenResidueFourInside a h)
    (s1Config L (8*k+4) 0 a 0 b h).tape
    ⟨4,h,m0EvenFourQ4CutTape a b h⟩).tape

private theorem m0EvenResidueFour_cut_eq_base
    (L k a b : Nat) (h x : Int) (hx : h ≤ x) :
    m0EvenResidueFourCutTape L k a b h x =
      m0EvenFourQ4CutTape a b h x := by
  have hin : m0EvenResidueFourInside a h x = true := by
    simp [m0EvenResidueFourInside]
    omega
  simp [m0EvenResidueFourCutTape,frame,hin]

private theorem m0EvenResidueFour_cut_eq_base_inside
    (L k a b : Nat) (h x : Int)
    (hin : m0EvenResidueFourInside a h x = true) :
    m0EvenResidueFourCutTape L k a b h x =
      m0EvenFourQ4CutTape a b h x := by
  simp [m0EvenResidueFourCutTape,frame,hin]

private theorem m0EvenResidueFour_cut_eq_input
    (L k a b : Nat) (h x : Int)
    (hout : m0EvenResidueFourInside a h x = false) :
    m0EvenResidueFourCutTape L k a b h x =
      (s1Config L (8*k+4) 0 a 0 b h).tape x := by
  simp [m0EvenResidueFourCutTape,frame,hout]

private theorem q4RightShape_congr
    (T U : Int → Bool) (h : Int) (b : Nat)
    (heq : ∀ x, h ≤ x → T x = U x)
    (hT : Agent8Q4Suffix.q4RightShape T h b) :
    Agent8Q4Suffix.q4RightShape U h b := by
  unfold Agent8Q4Suffix.q4RightShape at *
  constructor
  · intro i hi
    rw [← heq (h+(i:Int)) (by omega)]
    exact hT.1 i hi
  · constructor
    · rw [← heq (h+5) (by omega)]
      exact hT.2.1
    · constructor
      · rw [← heq (h+6) (by omega)]
        exact hT.2.2.1
      · constructor
        · intro i hi
          rw [← heq (h+7+(i:Int)) (by omega)]
          exact hT.2.2.2.1 i hi
        · intro i hi
          rw [← heq (h+10+(3*b:Int)+(i:Int)) (by omega)]
          exact hT.2.2.2.2 i hi

/-- Lift the base q4 prefix through the untouched arbitrary high-order
binary tail. -/
theorem m0Even_residue4_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    run tm2 (48+12*a)
      (s1Config L (8*k+4) 0 a 0 b h) =
      some ⟨4,h,m0EvenResidueFourCutTape L k a b h⟩ := by
  let base : Config := s1Config 3 4 0 a 0 b h
  let background := (s1Config L (8*k+4) 0 a 0 b h).tape
  have hinput := m0EvenResidueFour_input_matches L k a b h hL hbound
  have hstart :
      frame (m0EvenResidueFourInside a h) background base =
        s1Config L (8*k+4) 0 a 0 b h := by
    apply m0EvenResidueFour_config_ext
    · rfl
    · rfl
    · funext x
      by_cases hx : m0EvenResidueFourInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 48+12*a → ∀ d,
        run tm2 j base = some d →
        m0EvenResidueFourInside a h d.head = true := by
    intro j hj d hd
    have hlow := m0EvenFour_q4_prefix_head_bound a b h ha j hj d hd
    simpa [m0EvenResidueFourInside] using hlow
  have hlift := run_frame tm2 (m0EvenResidueFourInside a h)
    background base (48+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (48+12*a) base =
        some (⟨4,h,m0EvenFourQ4CutTape a b h⟩ : Config) := by
    have hrun := m0EvenFour_q4_prefix_run a b h ha
    have heq : base = ⟨3,h,(s1Config 3 4 0 a 0 b h).tape⟩ := by
      apply m0EvenResidueFour_config_ext <;> simp [base]
    rw [heq]
    exact hrun
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  have heq : frame (m0EvenResidueFourInside a h) background (⟨4,h,m0EvenFourQ4CutTape a b h⟩ : Config) = ⟨4,h,m0EvenResidueFourCutTape L k a b h⟩ := by
    apply m0EvenResidueFour_config_ext <;> rfl
  rw [heq] at hlift
  exact hlift

/-- The lifted cut agrees with the target left word on the common base
prefix and on the untouched shared boundary/high-order tail. -/
theorem m0Even_residue4_q4_prefix_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m0EvenResidueFourCutTape L k a b h (h-(i:Int)) =
        sideBit (m0EvenResidueFourLeftFacing L k a) i := by
  intro i
  by_cases hi : i ≤ 3*a+12
  · have hin : m0EvenResidueFourInside a h (h-(i:Int)) = true := by
      simp [m0EvenResidueFourInside]
      omega
    have hcut := m0EvenResidueFour_cut_eq_base_inside L k a b h
      (h-(i:Int)) hin
    have hbase := m0EvenFour_q4_prefix_leftFacing a b h ha i
    have hbaseBits :
        sideBit (m0EvenFourQ4LeftFacing a) i =
          sideBit (m0EvenResidueFourLeftFacing L k a) i := by
      rw [m0EvenResidueFour_base_target_left,
        m0EvenResidueFourLeftFacing]
      rw [Agent6Q4Prefix.sideBit_append_left
        (m0EvenResidueFourTargetPrefix a) ([true] ++ lh) i (by
          rw [m0EvenResidueFour_targetPrefix_length a ha]
          omega)]
      rw [Agent6Q4Prefix.sideBit_append_left
        (m0EvenResidueFourTargetPrefix a)
        ([true] ++ binDec (L-3) k ++ lh) i (by
          rw [m0EvenResidueFour_targetPrefix_length a ha]
          omega)]
    exact hcut.trans (hbase.trans hbaseBits)
  · have hout : m0EvenResidueFourInside a h (h-(i:Int)) = false := by
      simp [m0EvenResidueFourInside]
      omega
    have hcut := m0EvenResidueFour_cut_eq_input L k a b h
      (h-(i:Int)) hout
    have hsourceCell :=
      s1Config_left_cell L (8*k+4) 0 a 0 b h i
    have hsourceBits :
        sideBit (s1LeftFacing L (8*k+4) 0 a 0) i =
          sideBit ([true] ++ binDec (L-3) k ++ lh) (i-(3*a+13)) := by
      rw [m0EvenResidueFour_source_left L k a hL hbound]
      rw [Agent6Q4Prefix.sideBit_append_right
        (m0EvenResidueFourInputPrefix a)
        ([true] ++ binDec (L-3) k ++ lh) i (by
          rw [m0EvenResidueFour_inputPrefix_length]
          omega),m0EvenResidueFour_inputPrefix_length]
    have htargetBits :
        sideBit (m0EvenResidueFourLeftFacing L k a) i =
          sideBit ([true] ++ binDec (L-3) k ++ lh) (i-(3*a+13)) := by
      rw [m0EvenResidueFourLeftFacing]
      rw [Agent6Q4Prefix.sideBit_append_right
        (m0EvenResidueFourTargetPrefix a)
        ([true] ++ binDec (L-3) k ++ lh) i (by
          rw [m0EvenResidueFour_targetPrefix_length a ha]
          omega),m0EvenResidueFour_targetPrefix_length a ha]
    rw [hsourceBits] at hsourceCell
    calc
      m0EvenResidueFourCutTape L k a b h (h-(i:Int)) =
          (s1Config L (8*k+4) 0 a 0 b h).tape (h-(i:Int)) := hcut
      _ = sideBit ([true] ++ binDec (L-3) k ++ lh)
          (i-(3*a+13)) := hsourceCell
      _ = sideBit (m0EvenResidueFourLeftFacing L k a) i :=
        htargetBits.symm

private theorem m0Even_residue4_q4_prefix_far_tail
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m0EvenResidueFourCutTape L k a b h (h+1+(i:Int)) = false := by
  intro i hi
  rw [m0EvenResidueFour_cut_eq_base L k a b h (h+1+(i:Int)) (by omega)]
  exact m0EvenFour_q4_prefix_far_tail a b h ha i hi

private theorem m0Even_residue4_q4_prefix_rightShape
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    Agent8Q4Suffix.q4RightShape (m0EvenResidueFourCutTape L k a b h) h b := by
  apply q4RightShape_congr
    (m0EvenFourQ4CutTape a b h)
    (m0EvenResidueFourCutTape L k a b h) h b
  · intro x hx
    exact (m0EvenResidueFour_cut_eq_base L k a b h x hx).symm
  · exact m0EvenFour_q4_prefix_rightShape a b h ha

/-- Complete generalized q4 prefix interface for n=8*k+4. -/
theorem m0Even_residue4_q4_prefix_data
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    ∃ Tq,
      run tm2 (48+12*a) (s1Config L (8*k+4) 0 a 0 b h) =
        some ⟨4,h,Tq⟩ ∧
      (∀ i : Nat, Tq (h-(i:Int)) =
        sideBit (m0EvenResidueFourLeftFacing L k a) i) ∧
      Agent8Q4Suffix.q4RightShape Tq h b ∧
      (∀ i : Nat, 9+3*b ≤ i → Tq (h+1+(i:Int)) = false) := by
  refine ⟨m0EvenResidueFourCutTape L k a b h, ?_, ?_, ?_, ?_⟩
  · exact m0Even_residue4_q4_prefix_source L k a b h hL hbound ha
  · exact m0Even_residue4_q4_prefix_leftFacing L k a b h hL hbound ha
  · exact m0Even_residue4_q4_prefix_rightShape L k a b h hL hbound ha
  · exact m0Even_residue4_q4_prefix_far_tail L k a b h hL hbound ha

/-- The generic q4 suffix reconstructs the canonical n-1=8*k+3 target. -/
private theorem m0EvenResidueFour_suffix_target_left
    (L k a b : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    s1LeftFacing L (8*k+3) 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m0EvenResidueFourLeftFacing L k a).drop 1 := by
  have hbinPow := binDec_pow2_sub_one (a-1) b
  have hlen : (a-1)+b+2 = a+b+1 := by omega
  have hexp : (a-1)+2 = a+1 := by omega
  have hbin : binDec (a+b+1) (2^b-1) =
      d0pow b ++ d1pow (a+1) := by
    simpa [hlen,hexp] using hbinPow
  have hbound' : 8*k+3 < 2^L := by omega
  have hbin3 := binDec_residue3 L k hL hbound'
  unfold s1LeftFacing
  rw [hbin,hbin3]
  rw [← hexp]
  rw [d1pow_add_right (a-1) 2]
  simp [m0EvenResidueFourLeftFacing,m0EvenResidueFourTargetPrefix,
    List.drop,d0,d1,List.append_assoc]

/-- Since v2(8*k+4)=2, the reset prefix has cost 87+12a+3b. -/
private theorem m0EvenResidueFour_resetPrefixCost_eq (k a b : Nat) :
    resetPrefixCost 0 (8*k+4) a b = 87+12*a+3*b := by
  have hvOdd : BB6ChampionArithmetic.v2 (2*k+1) = 0 :=
    v2_of_odd (2*k+1) (by omega)
  have hvMid : BB6ChampionArithmetic.v2 (4*k+2) = 1 := by
    have h := v2_of_even (4*k+2) (by omega) (by omega)
    have hdiv : (4*k+2)/2 = 2*k+1 := by omega
    rw [hdiv,hvOdd] at h
    omega
  have hv : BB6ChampionArithmetic.v2 (8*k+4) = 2 := by
    have h := v2_of_even (8*k+4) (by omega) (by omega)
    have hdiv : (8*k+4)/2 = 4*k+2 := by omega
    rw [hdiv,hvMid] at h
    omega
  simp [resetPrefixCost,hv]
  omega

/-- Closed primitive-transition cost for the full Rst0 increment,
including the all-ones drain. -/
theorem m0Even_residue4_increment_cost_closed (k a b : Nat) :
    proposedIncrementCost 0 (8*k+4) a b + 9*b =
      6*4^b + 42*2^b + 12*a + 39 := by
  rw [proposedIncrementCost_decomp,
    m0EvenResidueFour_resetPrefixCost_eq]
  have h := drainCost_binary_additive b
  omega

theorem m0Even_residue4_q4_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 0 (8*k+4) a b)
      (s1Config L (8*k+4) 0 a 0 b h) =
      some (s1Config L (8*k+3) 2 (a+b+1) (2^b-1) 0
        (h+5+3*b)) := by
  obtain ⟨Tq,hprefix,hleft,hshape,htail⟩ :=
    m0Even_residue4_q4_prefix_data L k a b h hL hbound ha
  have happend := m0EvenResidueFour_suffix_target_left L k a b hL hbound ha
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    L (8*k+3) 2 (a+b+1) (2^b-1)
    (m0EvenResidueFourLeftFacing L k a)
    hshape htail hleft happend
  have hsum :
      resetPrefixCost 0 (8*k+4) a b = (48+12*a)+(39+3*b) := by
    rw [m0EvenResidueFour_resetPrefixCost_eq]
    omega
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

/-- Complete original-TM2 m=0 counted increment for every n=8*k+4,
including the exact geometric all-ones drain. -/
theorem m0Even_residue4_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 0 (8*k+4) a b)
      (s1Config L (8*k+4) 0 a 0 b h) =
      some (s1Config L (8*k+3) 2 (a+b+1) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m0Even_residue4_q4_reset_prefix_source
    L k a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 0 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*k+3) 2 (a+b+1) b (h+5+3*b)
    (s1Config L (8*k+4) 0 a 0 b h)
    (resetPrefixCost 0 (8*k+4) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms binDec_residue4
#print axioms binDec_residue3
#print axioms m0Even_residue4_increment_cost_closed
#print axioms m0Even_residue4_q4_prefix_source
#print axioms m0Even_residue4_q4_reset_prefix_source
#print axioms m0Even_residue4_counted_increment_source

end BB6Coverage.Agent48M0EvenResidueFour
