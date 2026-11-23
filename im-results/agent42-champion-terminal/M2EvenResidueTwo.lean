import M2EvenSixQ4Prefix
import M0EvenSixHeadBound
import Lean.Elab.Tactic.Omega

/-!
# Uniform m=2, n = 2 (mod 8) source reset prefix

The 38-step n=6 q4 bridge reads only the first five bits of the inner
BinDec word after the marker and digit blocks. Every n=8*k+2 has the
same five-bit input boundary, and its n-1 target has the same five-bit
output boundary. From the sixth bit onward the source and target
BinDec tails agree exactly, so the finite bridge lifts through a
half-line frame without assumptions about the higher-order tail.

This is the marker-2 row (not the distinct marker-0 or marker-1 rows
with the same numeric residue).

This establishes an original-table source reset prefix for every
admissible n=8*k+2. It is an intermediate result, not a complete
TM63 itinerary or a BB(6) upper bound.
-/

namespace BB6Coverage.Agent42M2EvenResidueTwo

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent48M2EvenSixQ4
open BB6Coverage.Agent42M0EvenSixHeadBound
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

theorem binDec_residue2 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+2 < 2^L) :
    binDec L (8*k+2) =
      d1 ++ d0 ++ d1 ++ binDec (L-3) k := by
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
  have hk : k < 2^(L-3) := by rw [hpow3] at hbound; omega
  have hq1 : 4*k+1 < 2^(L-1) := by rw [hpow2]; rw [hpow3] at hbound; omega
  have hq2 : 2*k < 2^(L-2) := by rw [hpow1]; rw [hpow3] at hbound; omega
  have h1 : binDec L (8*k+2) =
      d1 ++ binDec (L-1) (4*k+1) := by
    rw [show L = (L-1)+1 by omega,
      show 8*k+2 = 2*(4*k+1) by omega]
    exact binDec_even (L-1) (4*k+1) hq1
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

theorem binDec_residue1 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+1 < 2^L) :
    binDec L (8*k+1) =
      d0 ++ d1 ++ d1 ++ binDec (L-3) k := by
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
  have hk : k < 2^(L-3) := by rw [hpow3] at hbound; omega
  have hq1 : 4*k < 2^(L-1) := by rw [hpow2]; rw [hpow3] at hbound; omega
  have hq2 : 2*k < 2^(L-2) := by rw [hpow1]; rw [hpow3] at hbound; omega
  have h1 : binDec L (8*k+1) =
      d0 ++ binDec (L-1) (4*k) := by
    rw [show L = (L-1)+1 by omega,
      show 8*k+1 = 2*(4*k)+1 by omega]
    exact binDec_odd (L-1) (4*k) hq1
  have h2 : binDec (L-1) (4*k) =
      d1 ++ binDec (L-2) (2*k) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*k = 2*(2*k) by omega]
    exact binDec_even (L-2) (2*k) hq2
  have h3 : binDec (L-2) (2*k) =
      d1 ++ binDec (L-3) k := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_even (L-3) k hk
  rw [h1,h2,h3]
  simp [List.append_assoc]

private theorem binDec_three_six :
    binDec 3 6 = d1 ++ d0 ++ d0 := by decide

private theorem binDec_three_five :
    binDec 3 5 = d0 ++ d1 ++ d0 := by decide

private def m2EvenResidueTwoInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 2 ++ d0 ++ d1 ++ [false,false]

private def m2EvenResidueTwoTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ [true,true]

private def m2EvenResidueTwoSharedTail (L k : Nat) : List Bool :=
  [true] ++ d1 ++ binDec (L-3) k ++ lh

private def m2EvenResidueTwoBaseTail : List Bool :=
  [true] ++ d0 ++ lh

private theorem m2EvenResidueTwoInputPrefix_length (a : Nat) :
    (m2EvenResidueTwoInputPrefix a).length = 3*a+12 := by
  simp [m2EvenResidueTwoInputPrefix,d1pow_length,markerWord,d0,d1] <;> omega

private theorem m2EvenResidueTwoTargetPrefix_length (a : Nat) :
    (m2EvenResidueTwoTargetPrefix a).length = 3*a+12 := by
  simp [m2EvenResidueTwoTargetPrefix,d1pow_length,markerWord,d0,d1] <;> omega

private theorem m2EvenResidueTwo_source_base_left (a : Nat) :
    s1LeftFacing 3 6 2 a 0 =
      m2EvenResidueTwoInputPrefix a ++ m2EvenResidueTwoBaseTail := by
  simp [s1LeftFacing,m2EvenResidueTwoInputPrefix,
    m2EvenResidueTwoBaseTail,binDec_three_six,d0,d1,List.append_assoc]

private theorem m2EvenResidueTwo_target_base_left (a : Nat) :
    BB6Coverage.Agent8Q4Suffix.q4LeftFacing 3 5 a =
      m2EvenResidueTwoTargetPrefix a ++ m2EvenResidueTwoBaseTail := by
  simp [BB6Coverage.Agent8Q4Suffix.q4LeftFacing,m2EvenResidueTwoTargetPrefix,
    m2EvenResidueTwoBaseTail,binDec_three_five,d0,d1,List.append_assoc]

private theorem m2EvenResidueTwo_source_left
    (L k a : Nat) (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) :
    s1LeftFacing L (8*k+2) 2 a 0 =
      m2EvenResidueTwoInputPrefix a ++
        m2EvenResidueTwoSharedTail L k := by
  simp [s1LeftFacing,m2EvenResidueTwoInputPrefix,
    m2EvenResidueTwoSharedTail,binDec_residue2 L k hL hbound,
    d0,d1,List.append_assoc]

private theorem m2EvenResidueTwo_target_left
    (L k a : Nat) (hL : 3 ≤ L) (hbound : 8*k+1 < 2^L) :
    BB6Coverage.Agent8Q4Suffix.q4LeftFacing L (8*k+1) a =
      m2EvenResidueTwoTargetPrefix a ++
        m2EvenResidueTwoSharedTail L k := by
  simp [BB6Coverage.Agent8Q4Suffix.q4LeftFacing,m2EvenResidueTwoTargetPrefix,
    m2EvenResidueTwoSharedTail,binDec_residue1 L k hL hbound,
    d0,d1,List.append_assoc]

private theorem m2EvenResidueTwo_config_ext (c d : Config)
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

private def m2EvenResidueTwoSourceLeftSuffix : List Bool :=
  markerWord 2 ++ (d0 ++ (binDec 3 6 ++ lh))

noncomputable def m2EvenResidueTwoBaseTape
    (a b : Nat) (h : Int) (ha : 0<a) : Int → Bool :=
  Classical.choose (m2EvenSix_q4_prefix_data a b h ha)

private theorem m2EvenResidueTwoBaseTape_spec
    (a b : Nat) (h : Int) (ha : 0<a) :
    run tm2 (44+12*a) (s1Config 3 6 2 a 0 b h) =
      some (⟨4,h,m2EvenResidueTwoBaseTape a b h ha⟩ : Config) ∧
    (∀ i : Nat,
      m2EvenResidueTwoBaseTape a b h ha (h-(i:Int)) =
        sideBit (m2EvenSixQ4LeftFacing a) i) ∧
    BB6Coverage.Agent8Q4Suffix.BB6Coverage.Agent8Q4Suffix.q4RightShape
      (m2EvenResidueTwoBaseTape a b h ha) h b ∧
    (∀ i : Nat,
      m2EvenResidueTwoBaseTape a b h ha (h+1+(i:Int)) =
        sideBit (BB6Coverage.Agent8Q4Suffix.BB6Coverage.Agent8Q4Suffix.q4RightFacing b) i) := by
  simpa [m2EvenResidueTwoBaseTape] using
    (Classical.choose_spec (m2EvenSix_q4_prefix_data a b h ha))

def m2EvenResidueTwoInside (a : Nat) (h : Int) : Int → Bool :=
  fun x => decide (h-((3*a+11:Int)) ≤ x)

noncomputable def m2EvenResidueTwoCutTape
    (L k a b : Nat) (h : Int) (ha : 0<a) : Int → Bool :=
  (frame (m2EvenResidueTwoInside a h)
    (s1Config L (8*k+2) 2 a 0 b h).tape
    (⟨4,h,m2EvenResidueTwoBaseTape a b h ha⟩ : Config)).tape

private theorem m2EvenResidueTwo_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) :
    ∀ x, m2EvenResidueTwoInside a h x = true →
      (s1Config L (8*k+2) 2 a 0 b h).tape x =
      (s1Config 3 6 2 a 0 b h).tape x := by
  have hsourceLeft :=
    m2EvenResidueTwo_source_left L k a hL hbound
  have hbaseLeft := m2EvenResidueTwo_source_base_left a
  have hprefixLength := m2EvenResidueTwoInputPrefix_length a
  intro x hx
  by_cases hleft : x ≤ h
  · let i := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i:Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int)=x := by omega
    have hthreshold :
        h-((3*a+11:Int)) ≤ x := by
      simpa [m2EvenResidueTwoInside] using hx
    have hi : i ≤ 3*a+11 := by dsimp [i] at *; omega
    have hiPrefix :
        i < (m2EvenResidueTwoInputPrefix a).length := by
      rw [hprefixLength]
      omega
    have hsrc := s1Config_left_cell L (8*k+2) 2 a 0 b h i
    have hbase := s1Config_left_cell 3 6 2 a 0 b h i
    rw [hcoord] at hsrc hbase
    rw [hsourceLeft] at hsrc
    rw [hbaseLeft] at hbase
    have hsrcBit := sideBit_append_left
      (m2EvenResidueTwoInputPrefix a)
      (m2EvenResidueTwoSharedTail L k) i hiPrefix
    have hbaseBit := sideBit_append_left
      (m2EvenResidueTwoInputPrefix a)
      m2EvenResidueTwoBaseTail i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbase
    exact hsrc.trans hbase.symm
  · let i := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i:Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int)=x := by omega
    have hsrc := s1Config_right_cell L (8*k+2) 2 a 0 b h i
    have hbase := s1Config_right_cell 3 6 2 a 0 b h i
    rw [hcoord] at hsrc hbase
    exact hsrc.trans hbase.symm

private theorem m2EvenResidueTwo_cut_eq_base_inside
    (L k a b : Nat) (h x : Int) (ha : 0<a)
    (hin : m2EvenResidueTwoInside a h x = true) :
    m2EvenResidueTwoCutTape L k a b h ha x =
      m2EvenResidueTwoBaseTape a b h ha x := by
  simp [m2EvenResidueTwoCutTape,frame,hin]

private theorem m2EvenResidueTwo_cut_eq_input
    (L k a b : Nat) (h x : Int) (ha : 0<a)
    (hout : m2EvenResidueTwoInside a h x = false) :
    m2EvenResidueTwoCutTape L k a b h ha x =
      (s1Config L (8*k+2) 2 a 0 b h).tape x := by
  simp [m2EvenResidueTwoCutTape,frame,hout]

private theorem q4RightShape_congr
    (T U : Int → Bool) (h : Int) (b : Nat)
    (heq : ∀ x, h ≤ x → T x = U x)
    (hT : BB6Coverage.Agent8Q4Suffix.BB6Coverage.Agent8Q4Suffix.q4RightShape T h b) :
    BB6Coverage.Agent8Q4Suffix.BB6Coverage.Agent8Q4Suffix.q4RightShape U h b := by
  unfold BB6Coverage.Agent8Q4Suffix.BB6Coverage.Agent8Q4Suffix.q4RightShape at *
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

def m2EvenResidueTwoLeftFacing (L k a : Nat) : List Bool :=
  BB6Coverage.Agent8Q4Suffix.q4LeftFacing L (8*k+1) a

private theorem m2EvenResidueTwo_base_target_bit
    (a i : Nat) (hi : i < 3*a+12) :
    sideBit (m2EvenSixQ4LeftFacing a) i =
      sideBit (m2EvenResidueTwoTargetPrefix a) i := by
  have hface := m2EvenSixQ4LeftFacing_eq_q4LeftFacing a
  have hbase := m2EvenResidueTwo_target_base_left a
  rw [hface,hbase]
  have hside := sideBit_append_left
    (m2EvenResidueTwoTargetPrefix a) m2EvenResidueTwoBaseTail i
    (by rw [m2EvenResidueTwoTargetPrefix_length]; exact hi)
  simpa using hside

private theorem m2EvenResidueTwo_target_bit
    (L k a : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+2 < 2^L) (i : Nat) (hi : i < 3*a+12) :
    sideBit (BB6Coverage.Agent8Q4Suffix.q4LeftFacing L (8*k+1) a) i =
      sideBit (m2EvenResidueTwoTargetPrefix a) i := by
  have htarget :=
    m2EvenResidueTwo_target_left L k a hL (by omega)
  rw [htarget]
  have hside := sideBit_append_left
    (m2EvenResidueTwoTargetPrefix a)
    (m2EvenResidueTwoSharedTail L k) i
    (by rw [m2EvenResidueTwoTargetPrefix_length]; exact hi)
  simpa using hside

private theorem m2EvenResidueTwo_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m2EvenResidueTwoCutTape L k a b h ha (h-(i:Int)) =
        sideBit (m2EvenResidueTwoLeftFacing L k a) i := by
  have hsourceLeft :=
    m2EvenResidueTwo_source_left L k a hL hbound
  have htargetLeft :=
    m2EvenResidueTwo_target_left L k a hL (by omega)
  have hbaseTarget :=
    m2EvenResidueTwo_target_base_left a
  have hprefixLength := m2EvenResidueTwoTargetPrefix_length a
  have hbaseLeft : ∀ i : Nat,
      m2EvenResidueTwoBaseTape a b h ha (h-(i:Int)) =
        sideBit (m2EvenSixQ4LeftFacing a) i :=
    (m2EvenResidueTwoBaseTape_spec a b h ha).2.1
  intro i
  by_cases hi : i ≤ 3*a+11
  · have hin :
      m2EvenResidueTwoInside a h (h-(i:Int)) = true := by
      simp [m2EvenResidueTwoInside]
      omega
    rw [m2EvenResidueTwo_cut_eq_base_inside L k a b h
      (h-(i:Int)) ha hin]
    have hbase := hbaseLeft i
    rw [m2EvenSixQ4LeftFacing_eq_q4LeftFacing] at hbase
    rw [hbaseTarget] at hbase
    have hbaseBit := sideBit_append_left
      (m2EvenResidueTwoTargetPrefix a) m2EvenResidueTwoBaseTail i
      (by rw [hprefixLength]; omega)
    rw [hbaseBit] at hbase
    rw [m2EvenResidueTwoLeftFacing,htargetLeft]
    have htargetBit := sideBit_append_left
      (m2EvenResidueTwoTargetPrefix a)
      (m2EvenResidueTwoSharedTail L k) i
      (by rw [hprefixLength]; omega)
    rw [htargetBit]
    exact hbase
  · have hout :
      m2EvenResidueTwoInside a h (h-(i:Int)) = false := by
      simp [m2EvenResidueTwoInside]
      omega
    rw [m2EvenResidueTwo_cut_eq_input L k a b h
      (h-(i:Int)) ha hout]
    have hcell := s1Config_left_cell L (8*k+2) 2 a 0 b h i
    rw [hsourceLeft] at hcell
    rw [m2EvenResidueTwoLeftFacing,htargetLeft]
    have hsrcBit := sideBit_append_right
      (m2EvenResidueTwoInputPrefix a)
      (m2EvenResidueTwoSharedTail L k) i
      (by rw [m2EvenResidueTwoInputPrefix_length]; omega)
    have htgtBit := sideBit_append_right
      (m2EvenResidueTwoTargetPrefix a)
      (m2EvenResidueTwoSharedTail L k) i
      (by rw [m2EvenResidueTwoTargetPrefix_length]; omega)
    rw [hsrcBit] at hcell
    rw [htgtBit]
    exact hcell

private theorem m2EvenResidueTwo_rightFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m2EvenResidueTwoCutTape L k a b h ha (h+1+(i:Int)) =
        sideBit (BB6Coverage.Agent8Q4Suffix.q4RightFacing b) i := by
  intro i
  have hbase :=
    (m2EvenResidueTwoBaseTape_spec a b h ha).2.2.2.2 i
  have hin :
      m2EvenResidueTwoInside a h (h+1+(i:Int)) = true := by
    simp [m2EvenResidueTwoInside]
    omega
  rw [m2EvenResidueTwo_cut_eq_base_inside L k a b h
    (h+1+(i:Int)) ha hin]
  exact hbase

private theorem m2EvenResidueTwo_prefix_rightShape
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    BB6Coverage.Agent8Q4Suffix.q4RightShape
      (m2EvenResidueTwoCutTape L k a b h ha) h b := by
  apply q4RightShape_congr
    (m2EvenResidueTwoBaseTape a b h ha)
    (m2EvenResidueTwoCutTape L k a b h ha) h b
  · intro x hx
    have hin : m2EvenResidueTwoInside a h x = true := by
      simp [m2EvenResidueTwoInside]
      omega
    exact (m2EvenResidueTwo_cut_eq_base_inside L k a b h x ha hin).symm
  · exact (m2EvenResidueTwoBaseTape_spec a b h ha).2.2.1

private theorem fRun_prefix_exists {m c n k d}
    (h : fRun m n c = some d) (hk : k ≤ n) :
    ∃ e, fRun m k c = some e := by
  induction n generalizing k c d with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      exact ⟨c,by simpa [fRun] using h⟩
  | succ n ih =>
      have h' : (fRun m n c).bind (fStep m) = some d := by
        simpa [fRun] using h
      cases hp : fRun m n c with
      | none => simp [hp] at h'
      | some e =>
          by_cases hk' : k ≤ n
          · exact ih hp hk'
          · have hkEq : k=n+1 := by omega
            subst k
            exact ⟨d,h⟩

private theorem m2EvenSix_bridge_prefix_lower
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ y, m2EvenSixQ4Inside y = true →
      T (h+y) = decide (y ∈ m2EvenSixQ4BridgeStart.marked))
    (j : Nat) (hj : j < 38) (d : Config)
    (hd : run tm2 j ⟨3,h,T⟩ = some d) :
    h-9 ≤ d.head := by
  obtain ⟨e,hexact⟩ :=
    fRun_prefix_exists (k := j) m2EvenSixQ4Bridge_exact (by omega)
  have hcheckj :
      (List.range j).all (fun k =>
        match fRun tm2 k m2EvenSixQ4BridgeStart with
        | none => true
        | some f => m2EvenSixQ4Inside f.head) = true := by
    apply List.all_eq_true.mpr
    intro k hk
    have hj' : k < 38 := by
      have hmem := List.mem_range.mp hk
      omega
    exact (List.all_eq_true.mp m2EvenSixQ4Bridge_heads) k
      (List.mem_range.mpr hj')
  have hbridge := bridgeAt T h m2EvenSixQ4Inside
    m2EvenSixQ4BridgeStart e j rfl hexact hcheckj hmatch
  rw [hbridge] at hd
  have hdeq : d = frameAt T h m2EvenSixQ4Inside e :=
    Option.some.inj hd
  have hinside : m2EvenSixQ4Inside e.head = true := by
    have hh := (List.all_eq_true.mp m2EvenSixQ4Bridge_heads) j
      (List.mem_range.mpr hj)
    simpa [hexact] using hh
  have hlow : -9 ≤ e.head := by
    simp [m2EvenSixQ4Inside] at hinside
    omega
  rw [hdeq]
  simp [frameAt_head]
  omega

private theorem E_scan_prefix_head
    (T : Int → Bool) (h : Int) (n : Nat)
    (hlinear : linearRightOnes T h n)
    (j : Nat) (hj : j < n) (d : Config)
    (hd : run tm2 j ⟨4,h,T⟩ = some d) :
    d.head = h+(j:Int) := by
  have hlinearJ : linearRightOnes T h j := by
    intro i hi
    exact hlinear i (by omega)
  have hrun := E_scan T h j hlinearJ
  rw [hrun] at hd
  have heq := Option.some.inj hd
  have hhead := congrArg Config.head heq
  exact hhead.symm

private theorem m2EvenSix_q4_prefix_head_bound
    (a b : Nat) (h : Int) (ha : 0<a) :
    ∀ k, k < 44+12*a → ∀ d,
      run tm2 k (s1Config 3 6 2 a 0 b h) = some d →
      h-((3*a+2:Int))-9 ≤ d.head := by
  let T := (s1Config 3 6 2 a 0 b h).tape
  let N := 3*a+2
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m2EvenSixQ4CutTape a b h
  have hface : s1LeftFacing 3 6 2 a 0 =
      d1pow a ++ m2EvenResidueTwoSourceLeftSuffix := by
    simp [s1LeftFacing,binDec_zero,m2EvenResidueTwoSourceLeftSuffix,
      List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 6 2 a 0 b h i
    rw [hface] at hcell
    by_cases hi3 : i < 3*a
    · have hside := sideBit_append_left (d1pow a)
        m2EvenResidueTwoSourceLeftSuffix i (by rw [d1pow_length]; omega)
      rw [hside] at hcell
      have hbit := sideBit_d1pow_true a i hi3
      exact hcell.trans hbit
    · have hcases : i=3*a ∨ i=3*a+1 := by omega
      rcases hcases with hi0|hi1
      · subst i
        have hside := sideBit_append_right (d1pow a)
          m2EvenResidueTwoSourceLeftSuffix (3*a) (by rw [d1pow_length]; omega)
        rw [hside] at hcell
        simpa [m2EvenResidueTwoSourceLeftSuffix,markerWord,sideBit] using hcell
      · subst i
        have hside := sideBit_append_right (d1pow a)
          m2EvenResidueTwoSourceLeftSuffix (3*a+1) (by rw [d1pow_length]; omega)
        rw [hside] at hcell
        simpa [m2EvenResidueTwoSourceLeftSuffix,markerWord,sideBit] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 6 2 a 0 b h 0
    simpa [T,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hc
  have hSweep :
      run tm2 (3*N) ⟨3,h,T⟩ =
        some ⟨3,h-(N:Int),T1⟩ := by
    simpa [T1] using counted_left_sweep N T h hOn hright
  have hmatch := m2EvenSixQ4Bridge_input_match a b h
  have hBridge :
      run tm2 38 ⟨3,hN,T1⟩ =
        some ⟨4,hN+2,T2⟩ := by
    have hb := bridgeAt T1 hN m2EvenSixQ4Inside
      m2EvenSixQ4BridgeStart m2EvenSixQ4BridgeEnd 38 rfl
      m2EvenSixQ4Bridge_exact m2EvenSixQ4Bridge_heads hmatch
    have hframe :
        frameAt T1 hN m2EvenSixQ4Inside m2EvenSixQ4BridgeEnd =
          (⟨4,hN+2,T2⟩ : Config) := by
      apply m2EvenResidueTwo_config_ext
      · simp [frameAt_state,m2EvenSixQ4BridgeEnd]
      · simp [frameAt_head,m2EvenSixQ4BridgeEnd]
        omega
      · rfl
    rw [hframe] at hb
    exact hb
  have hlinear : linearRightOnes T2 (hN+2) (3*a) := by
    simpa [T2,hN,N] using
      m2EvenSixQ4CutTape_linearRightOnes a b h ha
  intro k hk d hd
  let p1 := 3*N
  let p2 := p1+38
  by_cases hk1 : k < p1
  · have hlow := counted_left_sweep_heads N T h hOn hright k
      (by dsimp [p1] at *; omega) d hd
    dsimp [hN,N] at *
    omega
  · by_cases hk2 : k < p2
    · let j := k-p1
      have hj : j<38 := by dsimp [j,p1] at *; omega
      have hkEq : k=p1+j := by dsimp [j,p1]; omega
      rw [hkEq,run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      have hlow := m2EvenSix_bridge_prefix_lower T1 hN hmatch j hj d hd
      dsimp [hN,N] at *
      omega
    · let j := k-p2
      have hj : j<3*a := by dsimp [j,p2,p1,N] at *; omega
      have hkEq : k=p1+(38+j) := by dsimp [j,p2,p1]; omega
      rw [hkEq,run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      rw [run_add,hBridge] at hd
      simp only [Option.bind_some] at hd
      have hhead := E_scan_prefix_head T2 (hN+2) (3*a) hlinear j hj d hd
      dsimp [hN,N] at *
      omega

theorem m2Even_residue2_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    run tm2 (44+12*a)
      (s1Config L (8*k+2) 2 a 0 b h) =
      some ⟨4,h,m2EvenResidueTwoCutTape L k a b h ha⟩ := by
  let base : Config := ⟨3,h,(s1Config 3 6 2 a 0 b h).tape⟩
  let background := (s1Config L (8*k+2) 2 a 0 b h).tape
  have hinput := m2EvenResidueTwo_input_matches L k a b h hL hbound
  have hstart :
      frame (m2EvenResidueTwoInside a h) background base =
        s1Config L (8*k+2) 2 a 0 b h := by
    apply m2EvenResidueTwo_config_ext
    · rfl
    · rfl
    · funext x
      by_cases hx : m2EvenResidueTwoInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 44+12*a → ∀ d,
        run tm2 j base = some d →
        m2EvenResidueTwoInside a h d.head = true := by
    intro j hj d hd
    have hlow := m2EvenSix_q4_prefix_head_bound a b h ha j hj d hd
    have hcoord :
        h - ((3*a+2:Int)) - 9 = h - ((3*a+11:Int)) := by omega
    have hlow' : h - ((3*a+11:Int)) ≤ d.head := by
      rw [← hcoord]
      exact hlow
    change decide (h - ((3*a+11:Int)) ≤ d.head) = true
    exact decide_eq_true_iff.mpr hlow'
  have hlift := run_frame tm2 (m2EvenResidueTwoInside a h)
    background base (44+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (44+12*a) base =
        some (⟨4,h,m2EvenResidueTwoBaseTape a b h ha⟩ : Config) := by
    simpa [base] using (m2EvenResidueTwoBaseTape_spec a b h ha).1
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  simpa [m2EvenResidueTwoCutTape,background,base] using hlift

theorem m2Even_residue2_q4_prefix_data
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    ∃ Tq,
      run tm2 (44+12*a) (s1Config L (8*k+2) 2 a 0 b h) =
        some ⟨4,h,Tq⟩ ∧
      (∀ i : Nat, Tq (h-(i:Int)) =
        sideBit (BB6Coverage.Agent8Q4Suffix.q4LeftFacing L (8*k+1) a) i) ∧
      BB6Coverage.Agent8Q4Suffix.q4RightShape Tq h b ∧
      (∀ i : Nat, Tq (h+1+(i:Int)) =
        sideBit (BB6Coverage.Agent8Q4Suffix.q4RightFacing b) i) := by
  refine ⟨m2EvenResidueTwoCutTape L k a b h ha, ?_, ?_, ?_, ?_⟩
  · exact m2Even_residue2_q4_prefix_source L k a b h hL hbound ha
  · simpa [m2EvenResidueTwoLeftFacing] using
      m2EvenResidueTwo_leftFacing L k a b h hL hbound ha
  · exact m2EvenResidueTwo_prefix_rightShape L k a b h hL hbound ha
  · exact m2EvenResidueTwo_rightFacing L k a b h hL hbound ha

private theorem m2EvenResidueTwo_prefix_far_tail
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m2EvenResidueTwoCutTape L k a b h ha (h+1+(i:Int)) = false := by
  intro i hi
  rw [m2EvenResidueTwo_rightFacing L k a b h hL hbound ha i]
  apply sideBit_ge_length
  rw [BB6Coverage.Agent8Q4Suffix.q4RightFacing_length]
  omega

theorem m2Even_residue2_q4_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 2 (8*k+2) a b)
      (s1Config L (8*k+2) 2 a 0 b h) =
      some (s1Config L (8*k+1) 1 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  obtain ⟨Tq,hprefix,hleft,hshape,hright⟩ :=
    m2Even_residue2_q4_prefix_data L k a b h hL hbound ha
  have htail : ∀ i : Nat, 9+3*b ≤ i →
      Tq (h+1+(i:Int)) = false := by
    intro i hi
    rw [hright i]
    apply sideBit_ge_length
    rw [BB6Coverage.Agent8Q4Suffix.q4RightFacing_length]
    omega
  have happend := q4SuffixTargetLeft L (8*k+1) a b
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    L (8*k+1) 1 (a+b+2) (2^b-1)
    (BB6Coverage.Agent8Q4Suffix.q4LeftFacing L (8*k+1) a)
    hshape htail hleft happend
  have hsum :
      resetPrefixCost 2 (8*k+2) a b = (44+12*a)+(39+3*b) := by
    have hv : v2 (8*k+2) = 1 := by
      exact v2_of_odd_factorization (8*k+2) (2*k) 1 (by omega)
    simp [resetPrefixCost,hv]
    omega
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

#print axioms binDec_residue2
#print axioms binDec_residue1
#print axioms m2Even_residue2_q4_prefix_source
#print axioms m2Even_residue2_q4_reset_prefix_source

end BB6Coverage.Agent42M2EvenResidueTwo
