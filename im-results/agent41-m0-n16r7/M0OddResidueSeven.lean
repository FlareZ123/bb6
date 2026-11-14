import M0OddQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# Root successor (m,n) = (0,16*r+7): source q4 reset prefix

The genuine TM63 countdown successor after the marker-1 n=8*k odd-k
increment is marker 0 at n=8*k-1 = 16*r+7.  This module lifts the
already source-proved m=0,n=5 q4 prefix through the common first d0 block:
the n=16*r+7 input and n=16*r+6 target differ only in that block.
A tight head-confinement lemma ensures the lifted run never reads beyond
the common input window.

This is an intermediate original-table reset-prefix theorem, not a
complete TM63 itinerary or BB(6) upper bound.
-/

namespace BB6Coverage.Agent41M0OddResidueSeven

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent24M0OddQ4Bridges
open BB6Coverage.Agent24M0OddQ4Prefix

set_option maxHeartbeats 3000000

/-- Four low source blocks for n=16*r+7. -/
theorem binDec_residue7 (L r : Nat) (hL : 4 ≤ L)
    (hbound : 16*r+7 < 2^L) :
    binDec L (16*r+7) =
      d0 ++ d0 ++ d0 ++ d1 ++ binDec (L-4) r := by
  have hpow4 : 2^L = 16 * 2^(L-4) := by
    rw [show L = (L-4)+4 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow3 : 2^(L-1) = 8 * 2^(L-4) := by
    rw [show L-1 = (L-4)+3 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow2 : 2^(L-2) = 4 * 2^(L-4) := by
    rw [show L-2 = (L-4)+2 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow1 : 2^(L-3) = 2 * 2^(L-4) := by
    rw [show L-3 = (L-4)+1 by omega, Nat.pow_add]
    norm_num
    ring
  have hr : r < 2^(L-4) := by
    rw [hpow4] at hbound
    omega
  have hq1 : 8*r+3 < 2^(L-1) := by rw [hpow3]; omega
  have hq2 : 4*r+1 < 2^(L-2) := by rw [hpow2]; omega
  have hq3 : 2*r < 2^(L-3) := by rw [hpow1]; omega
  have h1 : binDec L (16*r+7) =
      d0 ++ binDec (L-1) (8*r+3) := by
    rw [show L = (L-1)+1 by omega,
      show 16*r+7 = 2*(8*r+3)+1 by omega]
    exact binDec_odd (L-1) (8*r+3) hq1
  have h2 : binDec (L-1) (8*r+3) =
      d0 ++ binDec (L-2) (4*r+1) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 8*r+3 = 2*(4*r+1)+1 by omega]
    exact binDec_odd (L-2) (4*r+1) hq2
  have h3 : binDec (L-2) (4*r+1) =
      d0 ++ binDec (L-3) (2*r) := by
    rw [show L-2 = (L-3)+1 by omega,
      show 4*r+1 = 2*(2*r)+1 by omega]
    exact binDec_odd (L-3) (2*r) hq3
  have h4 : binDec (L-3) (2*r) =
      d1 ++ binDec (L-4) r := by
    rw [show L-3 = (L-4)+1 by omega,
      show 2*r = 2*r by rfl]
    exact binDec_even (L-4) r hr
  rw [h1,h2,h3,h4]
  simp [List.append_assoc]

/-- Four low target blocks for n-1=16*r+6. -/
theorem binDec_residue6 (L r : Nat) (hL : 4 ≤ L)
    (hbound : 16*r+7 < 2^L) :
    binDec L (16*r+6) =
      d1 ++ d0 ++ d0 ++ d1 ++ binDec (L-4) r := by
  have hpow4 : 2^L = 16 * 2^(L-4) := by
    rw [show L = (L-4)+4 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow3 : 2^(L-1) = 8 * 2^(L-4) := by
    rw [show L-1 = (L-4)+3 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow2 : 2^(L-2) = 4 * 2^(L-4) := by
    rw [show L-2 = (L-4)+2 by omega, Nat.pow_add]
    norm_num
    ring
  have hpow1 : 2^(L-3) = 2 * 2^(L-4) := by
    rw [show L-3 = (L-4)+1 by omega, Nat.pow_add]
    norm_num
    ring
  have hr : r < 2^(L-4) := by
    rw [hpow4] at hbound
    omega
  have hq1 : 8*r+3 < 2^(L-1) := by rw [hpow3]; omega
  have hq2 : 4*r+1 < 2^(L-2) := by rw [hpow2]; omega
  have hq3 : 2*r < 2^(L-3) := by rw [hpow1]; omega
  have h1 : binDec L (16*r+6) =
      d1 ++ binDec (L-1) (8*r+3) := by
    rw [show L = (L-1)+1 by omega,
      show 16*r+6 = 2*(8*r+3) by omega]
    exact binDec_even (L-1) (8*r+3) hq1
  have h2 : binDec (L-1) (8*r+3) =
      d0 ++ binDec (L-2) (4*r+1) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 8*r+3 = 2*(4*r+1)+1 by omega]
    exact binDec_odd (L-2) (4*r+1) hq2
  have h3 : binDec (L-2) (4*r+1) =
      d0 ++ binDec (L-3) (2*r) := by
    rw [show L-2 = (L-3)+1 by omega,
      show 4*r+1 = 2*(2*r)+1 by omega]
    exact binDec_odd (L-3) (2*r) hq3
  have h4 : binDec (L-3) (2*r) =
      d1 ++ binDec (L-4) r := by
    rw [show L-3 = (L-4)+1 by omega]
    exact binDec_even (L-4) r hr
  rw [h1,h2,h3,h4]
  simp [List.append_assoc]

def m0OddResidueSevenInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 0 ++ d0 ++ d0

def m0OddResidueSevenTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ d1

def m0OddResidueSevenLeftFacing (L r a : Nat) : List Bool :=
  m0OddResidueSevenTargetPrefix a ++
    (d0 ++ d0 ++ d1 ++ binDec (L-4) r ++ lh)

private theorem m0OddResidueSevenInputPrefix_length (a : Nat) :
    (m0OddResidueSevenInputPrefix a).length = 3*a+8 := by
  simp [m0OddResidueSevenInputPrefix,d1pow_length,markerWord,d0]
  omega

private theorem m0OddResidueSevenTargetPrefix_length (a : Nat) :
    (m0OddResidueSevenTargetPrefix a).length = 3*a+8 := by
  simp [m0OddResidueSevenTargetPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem binDec_three_five :
    binDec 3 5 = d0 ++ d1 ++ d0 := by
  have h1 : binDec 3 5 = d0 ++ binDec 2 2 := by
    simpa using binDec_odd 2 2 (by decide)
  have h2 : binDec 2 2 = d1 ++ binDec 1 1 := by
    simpa using binDec_even 1 1 (by decide)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private theorem binDec_three_four :
    binDec 3 4 = d1 ++ d1 ++ d0 := by
  have h1 : binDec 3 4 = d1 ++ binDec 2 2 := by
    simpa using binDec_even 2 2 (by decide)
  have h2 : binDec 2 2 = d1 ++ binDec 1 1 := by
    simpa using binDec_even 1 1 (by decide)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private theorem m0OddResidueSeven_source_left
    (L r a : Nat) (hL : 4 ≤ L) (hbound : 16*r+7 < 2^L) :
    s1LeftFacing L (16*r+7) 0 a 0 =
      m0OddResidueSevenInputPrefix a ++
        (d0 ++ d0 ++ d1 ++ binDec (L-4) r ++ lh) := by
  have hbin := binDec_residue7 L r hL hbound
  simp [s1LeftFacing,m0OddResidueSevenInputPrefix,
    binDec_zero,hbin,List.append_assoc]

private theorem m0OddResidueSeven_base_input_left (a : Nat) :
    s1LeftFacing 3 5 0 a 0 =
      m0OddResidueSevenInputPrefix a ++ (d1 ++ d0 ++ lh) := by
  simp [s1LeftFacing,m0OddResidueSevenInputPrefix,
    binDec_zero,binDec_three_five,List.append_assoc]

private theorem m0OddResidueSeven_input_matches
    (L r a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hbound : 16*r+7 < 2^L) :
    ∀ x, decide (h-((3*a+7:Int)) ≤ x) = true →
      (s1Config L (16*r+7) 0 a 0 b h).tape x =
        (s1Config 3 5 0 a 0 b h).tape x := by
  have hsource := m0OddResidueSeven_source_left L r a hL hbound
  have hbase := m0OddResidueSeven_base_input_left a
  have hlen := m0OddResidueSevenInputPrefix_length a
  intro x hx
  by_cases hleft : x ≤ h
  · let i : Nat := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i:Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int) = x := by omega
    have hthreshold : h-((3*a+7:Int)) ≤ x := by
      simpa using hx
    have hi : i ≤ 3*a+7 := by
      dsimp [i]
      omega
    have hiPrefix :
        i < (m0OddResidueSevenInputPrefix a).length := by
      rw [hlen]
      omega
    have hsrc := s1Config_left_cell L (16*r+7) 0 a 0 b h i
    have hbaseCell := s1Config_left_cell 3 5 0 a 0 b h i
    rw [hcoord] at hsrc hbaseCell
    rw [hsource] at hsrc
    rw [hbase] at hbaseCell
    have hsrcBit := sideBit_append_left
      (m0OddResidueSevenInputPrefix a)
      (d0 ++ d0 ++ d1 ++ binDec (L-4) r ++ lh) i hiPrefix
    have hbaseBit := sideBit_append_left
      (m0OddResidueSevenInputPrefix a) (d1 ++ d0 ++ lh) i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbaseCell
    exact hsrc.trans hbaseCell.symm
  · have hsrc := s1Config_right_cell L (16*r+7) 0 a 0 b h
      (Int.toNat (x-h-1))
    have hbaseCell := s1Config_right_cell 3 5 0 a 0 b h
      (Int.toNat (x-h-1))
    have hcoord :
        h+1+((Int.toNat (x-h-1):Nat):Int) = x := by
      have hnonneg : 0 ≤ x-h-1 := by omega
      rw [Int.toNat_of_nonneg hnonneg]
      omega
    rw [hcoord] at hsrc hbaseCell
    exact hsrc.trans hbaseCell.symm

def m0OddResidueSevenInside (a : Nat) (h x : Int) : Bool :=
  decide (h-((3*a+7:Int)) ≤ x)

/-- The generalized q4 cut is the n=5 q4 output on the common
head-facing half-line, with the n=16*r+7 source outside it. -/
def m0OddResidueSevenCutTape
    (L r a b : Nat) (h : Int) : Int → Bool :=
  (frame (m0OddResidueSevenInside a h)
    (s1Config L (16*r+7) 0 a 0 b h).tape
    (⟨4,h,m0OddQ4CutTape a b h⟩ : Config)).tape

private theorem m0OddResidueSeven_cut_eq_base_inside
    (L r a b : Nat) (h x : Int)
    (hin : m0OddResidueSevenInside a h x = true) :
    m0OddResidueSevenCutTape L r a b h x =
      m0OddQ4CutTape a b h x := by
  simp [m0OddResidueSevenCutTape,frame,hin]

private theorem m0OddResidueSeven_cut_eq_input
    (L r a b : Nat) (h x : Int)
    (hout : m0OddResidueSevenInside a h x = false) :
    m0OddResidueSevenCutTape L r a b h x =
      (s1Config L (16*r+7) 0 a 0 b h).tape x := by
  simp [m0OddResidueSevenCutTape,frame,hout]

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

private theorem sweptLeft_head_eq_source (q : Nat)
    (T : Int → Bool) (h : Int) :
    sweptLeft q T h (h-(q:Int)) = T (h-(q:Int)) := by
  induction q with
  | zero => simp [sweptLeft]
  | succ q ih =>
      have hcoord : h-((q+1:Int)) = (h-1)-(q:Int) := by omega
      rw [show sweptLeft (q+1) T h =
        sweptLeft q (holeThree T h) (h-1) by rfl]
      rw [hcoord,ih]
      have hne1 : h-((q+1:Int)) ≠ h+1 := by omega
      have hne2 : h-((q+1:Int)) ≠ h := by omega
      simp [holeThree,hne1,hne2]

private theorem sweptLeft_head_plus1_false (q : Nat)
    (T : Int → Bool) (h : Int) :
    sweptLeft (q+1) T h (h-(q:Int)) = false := by
  induction q with
  | zero => simp [sweptLeft,holeThree]
  | succ q ih =>
      have hcoord : h-((q+1:Int)) = (h-1)-(q:Int) := by omega
      rw [show sweptLeft (q+2) T h =
        sweptLeft (q+1) (holeThree T h) (h-1) by rfl]
      rw [hcoord]
      exact ih (holeThree T h) (h-1)

private theorem leftSweep_one (T : Int → Bool) (h : Int)
    (ht : T h = true) :
    run tm2 1 ⟨3,h,T⟩ = some ⟨1,h+1,T⟩ := by
  simp [run,rawStep,readSlot,applyMove,tm2,ht]

private theorem leftSweep_two (T : Int → Bool) (h : Int)
    (ht : T h = true) (hr : T (h+1) = false) :
    run tm2 2 ⟨3,h,T⟩ =
      some ⟨2,h,(fun x => if x = h+1 then true else T x)⟩ := by
  rw [show 2 = 1+1 by omega,run_add,leftSweep_one T h ht]
  simp [run,rawStep,readSlot,applyMove,tm2,hr]

private theorem counted_left_sweep_heads
    (N : Nat) (T : Int → Bool) (h : Int)
    (hOn : leftOnes T h N) (hr : T (h+1) = false)
    (k : Nat) (hk : k < 3*N) (d : Config)
    (hd : run tm2 k ⟨3,h,T⟩ = some d) :
    h-(N:Int) ≤ d.head := by
  let q := k/3
  let r := k%3
  have hkdecomp : k = 3*q+r := by dsimp [q,r]; omega
  have hq : q < N := by dsimp [q]; omega
  have hqOn : leftOnes T h q := by
    intro i hi
    exact hOn i (by omega)
  have hqrun := counted_left_sweep q T h hqOn hr
  let Tq := sweptLeft q T h
  have hqhead : Tq (h-(q:Int)) = true := by
    rw [show Tq = sweptLeft q T h by rfl,sweptLeft_head_eq_source]
    exact hOn q hq
  have hqright : Tq (h-(q:Int)+1) = false := by
    by_cases hq0 : q = 0
    · subst q
      simpa [Tq] using hr
    · obtain ⟨q',rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      have hfalse := sweptLeft_head_plus1_false q' T h
      simpa [Tq] using hfalse
  have hqrun' :
      run tm2 (3*q) ⟨3,h,T⟩ =
        some ⟨3,h-(q:Int),Tq⟩ := by
    simpa [Tq] using hqrun
  rw [hkdecomp,run_add,hqrun'] at hd
  simp only [Option.bind_some] at hd
  have hrlt : r < 3 := Nat.mod_lt _ (by decide)
  have hrCases : r=0 ∨ r=1 ∨ r=2 := by omega
  rcases hrCases with hr0|hr1|hr2
  · subst r
    simp [run] at hd
    have heq := Option.some.inj hd
    subst d
    simp
    omega
  · subst r
    rw [leftSweep_one Tq (h-(q:Int)) hqhead] at hd
    have heq := Option.some.inj hd
    subst d
    simp
    omega
  · subst r
    rw [leftSweep_two Tq (h-(q:Int)) hqhead hqright] at hd
    have heq := Option.some.inj hd
    subst d
    simp
    omega

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

private theorem m0Odd_bridge_prefix_lower
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ y, m0OddQ4Bridge27Inside y = true →
      T (h+y) = decide (y ∈ m0OddQ4Bridge27Start.marked))
    (j : Nat) (hj : j < 27) (d : Config)
    (hd : run tm2 j ⟨3,h,T⟩ = some d) :
    h-6 ≤ d.head := by
  obtain ⟨e,hexact⟩ :=
    fRun_prefix_exists m0OddQ4Bridge27_exact (by omega)
  have hcheckj :
      (List.range j).all (fun k =>
        match fRun tm2 k m0OddQ4Bridge27Start with
        | none => true
        | some f => m0OddQ4Bridge27Inside f.head) = true := by
    apply List.all_eq_true.mpr
    intro k hk
    have hk27 : k < 27 := by
      have hmem := List.mem_range.mp hk
      omega
    exact (List.all_eq_true.mp m0OddQ4Bridge27_heads) k
      (List.mem_range.mpr hk27)
  have hbridge := bridgeAt T h m0OddQ4Bridge27Inside
    m0OddQ4Bridge27Start e j rfl hexact hcheckj hmatch
  rw [hbridge] at hd
  have hdeq : d = frameAt T h m0OddQ4Bridge27Inside e :=
    Option.some.inj hd
  have hinside : m0OddQ4Bridge27Inside e.head = true := by
    have hh := (List.all_eq_true.mp m0OddQ4Bridge27_heads) j
      (List.mem_range.mpr hj)
    simpa [hexact] using hh
  have hlow : -6 ≤ e.head := by
    simp [m0OddQ4Bridge27Inside] at hinside
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
  simp at heq
  omega

/-- Every prefix of the base n=5 q4 run stays above h-3*a-6.
This is the sharp read bound: 3*a sweep cells, then the bridge's -6
left edge, followed only by the rightward E scan. -/
private theorem m0Odd_base_prefix_head_bound
    (a b : Nat) (h : Int) (ha : 0<a) :
    ∀ k, k < 24+12*a → ∀ d,
      run tm2 k (s1Config 3 5 0 a 0 b h) = some d →
      h-((3*a+6:Int)) ≤ d.head := by
  let T := (s1Config 3 5 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m0OddQ4CutTape a b h
  have hleft :
      s1LeftFacing 3 5 0 a 0 =
        d1pow a ++ (markerWord 0 ++ d0 ++ binDec 3 5 ++ lh) := by
    simp [s1LeftFacing,binDec_zero,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 5 0 a 0 b h i
    rw [hleft] at hcell
    have hbit := sideBit_append_left
      (d1pow a) (markerWord 0 ++ d0 ++ binDec 3 5 ++ lh) i
      (by rw [d1pow_length]; omega)
    rw [hbit] at hcell
    exact hcell.trans (sideBit_d1pow_true a i hi)
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 5 0 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m0OddQ4Bridge_input_match a b h ha
  have hBridge := m0OddQ4Bridge27At T1 hN hmatch
  have hBridge' :
      run tm2 27 ⟨3,hN,T1⟩ =
        some ⟨4,hN+3,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m0OddQ4Bridge27Inside m0OddQ4Bridge27End =
          (⟨4,hN+3,T2⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,m0OddQ4Bridge27End]
      · simp [frameAt_head,m0OddQ4Bridge27End] <;> omega
      · rfl
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+3) (3*(a-1)) := by
    intro i hi
    let x : Int := hN+3+(i:Int)
    by_cases hi0 : i=0
    · subst i
      have hrel : x-hN=3 := by dsimp [x]; omega
      have hin : m0OddQ4Bridge27Inside (x-hN)=true := by
        simp [m0OddQ4Bridge27Inside,hrel]
      have hcut := frameAt_tape_inside T1 hN
        m0OddQ4Bridge27Inside m0OddQ4Bridge27End x hin
      have hmark :
          decide ((x-hN) ∈ m0OddQ4Bridge27End.marked) = true := by
        rw [hrel]
        simp [m0OddQ4Bridge27End]
      simpa [T2,m0OddQ4CutTape,x,hN] using hcut.trans hmark
    · have hrel : x-hN=3+(i:Int) := by dsimp [x]; omega
      have hout : m0OddQ4Bridge27Inside (x-hN)=false := by
        simp [m0OddQ4Bridge27Inside,hrel]
        omega
      have hcut := frameAt_tape_outside T1 hN
        m0OddQ4Bridge27Inside m0OddQ4Bridge27End x hout
      let j : Nat := 3*a-3-i
      have hj : j+1 < N := by
        dsimp [j,N]
        omega
      have hblock := sweptLeft_block N j T h hj
      have hcoord : x = h-(j:Int) := by
        dsimp [x,j,N,hN]
        omega
      have hblock' : sweptLeft N T h x = true := by
        rw [hcoord]
        exact hblock
      simpa [T2,m0OddQ4CutTape,x] using hcut.trans hblock'
  intro k hk d hd
  let p1 := 3*N
  let p2 := p1+27
  by_cases hk1 : k < p1
  · have hlow := counted_left_sweep_heads N T h hOn hright k
      (by dsimp [p1]; omega) d hd
    dsimp [hN,N] at *
    omega
  · by_cases hk2 : k < p2
    · let j : Nat := k-p1
      have hj : j<27 := by dsimp [j,p1] at *; omega
      have hkEq : k=p1+j := by dsimp [j,p1]; omega
      rw [hkEq,run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      have hlow := m0Odd_bridge_prefix_lower T1 hN hmatch j hj d hd
      dsimp [hN,N] at *
      omega
    · let j : Nat := k-p2
      have hj : j<3*(a-1) := by dsimp [j,p2,p1,N] at *; omega
      have hkEq : k=p1+(27+j) := by dsimp [j,p2,p1]; omega
      rw [hkEq,run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      rw [run_add,hBridge'] at hd
      simp only [Option.bind_some] at hd
      have hhead := E_scan_prefix_head T2 (hN+3) (3*(a-1))
        hlinear j hj d hd
      dsimp [hN,N] at *
      omega

/-- The q4 prefix for n=16*r+7 is a framed copy of the n=5 source run.
Only the first d0 block is read or changed; the remaining three low blocks
are preserved from the genuine input and already equal the target tail. -/
theorem m0Odd_residue7_q4_prefix_source
    (L r a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hbound : 16*r+7 < 2^L) (ha : 0<a) :
    run tm2 (24+12*a)
      (s1Config L (16*r+7) 0 a 0 b h) =
      some ⟨4,h,m0OddResidueSevenCutTape L r a b h⟩ := by
  let base : Config := ⟨3,h,(s1Config 3 5 0 a 0 b h).tape⟩
  let background := (s1Config L (16*r+7) 0 a 0 b h).tape
  have hinput := m0OddResidueSeven_input_matches L r a b h hL hbound
  have hstart :
      frame (m0OddResidueSevenInside a h) background base =
        s1Config L (16*r+7) 0 a 0 b h := by
    apply config_ext
    · rfl
    · rfl
    · funext x
      by_cases hx : m0OddResidueSevenInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 24+12*a → ∀ d,
        run tm2 j base = some d →
        m0OddResidueSevenInside a h d.head = true := by
    intro j hj d hd
    have hlow := m0Odd_base_prefix_head_bound a b h ha j hj d hd
    simpa [m0OddResidueSevenInside] using (show
      h-((3*a+7:Int)) ≤ d.head by omega)
  have hlift := run_frame tm2 (m0OddResidueSevenInside a h)
    background base (24+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (24+12*a) base =
        some (⟨4,h,m0OddQ4CutTape a b h⟩ : Config) := by
    simpa [base] using m0Odd_q4_prefix_run a b h ha
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  simpa [m0OddResidueSevenCutTape,background] using hlift

private theorem m0OddResidueSeven_cut_eq_base
    (L r a b : Nat) (h x : Int) (hx : h ≤ x) :
    m0OddResidueSevenCutTape L r a b h x =
      m0OddQ4CutTape a b h x := by
  have hin : m0OddResidueSevenInside a h x = true := by
    simp [m0OddResidueSevenInside]
    omega
  exact m0OddResidueSeven_cut_eq_base_inside L r a b h x hin

private theorem m0OddResidueSeven_base_leftFacing (a : Nat) :
    m0OddQ4LeftFacing a =
      m0OddResidueSevenTargetPrefix a ++ (d1 ++ d0 ++ lh) := by
  simp [m0OddQ4LeftFacing,m0OddResidueSevenTargetPrefix,
    binDec_three_four,List.append_assoc]

/-- Complete left-facing word at the generalized q4 cut. -/
theorem m0Odd_residue7_q4_prefix_leftFacing
    (L r a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hbound : 16*r+7 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m0OddResidueSevenCutTape L r a b h (h-(i:Int)) =
        sideBit (m0OddResidueSevenLeftFacing L r a) i := by
  have hsource := m0OddResidueSeven_source_left L r a hL hbound
  have htargetLen := m0OddResidueSevenTargetPrefix_length a
  intro i
  by_cases hi : i ≤ 3*a+7
  · have hin :
      m0OddResidueSevenInside a h (h-(i:Int)) = true := by
      simp [m0OddResidueSevenInside]
      omega
    rw [m0OddResidueSeven_cut_eq_base_inside L r a b h
      (h-(i:Int)) hin]
    rw [m0Odd_q4_prefix_leftFacing a b h ha i]
    rw [m0OddResidueSeven_base_leftFacing]
    have hbaseBit := sideBit_append_left
      (m0OddResidueSevenTargetPrefix a) (d1 ++ d0 ++ lh) i
      (by rw [htargetLen]; omega)
    have htargetBit := sideBit_append_left
      (m0OddResidueSevenTargetPrefix a)
      (d0 ++ d0 ++ d1 ++ binDec (L-4) r ++ lh) i
      (by rw [htargetLen]; omega)
    calc
      sideBit
          (m0OddResidueSevenTargetPrefix a ++ (d1 ++ d0 ++ lh)) i =
          sideBit (m0OddResidueSevenTargetPrefix a) i := hbaseBit
      _ = sideBit
          (m0OddResidueSevenTargetPrefix a ++
            (d0 ++ d0 ++ d1 ++ binDec (L-4) r ++ lh)) i :=
          htargetBit.symm
  · have hout :
      m0OddResidueSevenInside a h (h-(i:Int)) = false := by
      simp [m0OddResidueSevenInside]
      omega
    rw [m0OddResidueSeven_cut_eq_input L r a b h
      (h-(i:Int)) hout]
    have hcell := s1Config_left_cell L (16*r+7) 0 a 0 b h i
    rw [hsource] at hcell
    have hsrc := sideBit_append_right
      (m0OddResidueSevenInputPrefix a)
      (d0 ++ d0 ++ d1 ++ binDec (L-4) r ++ lh) i
      (by rw [m0OddResidueSevenInputPrefix_length]; omega)
    have htgt := sideBit_append_right
      (m0OddResidueSevenTargetPrefix a)
      (d0 ++ d0 ++ d1 ++ binDec (L-4) r ++ lh) i
      (by rw [m0OddResidueSevenTargetPrefix_length]; omega)
    rw [hsrc] at hcell
    simpa [m0OddResidueSevenLeftFacing] using hcell.trans htgt.symm

/-- Complete right-facing word at the generalized q4 cut. -/
theorem m0Odd_residue7_q4_prefix_rightFacing
    (L r a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hbound : 16*r+7 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m0OddResidueSevenCutTape L r a b h (h+1+(i:Int)) =
        sideBit (q4RightFacing b) i := by
  intro i
  have hin :
      m0OddResidueSevenInside a h (h+1+(i:Int)) = true := by
    simp [m0OddResidueSevenInside]
    omega
  rw [m0OddResidueSeven_cut_eq_base_inside L r a b h
    (h+1+(i:Int)) hin]
  exact m0Odd_q4_prefix_rightFacing a b h ha i

/-- The generalized q4 cut retains the full right-shape contract. -/
theorem m0Odd_residue7_q4_prefix_rightShape
    (L r a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hbound : 16*r+7 < 2^L) (ha : 0<a) :
    q4RightShape (m0OddResidueSevenCutTape L r a b h) h b := by
  apply q4RightShape_congr
    (m0OddQ4CutTape a b h)
    (m0OddResidueSevenCutTape L r a b h) h b
  · intro x hx
    exact (m0OddResidueSeven_cut_eq_base L r a b h x hx).symm
  · exact m0Odd_q4_prefix_rightShape a b h ha

/-- Export the complete q4 prefix interface consumed by the suffix. -/
theorem m0Odd_residue7_q4_prefix_data
    (L r a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hbound : 16*r+7 < 2^L) (ha : 0<a) :
    ∃ Tq,
      run tm2 (24+12*a) (s1Config L (16*r+7) 0 a 0 b h) =
        some ⟨4,h,Tq⟩ ∧
      (∀ i : Nat, Tq (h-(i:Int)) =
        sideBit (m0OddResidueSevenLeftFacing L r a) i) ∧
      q4RightShape Tq h b ∧
      (∀ i : Nat, Tq (h+1+(i:Int)) =
        sideBit (q4RightFacing b) i) := by
  refine ⟨m0OddResidueSevenCutTape L r a b h, ?_, ?_, ?_, ?_⟩
  · exact m0Odd_residue7_q4_prefix_source L r a b h hL hbound ha
  · exact m0Odd_residue7_q4_prefix_leftFacing L r a b h hL hbound ha
  · exact m0Odd_residue7_q4_prefix_rightShape L r a b h hL hbound ha
  · exact m0Odd_residue7_q4_prefix_rightFacing L r a b h hL hbound ha

/-- The q4 suffix target has the canonical S1 left-facing encoding. -/
theorem m0OddResidueSeven_suffix_target_left
    (L r a b : Nat) (hL : 4 ≤ L) (hbound : 16*r+7 < 2^L)
    (ha : 0<a) :
    s1LeftFacing L (16*r+6) 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m0OddResidueSevenLeftFacing L r a).drop 1 := by
  have hbinPow := binDec_pow2_sub_one (a-1) b
  have hlen : (a-1)+b+2 = a+b+1 := by omega
  have hexp : (a-1)+2 = a+1 := by omega
  have hbin : binDec (a+b+1) (2^b-1) =
      d0pow b ++ d1pow (a+1) := by
    simpa [hlen,hexp] using hbinPow
  have hbin6 := binDec_residue6 L r hL hbound
  unfold s1LeftFacing
  rw [hbin,hbin6]
  rw [← hexp]
  rw [d1pow_add_right (a-1) 2]
  simp [m0OddResidueSevenLeftFacing,m0OddResidueSevenTargetPrefix,
    List.drop,List.append_assoc]

/-- The right-facing q4 suffix is blank beyond its finite window. -/
private theorem m0OddResidueSeven_prefix_far_tail
    (L r a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hbound : 16*r+7 < 2^L) (ha : 0<a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m0OddResidueSevenCutTape L r a b h (h+1+(i:Int)) = false := by
  intro i hi
  rw [m0Odd_residue7_q4_prefix_rightFacing L r a b h hL hbound ha i]
  apply sideBit_ge_length
  rw [q4RightFacing_length]
  omega

private theorem m0OddResidueSeven_resetPrefixCost_eq (r a b : Nat) :
    resetPrefixCost 0 (16*r+7) a b = 63+12*a+3*b := by
  have hv : v2 (16*r+7) = 0 := by
    exact v2_of_odd (16*r+7) (by omega)
  simp [resetPrefixCost,hv]

/-- Full original-table Rst0 reset prefix for every admissible n=16*r+7. -/
theorem m0Odd_residue7_q4_reset_prefix_source
    (L r a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hbound : 16*r+7 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 0 (16*r+7) a b)
      (s1Config L (16*r+7) 0 a 0 b h) =
      some (s1Config L (16*r+6) 2 (a+b+1) (2^b-1) 0
        (h+5+3*b)) := by
  obtain ⟨Tq,hprefix,hleft,hshape,hright⟩ :=
    m0Odd_residue7_q4_prefix_data L r a b h hL hbound ha
  have htail : ∀ i : Nat, 9+3*b ≤ i →
      Tq (h+1+(i:Int)) = false := by
    intro i hi
    rw [hright i]
    apply sideBit_ge_length
    rw [q4RightFacing_length]
    omega
  have happend := m0OddResidueSeven_suffix_target_left L r a b hL hbound ha
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    L (16*r+6) 2 (a+b+1) (2^b-1)
    (m0OddResidueSevenLeftFacing L r a)
    hshape htail hleft happend
  have hsum :
      resetPrefixCost 0 (16*r+7) a b = (24+12*a)+(39+3*b) := by
    rw [m0OddResidueSeven_resetPrefixCost_eq]
    omega
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

#print axioms binDec_residue7
#print axioms binDec_residue6
#print axioms m0Odd_residue7_q4_prefix_source
#print axioms m0Odd_residue7_q4_reset_prefix_source

end BB6Coverage.Agent41M0OddResidueSeven
