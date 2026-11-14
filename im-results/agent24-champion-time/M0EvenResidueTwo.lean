import M0EvenQ4Suffix
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Uniform m=0, n=8*k+2 source reset prefix

Lift the original-source n=2 even q4 prefix through its untouched
higher-order binary tail.  The lift is a half-line frame: the base run
never reads the extra tail, and the generic q4 suffix plus counted drain
then gives the full source increment for every admissible n=8*k+2.
-/ 

namespace BB6Coverage.Agent24M0EvenResidueTwo

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent24M0EvenQ4Bridge
open BB6Coverage.Agent24M0EvenQ4Prefix
open BB6Coverage.Agent24M0EvenSuffix
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

/-- Low three bits of every admissible n=8*k+2. -/
theorem binDec_residue2 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+2 < 2^L) :
    binDec L (8*k+2) = d1 ++ d0 ++ d1 ++ binDec (L-3) k := by
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

/-- Low three bits of the successor n-1=8*k+1. -/
theorem binDec_residue1 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+1 < 2^L) :
    binDec L (8*k+1) = d0 ++ d1 ++ d1 ++ binDec (L-3) k := by
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
  have h1 : binDec L (8*k+1) =
      d0 ++ binDec (L-1) (4*k) := by
    rw [show L = (L-1)+1 by omega,
      show 8*k+1 = 2*(4*k)+1 by omega]
    exact binDec_odd (L-1) (4*k) hq1
  have h2 : binDec (L-1) (4*k) =
      d1 ++ binDec (L-2) (2*k) := by
    rw [show L-1 = (L-2)+1 by omega]
    exact binDec_even (L-2) (2*k) hq2
  have h3 : binDec (L-2) (2*k) =
      d1 ++ binDec (L-3) k := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_even (L-3) k hk
  rw [h1,h2,h3]
  simp [List.append_assoc]

/-- The fixed source prefix before the higher-order input tail. -/
def m0EvenResidueTwoInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d0 ++ d1

/-- The corresponding fixed target prefix after the q4 suffix. -/
def m0EvenResidueTwoTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ d0 ++ d1 ++ d1

def m0EvenResidueTwoLeftFacing (L k a : Nat) : List Bool :=
  m0EvenResidueTwoTargetPrefix a ++ (binDec (L-3) k ++ lh)

private theorem m0EvenResidueTwo_inputPrefix_length (a : Nat) :
    (m0EvenResidueTwoInputPrefix a).length = 3*a+10 := by
  simp [m0EvenResidueTwoInputPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m0EvenResidueTwo_targetPrefix_length (a : Nat) :
    (m0EvenResidueTwoTargetPrefix a).length = 3*a+10 := by
  simp [m0EvenResidueTwoTargetPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m0EvenResidueTwo_source_left
    (L k a : Nat) (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) :
    s1LeftFacing L (8*k+2) 0 a 0 =
      m0EvenResidueTwoInputPrefix a ++ (binDec (L-3) k ++ lh) := by
  have hbin := binDec_residue2 L k hL hbound
  unfold s1LeftFacing
  rw [hbin]
  simp [m0EvenResidueTwoInputPrefix,List.append_assoc]

private theorem m0EvenResidueTwo_base_input_left (a : Nat) :
    s1LeftFacing 3 2 0 a 0 =
      m0EvenResidueTwoInputPrefix a ++ lh := by
  simp [s1LeftFacing,m0EvenResidueTwoInputPrefix,
    m0Even_binDec_three_two,List.append_assoc]

private theorem m0EvenResidueTwo_base_target_left (a : Nat) :
    m0EvenQ4LeftFacing a =
      m0EvenResidueTwoTargetPrefix a ++ lh := by
  simp [m0EvenQ4LeftFacing,m0EvenResidueTwoTargetPrefix,
    m0Even_binDec_three_one,List.append_assoc]

/-- The extra binary tail begins strictly to the left of the readable
half-line used by the fixed n=2 source prefix. -/
def m0EvenResidueTwoInside (a : Nat) (h x : Int) : Bool :=
  decide (h-((3*a+9:Int)) ≤ x)

private theorem m0EvenResidueTwo_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) :
    ∀ x, m0EvenResidueTwoInside a h x = true →
      (s1Config L (8*k+2) 0 a 0 b h).tape x =
        (s1Config 3 2 0 a 0 b h).tape x := by
  have hsource := m0EvenResidueTwo_source_left L k a hL hbound
  have hbase := m0EvenResidueTwo_base_input_left a
  intro x hx
  by_cases hleft : x ≤ h
  · let i : Nat := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i:Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hboundI : i ≤ 3*a+9 := by
      have hinside : h-((3*a+9:Int)) ≤ x := by
        simpa [m0EvenResidueTwoInside] using hx
      omega
    have hidx : i < (m0EvenResidueTwoInputPrefix a).length := by
      rw [m0EvenResidueTwo_inputPrefix_length]
      omega
    have hcoord : h-(i:Int) = x := by omega
    have hsrcCell :=
      s1Config_left_cell L (8*k+2) 0 a 0 b h i
    have hbaseCell := s1Config_left_cell 3 2 0 a 0 b h i
    rw [hcoord] at hsrcCell hbaseCell
    rw [hsource] at hsrcCell
    rw [hbase] at hbaseCell
    have hsrcBit := Agent6Q4Prefix.sideBit_append_left
      (m0EvenResidueTwoInputPrefix a) (binDec (L-3) k ++ lh) i hidx
    have hbaseBit := Agent6Q4Prefix.sideBit_append_left
      (m0EvenResidueTwoInputPrefix a) lh i hidx
    rw [hsrcBit] at hsrcCell
    rw [hbaseBit] at hbaseCell
    exact hsrcCell.trans hbaseCell.symm
  · let i : Nat := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i:Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int) = x := by omega
    have hsrcCell := s1Config_right_cell L (8*k+2) 0 a 0 b h i
    have hbaseCell := s1Config_right_cell 3 2 0 a 0 b h i
    rw [hcoord] at hsrcCell hbaseCell
    exact hsrcCell.trans hbaseCell.symm

/-- Pointwise extensionality for physical configurations. -/
private theorem m0EvenResidueTwo_config_ext (c d : Config)
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

/-- The generalized cut is the base q4 cut on the readable half-line
and retains the original high-order tail everywhere else. -/
def m0EvenResidueTwoCutTape
    (L k a b : Nat) (h : Int) : Int → Bool :=
  (frame (m0EvenResidueTwoInside a h)
    (s1Config L (8*k+2) 0 a 0 b h).tape
    (⟨4,h,m0EvenQ4CutTape a b h⟩ : Config)).tape

private theorem m0EvenResidueTwo_cut_eq_base
    (L k a b : Nat) (h x : Int) (hx : h ≤ x) :
    m0EvenResidueTwoCutTape L k a b h x =
      m0EvenQ4CutTape a b h x := by
  have hin : m0EvenResidueTwoInside a h x = true := by
    simp [m0EvenResidueTwoInside]
    omega
  simp [m0EvenResidueTwoCutTape,frame,hin]

private theorem m0EvenResidueTwo_cut_eq_base_inside
    (L k a b : Nat) (h x : Int)
    (hin : m0EvenResidueTwoInside a h x = true) :
    m0EvenResidueTwoCutTape L k a b h x =
      m0EvenQ4CutTape a b h x := by
  simp [m0EvenResidueTwoCutTape,frame,hin]

private theorem m0EvenResidueTwo_cut_eq_input
    (L k a b : Nat) (h x : Int)
    (hout : m0EvenResidueTwoInside a h x = false) :
    m0EvenResidueTwoCutTape L k a b h x =
      (s1Config L (8*k+2) 0 a 0 b h).tape x := by
  simp [m0EvenResidueTwoCutTape,frame,hout]

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

private theorem m0Even_bridge_prefix_lower
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ y, m0EvenQ4Inside y = true →
      T (h+y) = decide (y ∈ m0EvenQ4BridgeStart.marked))
    (j : Nat) (hj : j < 39) (d : Config)
    (hd : run tm2 j ⟨3,h,T⟩ = some d) :
    h-9 ≤ d.head := by
  obtain ⟨e,hexact⟩ :=
    fRun_prefix_exists m0EvenQ4Bridge_exact (by omega)
  have hcheckj :
      (List.range j).all (fun k =>
        match fRun tm2 k m0EvenQ4BridgeStart with
        | none => true
        | some f => m0EvenQ4Inside f.head) = true := by
    apply List.all_eq_true.mpr
    intro k hk
    have hk39 : k < 39 := by
      have hmem := List.mem_range.mp hk
      omega
    exact (List.all_eq_true.mp m0EvenQ4Bridge_heads) k
      (List.mem_range.mpr hk39)
  have hbridge := bridgeAt T h m0EvenQ4Inside
    m0EvenQ4BridgeStart e j rfl hexact hcheckj hmatch
  rw [hbridge] at hd
  have hdeq : d = frameAt T h m0EvenQ4Inside e :=
    Option.some.inj hd
  have hinside : m0EvenQ4Inside e.head = true := by
    have hh := (List.all_eq_true.mp m0EvenQ4Bridge_heads) j
      (List.mem_range.mpr hj)
    simpa [hexact] using hh
  have hlow : -9 ≤ e.head := by
    simp [m0EvenQ4Inside] at hinside
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

/-- Every prefix of the base n=2 source run stays inside the half-line
on which the generalized and base inputs agree. -/
private theorem m0Even_q4_prefix_head_bound
    (a b : Nat) (h : Int) (ha : 0<a) :
    ∀ k, k < 36+12*a → ∀ d,
      run tm2 k (s1Config 3 2 0 a 0 b h) = some d →
      h-((3*a+9:Int)) ≤ d.head := by
  let T := (s1Config 3 2 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m0EvenQ4CutTape a b h
  have hleft :
      s1LeftFacing 3 2 0 a 0 =
        d1pow a ++ (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh) := by
    simp [s1LeftFacing,binDec_zero,m0Even_binDec_three_two,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 2 0 a 0 b h i
    rw [hleft] at hcell
    have hbit := Agent6Q4Prefix.sideBit_append_left
      (d1pow a) (markerWord 0 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh) i
      (by rw [d1pow_length]; omega)
    rw [hbit] at hcell
    exact hcell.trans (sideBit_d1pow_true a i hi)
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 2 0 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m0EvenQ4Bridge_input_match a b h ha
  have hBridge := bridgeAt T1 hN m0EvenQ4Inside
    m0EvenQ4BridgeStart m0EvenQ4BridgeEnd 39 rfl
    m0EvenQ4Bridge_exact m0EvenQ4Bridge_heads hmatch
  have hBridge' :
      run tm2 39 ⟨3,hN,T1⟩ =
        some ⟨4,hN+3,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m0EvenQ4Inside m0EvenQ4BridgeEnd =
          (⟨4,hN+3,T2⟩ : Config) := by
      apply m0EvenResidueTwo_config_ext
      · simp [frameAt_state,m0EvenQ4BridgeEnd]
      · simp [frameAt_head,m0EvenQ4BridgeEnd] <;> omega
      · rfl
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+3) (3*(a-1)) := by
    intro i hi
    by_cases hi0 : i=0
    · subst i
      let x : Int := hN+3
      have hrel : x-hN=3 := by dsimp [x]; omega
      have hin : m0EvenQ4Inside (x-hN)=true := by
        simp [m0EvenQ4Inside,hrel]
      have hcut := m0EvenQ4CutTape_eq_end_inside a b h x hin
      have hmark :
          decide ((x-hN) ∈ m0EvenQ4BridgeEnd.marked) = true := by
        rw [hrel]
        simp [m0EvenQ4BridgeEnd]
      simpa [T2,x,hN] using hcut.trans hmark
    · let x : Int := hN+3+(i:Int)
      have hrel : x-hN=3+(i:Int) := by dsimp [x]; omega
      have hout : m0EvenQ4Inside (x-hN)=false := by
        simp [m0EvenQ4Inside,hrel]
        omega
      have hcut := m0EvenQ4CutTape_eq_swept a b h x hout
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
      simpa [T2,x] using hcut.trans hblock'
  intro k hk d hd
  let p1 := 3*N
  let p2 := p1+39
  by_cases hk1 : k < p1
  · have hlow := counted_left_sweep_heads N T h hOn hright k
      (by dsimp [p1]; omega) d hd
    dsimp [hN,N] at *
    omega
  · by_cases hk2 : k < p2
    · let j := k-p1
      have hj : j<39 := by dsimp [j,p1] at *; omega
      have hkEq : k=p1+j := by dsimp [j,p1]; omega
      rw [hkEq,run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      have hlow := m0Even_bridge_prefix_lower T1 hN hmatch j hj d hd
      dsimp [hN,N] at *
      omega
    · let j := k-p2
      have hj : j<3*(a-1) := by dsimp [j,p2,p1,N] at *; omega
      have hkEq : k=p1+(39+j) := by dsimp [j,p2,p1]; omega
      rw [hkEq,run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      rw [run_add,hBridge'] at hd
      simp only [Option.bind_some] at hd
      have hhead := E_scan_prefix_head T2 (hN+3) (3*(a-1)) hlinear j hj d hd
      dsimp [hN,N] at *
      omega

/-- The generalized q4 prefix is the base n=2 run framed by its common
readable half-line; the arbitrary high-order tail is not read. -/
theorem m0Even_residue2_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    run tm2 (36+12*a)
      (s1Config L (8*k+2) 0 a 0 b h) =
      some ⟨4,h,m0EvenResidueTwoCutTape L k a b h⟩ := by
  let base : Config := ⟨3,h,(s1Config 3 2 0 a 0 b h).tape⟩
  let background := (s1Config L (8*k+2) 0 a 0 b h).tape
  have hinput := m0EvenResidueTwo_input_matches L k a b h hL hbound
  have hstart :
      frame (m0EvenResidueTwoInside a h) background base =
        s1Config L (8*k+2) 0 a 0 b h := by
    apply m0EvenResidueTwo_config_ext
    · rfl
    · rfl
    · funext x
      by_cases hx : m0EvenResidueTwoInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 36+12*a → ∀ d,
        run tm2 j base = some d →
        m0EvenResidueTwoInside a h d.head = true := by
    intro j hj d hd
    have hlow := m0Even_q4_prefix_head_bound a b h ha j hj d hd
    simpa [m0EvenResidueTwoInside] using hlow
  have hlift := run_frame tm2 (m0EvenResidueTwoInside a h)
    background base (36+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (36+12*a) base =
        some (⟨4,h,m0EvenQ4CutTape a b h⟩ : Config) := by
    have hrun := m0Even_q4_prefix_run a b h ha
    simpa [base] using hrun
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  simpa [m0EvenResidueTwoCutTape,background] using hlift

/-- On the common prefix, the lifted cut has the base output stream;
after it, the source and target share the same untouched high-order tail. -/
theorem m0Even_residue2_q4_prefix_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m0EvenResidueTwoCutTape L k a b h (h-(i:Int)) =
        sideBit (m0EvenResidueTwoLeftFacing L k a) i := by
  intro i
  by_cases hi : i < 3*a+10
  · have hin : m0EvenResidueTwoInside a h (h-(i:Int)) = true := by
      simp [m0EvenResidueTwoInside]
      omega
    have hcut := m0EvenResidueTwo_cut_eq_base_inside L k a b h
      (h-(i:Int)) hin
    have hbase := m0Even_q4_prefix_leftFacing a b h ha i
    have hbaseBits :
        sideBit (m0EvenQ4LeftFacing a) i =
          sideBit (m0EvenResidueTwoLeftFacing L k a) i := by
      rw [m0EvenResidueTwo_base_target_left,
        m0EvenResidueTwoLeftFacing]
      have hlen := m0EvenResidueTwo_targetPrefix_length a
      rw [Agent6Q4Prefix.sideBit_append_left
        (m0EvenResidueTwoTargetPrefix a) lh i (by omega)]
      rw [Agent6Q4Prefix.sideBit_append_left
        (m0EvenResidueTwoTargetPrefix a)
        (binDec (L-3) k ++ lh) i (by omega)]
    exact hcut.trans (hbase.trans hbaseBits)
  · have hout : m0EvenResidueTwoInside a h (h-(i:Int)) = false := by
      simp [m0EvenResidueTwoInside]
      omega
    have hcut := m0EvenResidueTwo_cut_eq_input L k a b h
      (h-(i:Int)) hout
    have hsourceCell :=
      s1Config_left_cell L (8*k+2) 0 a 0 b h i
    have hsourceBits :
        sideBit (s1LeftFacing L (8*k+2) 0 a 0) i =
          sideBit (binDec (L-3) k ++ lh) (i-(3*a+10)) := by
      rw [m0EvenResidueTwo_source_left L k a hL hbound]
      rw [Agent6Q4Prefix.sideBit_append_right
        (m0EvenResidueTwoInputPrefix a)
        (binDec (L-3) k ++ lh) i (by
          rw [m0EvenResidueTwo_inputPrefix_length]
          omega)]
    have htargetBits :
        sideBit (m0EvenResidueTwoLeftFacing L k a) i =
          sideBit (binDec (L-3) k ++ lh) (i-(3*a+10)) := by
      rw [m0EvenResidueTwoLeftFacing]
      rw [Agent6Q4Prefix.sideBit_append_right
        (m0EvenResidueTwoTargetPrefix a)
        (binDec (L-3) k ++ lh) i (by
          rw [m0EvenResidueTwo_targetPrefix_length]
          omega)]
    rw [hsourceBits] at hsourceCell
    calc
      m0EvenResidueTwoCutTape L k a b h (h-(i:Int)) =
          (s1Config L (8*k+2) 0 a 0 b h).tape (h-(i:Int)) := hcut
      _ = sideBit (binDec (L-3) k ++ lh) (i-(3*a+10)) := hsourceCell
      _ = sideBit (m0EvenResidueTwoLeftFacing L k a) i :=
        htargetBits.symm

private theorem m0Even_residue2_q4_prefix_far_tail
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m0EvenResidueTwoCutTape L k a b h (h+1+(i:Int)) = false := by
  intro i hi
  rw [m0EvenResidueTwo_cut_eq_base L k a b h (h+1+(i:Int)) (by omega)]
  exact m0Even_q4_prefix_far_tail a b h ha i hi

private theorem m0Even_residue2_q4_prefix_rightShape
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    q4RightShape (m0EvenResidueTwoCutTape L k a b h) h b := by
  apply q4RightShape_congr
    (m0EvenQ4CutTape a b h)
    (m0EvenResidueTwoCutTape L k a b h) h b
  · intro x hx
    exact (m0EvenResidueTwo_cut_eq_base L k a b h x hx).symm
  · exact m0Even_q4_prefix_rightShape a b h ha

/-- Complete generalized q4 prefix interface for n=8*k+2. -/
theorem m0Even_residue2_q4_prefix_data
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    ∃ Tq,
      run tm2 (36+12*a) (s1Config L (8*k+2) 0 a 0 b h) =
        some ⟨4,h,Tq⟩ ∧
      (∀ i : Nat, Tq (h-(i:Int)) =
        sideBit (m0EvenResidueTwoLeftFacing L k a) i) ∧
      q4RightShape Tq h b ∧
      (∀ i : Nat, 9+3*b ≤ i → Tq (h+1+(i:Int)) = false) := by
  refine ⟨m0EvenResidueTwoCutTape L k a b h, ?_, ?_, ?_, ?_⟩
  · exact m0Even_residue2_q4_prefix_source L k a b h hL hbound ha
  · exact m0Even_residue2_q4_prefix_leftFacing L k a b h hL hbound ha
  · exact m0Even_residue2_q4_prefix_rightShape L k a b h hL hbound ha
  · exact m0Even_residue2_q4_prefix_far_tail L k a b h hL hbound ha

/-- The generic q4 suffix reconstructs the canonical n-1=8*k+1 target. -/
private theorem m0EvenResidueTwo_suffix_target_left
    (L k a b : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    s1LeftFacing L (8*k+1) 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m0EvenResidueTwoLeftFacing L k a).drop 1 := by
  have hbinPow := binDec_pow2_sub_one (a-1) b
  have hlen : (a-1)+b+2 = a+b+1 := by omega
  have hexp : (a-1)+2 = a+1 := by omega
  have hbin : binDec (a+b+1) (2^b-1) =
      d0pow b ++ d1pow (a+1) := by
    simpa [hlen,hexp] using hbinPow
  have hbound' : 8*k+1 < 2^L := by omega
  have hbin1 := binDec_residue1 L k hL hbound'
  unfold s1LeftFacing
  rw [hbin,hbin1]
  rw [← hexp]
  rw [d1pow_add_right (a-1) 2]
  simp [m0EvenResidueTwoLeftFacing,m0EvenResidueTwoTargetPrefix,
    List.drop,List.append_assoc]

/-- Since v2(8*k+2)=1, this family has the same reset cost as n=2. -/
private theorem m0EvenResidueTwo_resetPrefixCost_eq (k a b : Nat) :
    resetPrefixCost 0 (8*k+2) a b = 75+12*a+3*b := by
  have hvOdd : BB6ChampionArithmetic.v2 (4*k+1) = 0 :=
    v2_of_odd (4*k+1) (by omega)
  have hv : BB6ChampionArithmetic.v2 (8*k+2) = 1 := by
    have h := v2_of_even (8*k+2) (by omega) (by omega)
    have hdiv : (8*k+2)/2 = 4*k+1 := by omega
    rw [hdiv,hvOdd] at h
    omega
  simp [resetPrefixCost,hv]
  omega

/-- Full source-level Rst0 reset prefix for every admissible n=8*k+2. -/
theorem m0Even_residue2_q4_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 0 (8*k+2) a b)
      (s1Config L (8*k+2) 0 a 0 b h) =
      some (s1Config L (8*k+1) 2 (a+b+1) (2^b-1) 0
        (h+5+3*b)) := by
  obtain ⟨Tq,hprefix,hleft,hshape,htail⟩ :=
    m0Even_residue2_q4_prefix_data L k a b h hL hbound ha
  have happend := m0EvenResidueTwo_suffix_target_left L k a b hL hbound ha
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    L (8*k+1) 2 (a+b+1) (2^b-1)
    (m0EvenResidueTwoLeftFacing L k a)
    hshape htail hleft happend
  have hsum :
      resetPrefixCost 0 (8*k+2) a b = (36+12*a)+(39+3*b) := by
    rw [m0EvenResidueTwo_resetPrefixCost_eq]
    omega
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

/-- Complete original-TM2 m=0 counted increment for every n=8*k+2,
including the exact geometric all-ones drain. -/
theorem m0Even_residue2_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+2 < 2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 0 (8*k+2) a b)
      (s1Config L (8*k+2) 0 a 0 b h) =
      some (s1Config L (8*k+1) 2 (a+b+1) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m0Even_residue2_q4_reset_prefix_source
    L k a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 0 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*k+1) 2 (a+b+1) b (h+5+3*b)
    (s1Config L (8*k+2) 0 a 0 b h)
    (resetPrefixCost 0 (8*k+2) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms binDec_residue2
#print axioms binDec_residue1
#print axioms m0Even_residue2_q4_prefix_source
#print axioms m0Even_residue2_q4_reset_prefix_source
#print axioms m0Even_residue2_counted_increment_source

end BB6Coverage.Agent24M0EvenResidueTwo
