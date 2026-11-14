import M1EvenQ4Suffix
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent42M1EvenResidueSix

open BB6Coverage
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent42M1EvenSuffix
open BB6Coverage.Agent8CountedReset
open BB6ChampionArithmetic

/-- The low-three-bit decomposition used by every m=1, n=6 (mod 8) source. -/
theorem binDec_residue6 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+6 < 2^L) :
    binDec L (8*k+6) = d1 ++ d0 ++ d0 ++ binDec (L-3) k := by
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
  have hq1 : 4*k+3 < 2^(L-1) := by
    rw [hpow2]
    omega
  have hq2 : 2*k+1 < 2^(L-2) := by
    rw [hpow1]
    omega
  have h1 : binDec L (8*k+6) =
      d1 ++ binDec (L-1) (4*k+3) := by
    rw [show L = (L-1)+1 by omega,
      show 8*k+6 = 2*(4*k+3) by omega]
    exact binDec_even (L-1) (4*k+3) hq1
  have h2 : binDec (L-1) (4*k+3) =
      d0 ++ binDec (L-2) (2*k+1) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*k+3 = 2*(2*k+1)+1 by omega]
    exact binDec_odd (L-2) (2*k+1) hq2
  have h3 : binDec (L-2) (2*k+1) =
      d0 ++ binDec (L-3) k := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_odd (L-3) k hk
  rw [h1,h2,h3]
  simp [List.append_assoc]

/-- The successor low-three-bit decomposition, with the same arbitrary tail. -/
theorem binDec_residue5 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+5 < 2^L) :
    binDec L (8*k+5) = d0 ++ d1 ++ d0 ++ binDec (L-3) k := by
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
  have h1 : binDec L (8*k+5) =
      d0 ++ binDec (L-1) (4*k+2) := by
    rw [show L = (L-1)+1 by omega,
      show 8*k+5 = 2*(4*k+2)+1 by omega]
    exact binDec_odd (L-1) (4*k+2) hq1
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

private theorem sideBit_residue6_eq_residue5_after5
    (tail : List Bool) (j : Nat) (hj : 5 ≤ j) :
    sideBit (d1 ++ d0 ++ d0 ++ tail) j =
      sideBit (d0 ++ d1 ++ d0 ++ tail) j := by
  by_cases hj5 : j = 5
  · subst j
    simp [sideBit,d0,d1]
  · have hj6 : 6 ≤ j := by omega
    calc
      sideBit (d1 ++ d0 ++ d0 ++ tail) j =
          sideBit ((d1 ++ d0) ++ (d0 ++ tail)) j := by
            simp [List.append_assoc]
      _ = sideBit (d0 ++ tail) (j-6) :=
        sideBit_append_right (d1 ++ d0) (d0 ++ tail) j
          (by simp [d0,d1]; omega)
      _ = sideBit ((d0 ++ d1) ++ (d0 ++ tail)) j := by
        symm
        exact sideBit_append_right (d0 ++ d1) (d0 ++ tail) j
          (by simp [d0,d1]; omega)
      _ = sideBit (d0 ++ d1 ++ d0 ++ tail) j := by
        simp [List.append_assoc]

private theorem sweptLeft_head_eq_source (q : Nat)
    (T : Int → Bool) (h : Int) :
    sweptLeft q T h (h-(q:Int)) = T (h-(q:Int)) := by
  induction q with
  | zero => simp [sweptLeft]
  | succ q ih =>
      have hcoord : h-((q+1:Int)) = (h-1)-(q:Int) := by omega
      rw [show sweptLeft (q+1) T h =
        sweptLeft q (holeThree T h) (h-1) by rfl]
      rw [hcoord, ih]
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
  rw [show 2 = 1+1 by omega, run_add, leftSweep_one T h ht]
  simp [run,rawStep,readSlot,applyMove,tm2,hr]

/-- Every intermediate head in the counted left sweep stays no farther left
than the final sweep head. -/
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
    rw [show Tq = sweptLeft q T h by rfl, sweptLeft_head_eq_source]
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
  have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
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
      exact ⟨c, by simpa [fRun] using h⟩
  | succ n ih =>
      have h' : (fRun m n c).bind (fStep m) = some d := by
        simpa [fRun] using h
      cases hp : fRun m n c with
      | none =>
          simp [hp] at h'
      | some e =>
          by_cases hk' : k ≤ n
          · exact ih hp hk'
          · have hkEq : k = n+1 := by omega
            subst k
            exact ⟨d,h⟩

private theorem m1Even_bridge_prefix_lower
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ y, m1EvenQ4Inside y = true →
      T (h+y) = decide (y ∈ m1EvenQ4BridgeStart.marked))
    (j : Nat) (hj : j < 41) (d : Config)
    (hd : run tm2 j ⟨3,h,T⟩ = some d) :
    h-9 ≤ d.head := by
  obtain ⟨e,hexact⟩ :=
    fRun_prefix_exists m1EvenQ4Bridge_exact (by omega)
  have hcheckj :
      (List.range j).all (fun k =>
        match fRun tm2 k m1EvenQ4BridgeStart with
        | none => true
        | some f => m1EvenQ4Inside f.head) = true := by
    apply List.all_eq_true.mpr
    intro k hk
    have hk41 : k < 41 := by
      have hmem := List.mem_range.mp hk
      omega
    exact (List.all_eq_true.mp m1EvenQ4Bridge_heads) k
      (List.mem_range.mpr hk41)
  have hbridge := bridgeAt T h m1EvenQ4Inside
    m1EvenQ4BridgeStart e j rfl hexact hcheckj hmatch
  rw [hbridge] at hd
  have hdeq : d = frameAt T h m1EvenQ4Inside e :=
    Option.some.inj hd
  have hinside : m1EvenQ4Inside e.head = true := by
    have hh := (List.all_eq_true.mp m1EvenQ4Bridge_heads) j
      (List.mem_range.mpr hj)
    simpa [hexact] using hh
  have hlow : -9 ≤ e.head := by
    simp [m1EvenQ4Inside] at hinside
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

/-- The 44+12a prefix has a one-sided head bound sharp enough to frame any
arbitrary S1 tail following the first five low-order counter bits. -/
private theorem m1Even_q4_prefix_head_bound
    (a b : Nat) (h : Int) :
    ∀ k, k < 44+12*a → ∀ d,
      run tm2 k (s1Config 3 6 1 a 0 b h) = some d →
      h-((3*a+1:Int))-9 ≤ d.head := by
  let T := (s1Config 3 6 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m1EvenQ4CutTape a b h
  have hbin36 : binDec 3 6 = d1 ++ d0 ++ d0 := by
    have hh := binDec_residue6 3 0 (by omega) (by decide)
    simpa [binDec_zero,d1pow] using hh
  have hbaseInputLeft :
      s1LeftFacing 3 6 1 a 0 =
        (d1pow a ++ markerWord 1 ++ d0 ++ d1 ++ d0 ++ d0) ++ lh := by
    simp [s1LeftFacing,binDec_zero,hbin36,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 6 1 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 6 1 a 0) i = true := by
      rw [hbaseInputLeft]
      by_cases hi3 : i < 3*a
      · have hbit := sideBit_append_left (d1pow a)
          (markerWord 1 ++ d0 ++ d1 ++ d0 ++ d0 ++ lh) i
          (by rw [d1pow_length]; omega)
        rw [hbit]
        exact sideBit_d1pow_true a i hi3
      · have hieq : i = 3*a := by omega
        subst i
        have hbit := sideBit_append_right (d1pow a)
          (markerWord 1 ++ d0 ++ d1 ++ d0 ++ d0 ++ lh) (3*a)
          (by rw [d1pow_length])
        rw [hbit]
        simp [markerWord,sideBit]
    rw [hside] at hcell
    exact hcell
  have hright : T (h+1) = false := by
    simpa [T,s1PhysicalRight_source,sideBit] using
      s1Config_right_cell 3 6 1 a 0 b h 0
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m1EvenQ4Bridge_input_match a b h
  have hBridge := bridgeAt T1 hN m1EvenQ4Inside
    m1EvenQ4BridgeStart m1EvenQ4BridgeEnd 41 rfl
    m1EvenQ4Bridge_exact m1EvenQ4Bridge_heads hmatch
  have hBridge' :
      run tm2 41 ⟨3,hN,T1⟩ = some ⟨4,hN+5,T2⟩ := by
    simpa [T1,T2,N,hN,m1EvenQ4CutTape] using hBridge
  have hlinear : linearRightOnes T2 (hN+5) (3*a) := by
    intro i hi
    let x := hN+5+(i:Int)
    have houtside : m1EvenQ4Inside (x-hN) = false := by
      simp [m1EvenQ4Inside,x]
      omega
    have hframe : T2 x = T1 x := by
      simpa [T2,m1EvenQ4CutTape] using
        frameAt_tape_outside T1 hN m1EvenQ4Inside
          m1EvenQ4BridgeEnd x houtside
    have hT1 : T1 x = true := by
      by_cases hx : x ≤ h
      · let j := 3*a-4-i
        have hj : j+1 < N := by
          dsimp [j,N,x,hN] at *
          omega
        have hblock := sweptLeft_block N j T h hj
        have hcoord : x = h-(j:Int) := by
          dsimp [j,N,x,hN]
          omega
        rw [hcoord] at hblock
        exact hblock
      · have hxCases : x = h+1 ∨ x = h+2 ∨ x = h+3 := by
          dsimp [x,N,hN] at *
          omega
        rcases hxCases with hx1|hx2|hx3
        · rw [hx1]
          simpa [T1,N] using sweptLeft_plus1 (3*a) T h
        · rw [hx2]
          have hp := sweptLeft_preserves_right N T h (h+2) (by omega)
          have hsrc : T (h+2) = true := by
            simpa [T,s1PhysicalRight_source,sideBit] using
              s1Config_right_cell 3 6 1 a 0 b h 1
          rw [hp,hsrc]
        · rw [hx3]
          have hp := sweptLeft_preserves_right N T h (h+3) (by omega)
          have hsrc : T (h+3) = true := by
            simpa [T,s1PhysicalRight_source,sideBit] using
              s1Config_right_cell 3 6 1 a 0 b h 2
          rw [hp,hsrc]
    simpa [T2] using hframe.trans hT1
  intro k hk d hd
  let p1 := 3*N
  let p2 := p1+41
  by_cases hk1 : k < p1
  · have hlow := counted_left_sweep_heads N T h hOn hright k
      (by dsimp [p1,N] at *; omega) d hd
    dsimp [hN,N] at *
    omega
  · by_cases hk2 : k < p2
    · let j := k-p1
      have hj : j < 41 := by dsimp [j,p1] at *; omega
      have hkEq : k = p1+j := by dsimp [j,p1]; omega
      rw [hkEq,run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      have hlow := m1Even_bridge_prefix_lower T1 hN hmatch j hj d hd
      dsimp [hN,N] at *
      omega
    · let j := k-p2
      have hj : j < 3*a := by dsimp [j,p2,p1,N] at *; omega
      have hkEq : k = p1+(41+j) := by dsimp [j,p2,p1]; omega
      rw [hkEq,run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      rw [run_add,hBridge'] at hd
      simp only [Option.bind_some] at hd
      have hhead := E_scan_prefix_head T2 (hN+5) (3*a) hlinear j hj d hd
      dsimp [hN,N] at *
      omega

/-- The general source is framed by the n=6 source on the half-line actually
read by its prefix.  To the left of that line the original general tail is
left untouched. -/
def m1EvenResidueSixInside (a : Nat) (h : Int) : Int → Bool :=
  fun x => decide (h-((3*a+1:Int))-9 ≤ x)

def m1EvenResidueSixCutTape
    (L k a b : Nat) (h : Int) : Int → Bool :=
  (frame (m1EvenResidueSixInside a h)
    (s1Config L (8*k+6) 1 a 0 b h).tape
    (⟨4,h+4,m1EvenQ4CutTape a b h⟩ : Config)).tape

private def m1EvenResidueSixInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 1 ++ d0 ++ d1 ++ d0 ++ d0

private def m1EvenResidueSixTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ d0 ++ d1 ++ d0

private def m1EvenResidueSixInputBoundary (a : Nat) : List Bool :=
  d1pow a ++ markerWord 1 ++ d0

private def m1EvenResidueSixTargetBoundary (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0


/-- Config extensionality for the repository's explicit infinite-tape record. -/
private theorem m1EvenResidueSix_config_ext_by_fields (c d : Config)
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

/-- The n=8k+6 and n=6 S1 source tapes agree on the half-line read by
the n=6 prefix.  Their left words share the complete low-order input prefix;
their right words depend only on b. -/
private theorem m1EvenResidueSix_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+6 < 2^L) :
    ∀ x, m1EvenResidueSixInside a h x = true →
      (s1Config L (8*k+6) 1 a 0 b h).tape x =
      (s1Config 3 6 1 a 0 b h).tape x := by
  have hbin6 := binDec_residue6 L k hL hbound
  have hbin36 : binDec 3 6 = d1 ++ d0 ++ d0 := by
    have hh := binDec_residue6 3 0 (by omega) (by decide)
    simpa [binDec_zero,d1pow] using hh
  have hsourceLeft :
      s1LeftFacing L (8*k+6) 1 a 0 =
        m1EvenResidueSixInputPrefix a ++
          (binDec (L-3) k ++ lh) := by
    simp [s1LeftFacing,m1EvenResidueSixInputPrefix,
      binDec_zero,hbin6,List.append_assoc]
  have hbaseLeft :
      s1LeftFacing 3 6 1 a 0 =
        m1EvenResidueSixInputPrefix a ++ lh := by
    simp [s1LeftFacing,m1EvenResidueSixInputPrefix,
      binDec_zero,hbin36,List.append_assoc]
  have hprefixLength :
      (m1EvenResidueSixInputPrefix a).length = 3*a+15 := by
    simp [m1EvenResidueSixInputPrefix,d1pow_length,markerWord,d0,d1]
  intro x hx
  by_cases hleft : x ≤ h
  · let i := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i : Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int) = x := by omega
    have hthreshold : h - ((3*a+1:Int)) - 9 ≤ x := by
      simpa [m1EvenResidueSixInside] using hx
    have hi : i ≤ 3*a+10 := by omega
    have hiPrefix : i < (m1EvenResidueSixInputPrefix a).length := by
      rw [hprefixLength]
      omega
    have hsrc := s1Config_left_cell L (8*k+6) 1 a 0 b h i
    have hbase := s1Config_left_cell 3 6 1 a 0 b h i
    rw [hcoord] at hsrc hbase
    rw [hsourceLeft] at hsrc
    rw [hbaseLeft] at hbase
    have hsrcBit := sideBit_append_left
      (m1EvenResidueSixInputPrefix a) (binDec (L-3) k ++ lh)
      i hiPrefix
    have hbaseBit := sideBit_append_left
      (m1EvenResidueSixInputPrefix a) lh i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbase
    exact hsrc.trans hbase.symm
  · let i := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i : Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int) = x := by omega
    have hsrc := s1Config_right_cell L (8*k+6) 1 a 0 b h i
    have hbase := s1Config_right_cell 3 6 1 a 0 b h i
    rw [hcoord] at hsrc hbase
    exact hsrc.trans hbase.symm

/-- Lift the 44+12a source prefix from n=6 to every admissible n=8k+6.
The original n=6 run reads only the common half-line, so the rest of the
general source tape is preserved exactly by run_frame. -/
theorem m1Even_residue6_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+6 < 2^L) :
    run tm2 (44+12*a)
      (s1Config L (8*k+6) 1 a 0 b h) =
      some ⟨4,h+4,m1EvenResidueSixCutTape L k a b h⟩ := by
  let base : Config := ⟨3,h,(s1Config 3 6 1 a 0 b h).tape⟩
  let background := (s1Config L (8*k+6) 1 a 0 b h).tape
  have hinput := m1EvenResidueSix_input_matches L k a b h hL hbound
  have hstart :
      frame (m1EvenResidueSixInside a h) background base =
        s1Config L (8*k+6) 1 a 0 b h := by
    apply m1EvenResidueSix_config_ext_by_fields
    · rfl
    · rfl
    · funext x
      by_cases hx : m1EvenResidueSixInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 44+12*a → ∀ d,
        run tm2 j base = some d →
        m1EvenResidueSixInside a h d.head = true := by
    intro j hj d hd
    have hlow := m1Even_q4_prefix_head_bound a b h j hj d hd
    simpa [m1EvenResidueSixInside] using hlow
  have hlift := run_frame tm2 (m1EvenResidueSixInside a h)
    background base (44+12*a) hheads
  rw [hstart] at hlift
  rw [m1Even_q4_prefix_run a b h] at hlift
  simp only [Option.map_some] at hlift
  simpa [m1EvenResidueSixCutTape,background] using hlift

def m1EvenResidueSixLeftFacing (L k a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++ d0 ++ binDec L (8*k+5) ++ lh

private theorem m1EvenResidueSix_cut_eq_base
    (L k a b : Nat) (h x : Int) (hx : h ≤ x) :
    m1EvenResidueSixCutTape L k a b h x =
      m1EvenQ4CutTape a b h x := by
  have hin : m1EvenResidueSixInside a h x = true := by
    simp [m1EvenResidueSixInside]
    omega
  simp [m1EvenResidueSixCutTape,frame,hin]

private theorem m1EvenResidueSix_cut_eq_input
    (L k a b : Nat) (h x : Int)
    (hout : m1EvenResidueSixInside a h x = false) :
    m1EvenResidueSixCutTape L k a b h x =
      (s1Config L (8*k+6) 1 a 0 b h).tape x := by
  simp [m1EvenResidueSixCutTape,frame,hout]

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

private theorem m1EvenResidueSix_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+6 < 2^L) :
    ∀ i, m1EvenResidueSixCutTape L k a b h (h-(i:Int)) =
      sideBit (m1EvenResidueSixLeftFacing L k a) i := by
  have hbound5 : 8*k+5 < 2^L := by omega
  have hbin36 : binDec 3 6 = d1 ++ d0 ++ d0 := by
    have hh := binDec_residue6 3 0 (by omega) (by decide)
    simpa [binDec_zero,d1pow] using hh
  have hbin35 : binDec 3 5 = d0 ++ d1 ++ d0 := by
    have hh := binDec_residue5 3 0 (by omega) (by decide)
    simpa [binDec_zero,d1pow] using hh
  have hbin6 := binDec_residue6 L k hL hbound
  have hbin5 := binDec_residue5 L k hL hbound5
  have hbaseLeft :
      m1EvenQ4LeftFacing a =
        m1EvenResidueSixTargetPrefix a ++ lh := by
    simp [m1EvenQ4LeftFacing,m1EvenResidueSixTargetPrefix,
      hbin35,List.append_assoc]
  have htargetLeft :
      m1EvenResidueSixLeftFacing L k a =
        m1EvenResidueSixTargetPrefix a ++
          (binDec (L-3) k ++ lh) := by
    simp [m1EvenResidueSixLeftFacing,m1EvenResidueSixTargetPrefix,
      hbin5,List.append_assoc]
  have htargetPrefixLength :
      (m1EvenResidueSixTargetPrefix a).length = 3*a+15 := by
    simp [m1EvenResidueSixTargetPrefix,d1pow_length,markerWord,d0,d1]
  have hinputLeft :
      s1LeftFacing L (8*k+6) 1 a 0 =
        m1EvenResidueSixInputBoundary a ++
          (d1 ++ d0 ++ d0 ++ binDec (L-3) k ++ lh) := by
    simp [s1LeftFacing,m1EvenResidueSixInputBoundary,
      binDec_zero,hbin6,List.append_assoc]
  have htargetBoundary :
      m1EvenResidueSixLeftFacing L k a =
        m1EvenResidueSixTargetBoundary a ++
          (d0 ++ d1 ++ d0 ++ binDec (L-3) k ++ lh) := by
    simp [m1EvenResidueSixLeftFacing,m1EvenResidueSixTargetBoundary,
      hbin5,List.append_assoc]
  have hinputBoundaryLength :
      (m1EvenResidueSixInputBoundary a).length = 3*a+6 := by
    simp [m1EvenResidueSixInputBoundary,d1pow_length,markerWord,d0]
  have htargetBoundaryLength :
      (m1EvenResidueSixTargetBoundary a).length = 3*a+6 := by
    simp [m1EvenResidueSixTargetBoundary,d1pow_length,markerWord,d0]
  intro i
  by_cases hi : i ≤ 3*a+10
  · have hin : m1EvenResidueSixInside a h (h-(i:Int)) = true := by
      simp [m1EvenResidueSixInside]
      omega
    rw [m1EvenResidueSix_cut_eq_base L k a b h (h-(i:Int)) (by omega)]
    rw [m1Even_q4_prefix_leftFacing a b h i]
    rw [hbaseLeft,htargetLeft]
    have hbaseBit := sideBit_append_left
      (m1EvenResidueSixTargetPrefix a) lh i
      (by rw [htargetPrefixLength]; omega)
    have htargetBit := sideBit_append_left
      (m1EvenResidueSixTargetPrefix a) (binDec (L-3) k ++ lh) i
      (by rw [htargetPrefixLength]; omega)
    rw [hbaseBit,htargetBit]
  · have hout : m1EvenResidueSixInside a h (h-(i:Int)) = false := by
      simp [m1EvenResidueSixInside]
      omega
    rw [m1EvenResidueSix_cut_eq_input L k a b h (h-(i:Int)) hout]
    rw [s1Config_left_cell L (8*k+6) 1 a 0 b h i]
    rw [hinputLeft,htargetBoundary]
    have hinputBit := sideBit_append_right
      (m1EvenResidueSixInputBoundary a)
      (d1 ++ d0 ++ d0 ++ binDec (L-3) k ++ lh) i
      (by rw [hinputBoundaryLength]; omega)
    have htargetBit := sideBit_append_right
      (m1EvenResidueSixTargetBoundary a)
      (d0 ++ d1 ++ d0 ++ binDec (L-3) k ++ lh) i
      (by rw [htargetBoundaryLength]; omega)
    rw [hinputBit,htargetBit]
    apply sideBit_residue6_eq_residue5_after5
    omega

private theorem m1EvenResidueSix_rightShape
    (L k a b : Nat) (h : Int) :
    q4RightShape (m1EvenResidueSixCutTape L k a b h) h b := by
  apply q4RightShape_congr (m1EvenQ4CutTape a b h)
    (m1EvenResidueSixCutTape L k a b h) h b
  · intro x hx
    symm
    exact m1EvenResidueSix_cut_eq_base L k a b h x hx
  · exact m1Even_q4_prefix_rightShape a b h

private theorem m1EvenResidueSix_far_tail
    (L k a b : Nat) (h : Int) :
    ∀ i, 9+3*b ≤ i →
      m1EvenResidueSixCutTape L k a b h (h+1+(i:Int)) = false := by
  intro i hi
  rw [m1EvenResidueSix_cut_eq_base L k a b h
    (h+1+(i:Int)) (by omega)]
  exact m1Even_q4_prefix_far_tail a b h i hi

private theorem m1EvenResidueSix_target_left
    (L k a b : Nat) :
    s1LeftFacing L (8*k+5) 0 (a+b+2) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m1EvenResidueSixLeftFacing L k a).drop 1 := by
  unfold s1LeftFacing m1EvenResidueSixLeftFacing
  rw [binDec_pow2_sub_one]
  rw [d1pow_add_right a 2]
  simp [List.drop,List.append_assoc]

/-- A complete source-level m=1 reset prefix for every n=8k+6.  The only
specialized simulation reused is the n=6 finite bridge; its arbitrary left
tail is transported by run_frame, and the suffix consumes only the right
counter and the explicitly described left-facing stream. -/
theorem m1Even_residue6_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+6 < 2^L) :
    run tm2 (79+12*a+3*b)
      (s1Config L (8*k+6) 1 a 0 b h) =
      some (s1Config L (8*k+5) 0 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  let T := m1EvenResidueSixCutTape L k a b h
  let sourceLeft := m1EvenResidueSixLeftFacing L k a
  have hprefix := m1Even_residue6_q4_prefix_source L k a b h hL hbound
  have hshape := m1EvenResidueSix_rightShape L k a b h
  have htail := m1EvenResidueSix_far_tail L k a b h
  have hleft := m1EvenResidueSix_leftFacing L k a b h hL hbound
  have happend := m1EvenResidueSix_target_left L k a b
  have hfullSuffix := q4_suffix_run_to_s1Config
    T h b L (8*k+5) 0 (a+b+2) (2^b-1) sourceLeft
    hshape htail hleft happend
  have hfirst := m1EvenQ4First4_at T h hshape.1
  have hnum : 39+3*b = 4+(35+3*b) := by omega
  rw [hnum,run_add,hfirst] at hfullSuffix
  simp only [Option.bind_some] at hfullSuffix
  have hnumTotal : 79+12*a+3*b =
      (44+12*a)+(35+3*b) := by omega
  rw [hnumTotal,run_add,hprefix]
  simp only [Option.bind_some]
  exact hfullSuffix

/-- Counted drain closes the full generic residue-six increment. -/
theorem m1Even_residue6_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+6 < 2^L) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 1 (8*k+6) a b)
      (s1Config L (8*k+6) 1 a 0 b h) =
      some (s1Config L (8*k+5) 0 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hvodd : v2 (4*k+3) = 0 :=
    v2_of_odd (4*k+3) (by omega)
  have hfactor : 8*k+6 = 2*(4*k+3) := by omega
  have hv : v2 (8*k+6) = 1 := by
    rw [hfactor]
    have hgt : 1 < 2*(4*k+3) := by omega
    have heven : (2*(4*k+3)) % 2 = 0 := by omega
    have hdiv : (2*(4*k+3)) / 2 = 4*k+3 := by omega
    simp [v2,hgt,heven,hdiv,hvodd]
  have hcost : resetPrefixCost 1 (8*k+6) a b =
      79+12*a+3*b := by
    simp [resetPrefixCost,hv]
    omega
  have hprefix := m1Even_residue6_reset_prefix_source
    L k a b h hL hbound
  have hdrainBound := resetDrainBound a b 1 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*k+5) 0 (a+b+2) b (h+5+3*b)
    (s1Config L (8*k+6) 1 a 0 b h)
    (resetPrefixCost 1 (8*k+6) a b)
    (by simpa [hcost] using hprefix)
    (by simpa [resetDelta] using hdrainBound)
  rw [proposedIncrementCost_decomp 1 (8*k+6) a b,hcost]
  exact hrun

end BB6Coverage.Agent42M1EvenResidueSix
