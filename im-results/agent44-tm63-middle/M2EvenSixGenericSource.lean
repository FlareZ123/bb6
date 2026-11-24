import M2EvenSixQ4Prefix
import M0EvenSixHeadBound
import Lean.Elab.Tactic.Omega

/-!
# Generic original-table m=2, n=8*q+6 q4 reset prefix

The existing 38-step m=2,n=6 bridge has a 44+12*a q4 prefix.
Its read frame reaches only the first 3*a+12 cells of the head-facing
source word.  For every n=8*q+6, both the source and decremented target
BinDec words have the same three-block boundary as n=6 and n=5,
respectively, followed by the same arbitrary BinDec(L-3,q) tail.
A half-line frame therefore lifts the exact base run to all q.

This is the complementary odd-quotient extension of the existing
n=16*k+6 source theorem.  It proves the complete q4 reset prefix to the
next S1 configuration; the later counted drain remains a separate generic
composition.  It is not a complete TM63 itinerary or a BB(6) upper bound.
-/

namespace BB6Coverage.Agent44M2EvenSixGenericSource

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent48M2EvenSixQ4
open BB6Coverage.Agent42M0EvenSixHeadBound
open BB6ChampionArithmetic

set_option maxHeartbeats 5000000

private def m2EvenSixGenericInside (a : Nat) (h : Int) : Int → Bool :=
  fun x => decide (h-((3*a+11:Int)) ≤ x)

private def m2EvenSixGenericInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 2 ++ d0 ++ d1 ++ [false,false]

private def m2EvenSixGenericTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ [true,true]

private def m2EvenSixGenericCommonTail (L q : Nat) : List Bool :=
  [true] ++ d0 ++ binDec (L-3) q ++ lh

private def m2EvenSixGenericInputLeftFacing (L q a : Nat) : List Bool :=
  m2EvenSixGenericInputPrefix a ++ m2EvenSixGenericCommonTail L q

private def m2EvenSixGenericCutTape
    (L q a b : Nat) (h : Int) : Int → Bool :=
  (frame (m2EvenSixGenericInside a h)
    (s1Config L (8*q+6) 2 a 0 b h).tape
    (⟨4,h,m2EvenSixQ4CutTape a b h⟩ : Config)).tape

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

private theorem m2EvenSixGeneric_binDec_source
    (L q : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+6 < 2^L) :
    binDec L (8*q+6) =
      d1 ++ d0 ++ d0 ++ binDec (L-3) q := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    calc
      2^L = 2^((L-3)+3) := by congr 1; omega
      _ = 2^(L-3) * 2^3 := by rw [Nat.pow_add]
      _ = 8 * 2^(L-3) := by
        rw [show (2:Nat)^3 = 8 by decide]
        exact Nat.mul_comm _ _
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    calc
      2^(L-1) = 2^((L-3)+2) := by congr 1; omega
      _ = 2^(L-3) * 2^2 := by rw [Nat.pow_add]
      _ = 4 * 2^(L-3) := by
        rw [show (2:Nat)^2 = 4 by decide]
        exact Nat.mul_comm _ _
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    calc
      2^(L-2) = 2^((L-3)+1) := by congr 1; omega
      _ = 2^(L-3) * 2^1 := by rw [Nat.pow_add]
      _ = 2 * 2^(L-3) := by
        rw [show (2:Nat)^1 = 2 by decide]
        exact Nat.mul_comm _ _
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

private theorem m2EvenSixGeneric_binDec_target
    (L q : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+6 < 2^L) :
    binDec L (8*q+5) =
      d0 ++ d1 ++ d0 ++ binDec (L-3) q := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    calc
      2^L = 2^((L-3)+3) := by congr 1; omega
      _ = 2^(L-3) * 2^3 := by rw [Nat.pow_add]
      _ = 8 * 2^(L-3) := by
        rw [show (2:Nat)^3 = 8 by decide]
        exact Nat.mul_comm _ _
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    calc
      2^(L-1) = 2^((L-3)+2) := by congr 1; omega
      _ = 2^(L-3) * 2^2 := by rw [Nat.pow_add]
      _ = 4 * 2^(L-3) := by
        rw [show (2:Nat)^2 = 4 by decide]
        exact Nat.mul_comm _ _
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    calc
      2^(L-2) = 2^((L-3)+1) := by congr 1; omega
      _ = 2^(L-3) * 2^1 := by rw [Nat.pow_add]
      _ = 2 * 2^(L-3) := by
        rw [show (2:Nat)^1 = 2 by decide]
        exact Nat.mul_comm _ _
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

private theorem m2EvenSixGeneric_sourceLeftFacing
    (L q a : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+6 < 2^L) :
    s1LeftFacing L (8*q+6) 2 a 0 =
      m2EvenSixGenericInputLeftFacing L q a := by
  have hbin := m2EvenSixGeneric_binDec_source L q hL hbound
  simp [s1LeftFacing,m2EvenSixGenericInputLeftFacing,
    m2EvenSixGenericInputPrefix,m2EvenSixGenericCommonTail,
    hbin,binDec_zero,d0,d1,List.append_assoc]

private theorem m2EvenSixGeneric_baseSourceLeftFacing (a : Nat) :
    s1LeftFacing 3 6 2 a 0 =
      m2EvenSixGenericInputPrefix a ++ ([true] ++ d0 ++ lh) := by
  have hbin : binDec 3 6 = d1 ++ d0 ++ d0 := by decide
  simp [s1LeftFacing,m2EvenSixGenericInputPrefix,
    hbin,binDec_zero,d0,d1,List.append_assoc]

private theorem m2EvenSixGeneric_baseCutLeftFacing (a : Nat) :
    m2EvenSixQ4LeftFacing a =
      m2EvenSixGenericTargetPrefix a ++ ([true] ++ d0 ++ lh) := by
  have hbin : binDec 3 5 = d0 ++ d1 ++ d0 := by decide
  rw [m2EvenSixQ4LeftFacing_eq_q4LeftFacing]
  simp [BB6Coverage.Agent8Q4Suffix.q4LeftFacing,m2EvenSixGenericTargetPrefix,
    hbin,d0,d1,markerWord,List.append_assoc]

private theorem m2EvenSixGeneric_targetLeftFacing
    (L q a : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+6 < 2^L) :
    BB6Coverage.Agent8Q4Suffix.q4LeftFacing L (8*q+5) a =
      m2EvenSixGenericTargetPrefix a ++
        m2EvenSixGenericCommonTail L q := by
  have hbin := m2EvenSixGeneric_binDec_target L q hL hbound
  simp [BB6Coverage.Agent8Q4Suffix.q4LeftFacing,m2EvenSixGenericTargetPrefix,
    m2EvenSixGenericCommonTail,hbin,d0,d1,markerWord,List.append_assoc]

private theorem m2EvenSixGeneric_inputPrefix_length (a : Nat) :
    (m2EvenSixGenericInputPrefix a).length = 3*a+12 := by
  simp [m2EvenSixGenericInputPrefix,d1pow_length,markerWord,d0,d1]

private theorem m2EvenSixGeneric_targetPrefix_length (a : Nat) :
    (m2EvenSixGenericTargetPrefix a).length = 3*a+12 := by
  simp [m2EvenSixGenericTargetPrefix,d1pow_length,markerWord,d0,d1]

private theorem m2EvenSixGeneric_input_matches
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+6 < 2^L) :
    ∀ x, m2EvenSixGenericInside a h x = true →
      (s1Config L (8*q+6) 2 a 0 b h).tape x =
      (s1Config 3 6 2 a 0 b h).tape x := by
  have hsourceLeft := m2EvenSixGeneric_sourceLeftFacing L q a hL hbound
  have hbaseLeft := m2EvenSixGeneric_baseSourceLeftFacing a
  have hprefixLength := m2EvenSixGeneric_inputPrefix_length a
  intro x hx
  by_cases hleft : x ≤ h
  · let i : Nat := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i:Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int) = x := by omega
    have hthreshold : h-((3*a+11:Int)) ≤ x := by
      simpa [m2EvenSixGenericInside] using hx
    have hi : i ≤ 3*a+11 := by omega
    have hiPrefix :
        i < (m2EvenSixGenericInputPrefix a).length := by
      rw [hprefixLength]
      omega
    have hsrc := s1Config_left_cell L (8*q+6) 2 a 0 b h i
    have hbase := s1Config_left_cell 3 6 2 a 0 b h i
    rw [hcoord] at hsrc hbase
    rw [hsourceLeft] at hsrc
    rw [hbaseLeft] at hbase
    change (s1Config L (8*q+6) 2 a 0 b h).tape x =
      sideBit (m2EvenSixGenericInputPrefix a ++ m2EvenSixGenericCommonTail L q) i at hsrc
    have hsrcBit := sideBit_append_left
      (m2EvenSixGenericInputPrefix a)
      (m2EvenSixGenericCommonTail L q) i hiPrefix
    have hbaseBit := sideBit_append_left
      (m2EvenSixGenericInputPrefix a)
      ([true] ++ d0 ++ lh) i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbase
    exact hsrc.trans hbase.symm
  · let i : Nat := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i:Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int) = x := by omega
    have hsrc := s1Config_right_cell L (8*q+6) 2 a 0 b h i
    have hbase := s1Config_right_cell 3 6 2 a 0 b h i
    rw [hcoord] at hsrc hbase
    exact hsrc.trans hbase.symm

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

private theorem m2EvenSixGeneric_bridge_prefix_lower
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
  have hbridgeFrame := bridgeAt T h m2EvenSixQ4Inside
    m2EvenSixQ4BridgeStart e j rfl hexact hcheckj hmatch
  have hbridge : run tm2 j ⟨3,h,T⟩ =
      some (frameAt T h m2EvenSixQ4Inside e) := by
    simpa [m2EvenSixQ4BridgeStart] using hbridgeFrame
  rw [hbridge] at hd
  have hdeq : d = frameAt T h m2EvenSixQ4Inside e :=
    (Option.some.inj hd).symm
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

private theorem m2EvenSixGeneric_E_scan_prefix_head
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
  cases heq
  rfl

private theorem m2EvenSixGeneric_q4_prefix_head_bound
    (a b : Nat) (h : Int) (ha : 0<a) :
    ∀ k, k < 44+12*a → ∀ d,
      run tm2 k (s1Config 3 6 2 a 0 b h) = some d →
      h-((3*a+11:Int)) ≤ d.head := by
  let T := (s1Config 3 6 2 a 0 b h).tape
  let N := 3*a+2
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  have hbaseConfig : s1Config 3 6 2 a 0 b h =
      (⟨3,h,T⟩ : Config) := by
    apply config_ext_by_fields
    · simp
    · simp
    · rfl
  let T2 := m2EvenSixQ4CutTape a b h
  have hface : s1LeftFacing 3 6 2 a 0 =
      d1pow a ++ (markerWord 2 ++ d0 ++ binDec 3 6 ++ lh) := by
    simp [s1LeftFacing,binDec_zero,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 6 2 a 0 b h i
    rw [hface] at hcell
    by_cases hi3 : i < 3*a
    · have hside := sideBit_append_left (d1pow a)
        (markerWord 2 ++ d0 ++ binDec 3 6 ++ lh) i
        (by rw [d1pow_length]; omega)
      rw [hside] at hcell
      exact hcell.trans (sideBit_d1pow_true a i hi3)
    · have hcases : i=3*a ∨ i=3*a+1 := by omega
      rcases hcases with hi0 | hi1
      · subst i
        have hside := sideBit_d1pow_append a (3*a)
          (markerWord 2 ++ d0 ++ binDec 3 6 ++ lh) (by omega)
        rw [hside] at hcell
        simpa [markerWord,sideBit] using hcell
      · subst i
        have hside := sideBit_d1pow_append a (3*a+1)
          (markerWord 2 ++ d0 ++ binDec 3 6 ++ lh) (by omega)
        rw [hside] at hcell
        simpa [markerWord,sideBit] using hcell
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
      apply config_ext_by_fields
      · simp [frameAt_state,m2EvenSixQ4BridgeEnd]
      · simp [frameAt_head,m2EvenSixQ4BridgeEnd]
        omega
      · rfl
    rw [hframe] at hb
    exact hb
  have hlinear : linearRightOnes T2 (hN+2) (3*a) := by
    have hcoord : hN+2 = h-(3*a:Int) := by
      dsimp [hN,N]
      omega
    rw [hcoord]
    simpa [T2] using
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
      rw [hkEq] at hd
      dsimp [p1] at hd
      rw [hbaseConfig] at hd
      rw [run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      have hlow := m2EvenSixGeneric_bridge_prefix_lower T1 hN hmatch j hj d hd
      dsimp [hN,N] at *
      omega
    · let j := k-p2
      have hj : j<3*a := by dsimp [j,p2,p1,N] at *; omega
      have hkEq : k=p1+(38+j) := by dsimp [j,p2,p1]; omega
      rw [hkEq] at hd
      dsimp [p1] at hd
      rw [hbaseConfig] at hd
      rw [run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      rw [run_add,hBridge] at hd
      simp only [Option.bind_some] at hd
      have hhead := m2EvenSixGeneric_E_scan_prefix_head
        T2 (hN+2) (3*a) hlinear j hj d hd
      dsimp [hN,N] at *
      omega

/-- Lift the base 44+12*a q4 prefix to arbitrary L>=3 and n=8*q+6. -/
theorem m2EvenSix_generic_q4_prefix_source
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+6 < 2^L) (ha : 0<a) :
    run tm2 (44+12*a)
      (s1Config L (8*q+6) 2 a 0 b h) =
      some ⟨4,h,m2EvenSixGenericCutTape L q a b h⟩ := by
  let base : Config := s1Config 3 6 2 a 0 b h
  let background := (s1Config L (8*q+6) 2 a 0 b h).tape
  have hinput := m2EvenSixGeneric_input_matches L q a b h hL hbound
  have hstart :
      frame (m2EvenSixGenericInside a h) background base =
        s1Config L (8*q+6) 2 a 0 b h := by
    apply config_ext_by_fields
    · rfl
    · rfl
    · funext x
      by_cases hx : m2EvenSixGenericInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 44+12*a → ∀ d,
        run tm2 j base = some d →
        m2EvenSixGenericInside a h d.head = true := by
    intro j hj d hd
    have hlow := m2EvenSixGeneric_q4_prefix_head_bound a b h ha j hj d hd
    simpa [m2EvenSixGenericInside] using hlow
  have hlift := run_frame tm2 (m2EvenSixGenericInside a h)
    background base (44+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (44+12*a) base =
        some (⟨4,h,m2EvenSixQ4CutTape a b h⟩ : Config) := by
    simpa [base] using
      (m2EvenSix_q4_prefix_data_exact a b h ha).1
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  simpa [m2EvenSixGenericCutTape,background,frame] using hlift

private theorem m2EvenSixGeneric_cut_eq_base_inside
    (L q a b : Nat) (h x : Int)
    (hin : m2EvenSixGenericInside a h x = true) :
    m2EvenSixGenericCutTape L q a b h x =
      m2EvenSixQ4CutTape a b h x := by
  simp [m2EvenSixGenericCutTape,frame,hin]

private theorem m2EvenSixGeneric_cut_eq_input_outside
    (L q a b : Nat) (h x : Int)
    (hout : m2EvenSixGenericInside a h x = false) :
    m2EvenSixGenericCutTape L q a b h x =
      (s1Config L (8*q+6) 2 a 0 b h).tape x := by
  simp [m2EvenSixGenericCutTape,frame,hout]

/-- Exact generic target left-facing stream at the q4 cut. -/
theorem m2EvenSix_generic_q4_prefix_leftFacing
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+6 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m2EvenSixGenericCutTape L q a b h (h-(i:Int)) =
        sideBit (BB6Coverage.Agent8Q4Suffix.q4LeftFacing L (8*q+5) a) i := by
  have hsourceLeft := m2EvenSixGeneric_sourceLeftFacing L q a hL hbound
  have hbaseCutLeft := m2EvenSixGeneric_baseCutLeftFacing a
  have htargetLeft := m2EvenSixGeneric_targetLeftFacing L q a hL hbound
  have hinputPrefixLength := m2EvenSixGeneric_inputPrefix_length a
  have htargetPrefixLength := m2EvenSixGeneric_targetPrefix_length a
  have hbaseLeft : ∀ i : Nat,
      m2EvenSixQ4CutTape a b h (h-(i:Int)) =
        sideBit (m2EvenSixQ4LeftFacing a) i :=
    (m2EvenSix_q4_prefix_data_exact a b h ha).2.1
  intro i
  by_cases hi : i ≤ 3*a+11
  · have hin :
      m2EvenSixGenericInside a h (h-(i:Int)) = true := by
      simp [m2EvenSixGenericInside]
      omega
    rw [m2EvenSixGeneric_cut_eq_base_inside L q a b h
      (h-(i:Int)) hin]
    have hbase := hbaseLeft i
    rw [hbaseCutLeft] at hbase
    have hbaseBit := sideBit_append_left
      (m2EvenSixGenericTargetPrefix a) ([true] ++ d0 ++ lh) i
      (by rw [m2EvenSixGeneric_targetPrefix_length]; omega)
    rw [hbaseBit] at hbase
    rw [htargetLeft]
    have htargetBit := sideBit_append_left
      (m2EvenSixGenericTargetPrefix a)
      (m2EvenSixGenericCommonTail L q) i
      (by rw [m2EvenSixGeneric_targetPrefix_length]; omega)
    rw [htargetBit]
    exact hbase
  · have hout :
      m2EvenSixGenericInside a h (h-(i:Int)) = false := by
      simp [m2EvenSixGenericInside]
      omega
    rw [m2EvenSixGeneric_cut_eq_input_outside L q a b h
      (h-(i:Int)) hout]
    rw [s1Config_left_cell L (8*q+6) 2 a 0 b h i]
    rw [hsourceLeft]
    rw [htargetLeft]
    have hsourceBit := sideBit_append_right
      (m2EvenSixGenericInputPrefix a)
      (m2EvenSixGenericCommonTail L q) i
      (by rw [hinputPrefixLength]; omega)
    have htargetBit := sideBit_append_right
      (m2EvenSixGenericTargetPrefix a)
      (m2EvenSixGenericCommonTail L q) i
      (by rw [htargetPrefixLength]; omega)
    change sideBit
      (m2EvenSixGenericInputPrefix a ++ m2EvenSixGenericCommonTail L q) i =
      sideBit
        (m2EvenSixGenericTargetPrefix a ++ m2EvenSixGenericCommonTail L q) i
    rw [hsourceBit,htargetBit]
    rw [hinputPrefixLength,htargetPrefixLength]

private theorem m2EvenSixGeneric_q4RightShape_congr
    (T U : Int → Bool) (h : Int) (b : Nat)
    (heq : ∀ x, h ≤ x → T x = U x)
    (hT : BB6Coverage.Agent8Q4Suffix.q4RightShape T h b) :
    BB6Coverage.Agent8Q4Suffix.q4RightShape U h b := by
  unfold BB6Coverage.Agent8Q4Suffix.q4RightShape at *
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

private theorem m2EvenSixGeneric_q4_rightFacing
    (L q a b : Nat) (h : Int) (ha : 0<a) :
    ∀ i : Nat,
      m2EvenSixGenericCutTape L q a b h (h+1+(i:Int)) =
        sideBit (BB6Coverage.Agent6Q4Prefix.q4RightFacing b) i := by
  have hbase : ∀ i : Nat,
      m2EvenSixQ4CutTape a b h (h+1+(i:Int)) =
        sideBit (BB6Coverage.Agent6Q4Prefix.q4RightFacing b) i :=
    (m2EvenSix_q4_prefix_data_exact a b h ha).2.2.2
  intro i
  have hin :
      m2EvenSixGenericInside a h (h+1+(i:Int)) = true := by
    simp [m2EvenSixGenericInside]
    omega
  rw [m2EvenSixGeneric_cut_eq_base_inside L q a b h
    (h+1+(i:Int)) hin]
  exact hbase i

private theorem m2EvenSixGeneric_q4_rightShape
    (L q a b : Nat) (h : Int) (ha : 0<a) :
    BB6Coverage.Agent8Q4Suffix.q4RightShape (m2EvenSixGenericCutTape L q a b h) h b := by
  apply m2EvenSixGeneric_q4RightShape_congr
    (m2EvenSixQ4CutTape a b h)
    (m2EvenSixGenericCutTape L q a b h) h b
  · intro x hx
    have hin : m2EvenSixGenericInside a h x = true := by
      simp [m2EvenSixGenericInside]
      omega
    symm
    exact m2EvenSixGeneric_cut_eq_base_inside L q a b h x hin
  · exact (m2EvenSix_q4_prefix_data_exact a b h ha).2.2.1

private theorem m2EvenSixGeneric_q4_far_tail
    (L q a b : Nat) (h : Int) (ha : 0<a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m2EvenSixGenericCutTape L q a b h (h+1+(i:Int)) = false := by
  intro i hi
  rw [m2EvenSixGeneric_q4_rightFacing L q a b h ha i]
  apply sideBit_ge_length
  rw [BB6Coverage.Agent6Q4Prefix.q4RightFacing_length]
  omega

private theorem m2EvenSixGeneric_resetPrefixCost
    (q a b : Nat) :
    resetPrefixCost 2 (8*q+6) a b =
      (44+12*a)+(39+3*b) := by
  have hvOdd : v2 (4*q+3) = 0 := by
    exact v2_of_odd (4*q+3) (by omega)
  have hdiv : (8*q+6)/2 = 4*q+3 := by omega
  have hvEven := v2_of_even (8*q+6) (by omega) (by omega)
  have hv : v2 (8*q+6) = 1 := by
    simpa [hdiv,hvOdd] using hvEven
  simp [resetPrefixCost,hv]
  omega

/-- Full source-level q4 reset prefix for arbitrary L>=3 and n=8*q+6. -/
theorem m2EvenSix_generic_q4_reset_prefix_source
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+6 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 2 (8*q+6) a b)
      (s1Config L (8*q+6) 2 a 0 b h) =
      some (s1Config L (8*q+5) 1 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  let Tq := m2EvenSixGenericCutTape L q a b h
  have hprefix := m2EvenSix_generic_q4_prefix_source
    L q a b h hL hbound ha
  have hleft := m2EvenSix_generic_q4_prefix_leftFacing
    L q a b h hL hbound ha
  have hshape := m2EvenSixGeneric_q4_rightShape L q a b h ha
  have htail := m2EvenSixGeneric_q4_far_tail L q a b h ha
  have happend := q4SuffixTargetLeft L (8*q+5) a b
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    L (8*q+5) 1 (a+b+2) (2^b-1)
    (BB6Coverage.Agent8Q4Suffix.q4LeftFacing L (8*q+5) a)
    hshape htail hleft happend
  have hsum := m2EvenSixGeneric_resetPrefixCost q a b
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

#print axioms m2EvenSix_generic_q4_prefix_source
#print axioms m2EvenSix_generic_q4_prefix_leftFacing
#print axioms m2EvenSix_generic_q4_reset_prefix_source

end BB6Coverage.Agent44M2EvenSixGenericSource
