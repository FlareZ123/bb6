import M1OneQ4Prefix
import M0EvenSixHeadBound
import Lean.Elab.Tactic.Omega

/-!
# Half-line head bound for the fixed m=1,n=1 q4 prefix

This derives the one-sided head bound needed to lift the existing fixed
n=1 q4 prefix at L=3 to arbitrary n=8*q+1.  It reuses the existing
29-step bridge and its narrower read window [-7,4].
-/

namespace BB6Coverage.Agent48M1OddResidueOneHeadBound

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent42M0EvenSixHeadBound
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent24M1OddQ4Prefix
open BB6Coverage.Agent48FinalRst1
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

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

private theorem m1One_bridge_prefix_lower
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ y, m1OneQ4Inside y = true →
      T (h+y) = decide (y ∈ m1OddQ4BridgeStart.marked))
    (j : Nat) (hj : j < 29) (d : Config)
    (hd : run tm2 j ⟨3,h,T⟩ = some d) :
    h-7 ≤ d.head := by
  obtain ⟨e,hexact⟩ :=
    fRun_prefix_exists (k := j) m1OddQ4Bridge_exact (by omega)
  have hcheckj :
      (List.range j).all (fun k =>
        match fRun tm2 k m1OddQ4BridgeStart with
        | none => true
        | some f => m1OneQ4Inside f.head) = true := by
    apply List.all_eq_true.mpr
    intro k hk
    have hk29 : k < 29 := by
      have hmem := List.mem_range.mp hk
      omega
    exact (List.all_eq_true.mp m1OneQ4Bridge_heads) k
      (List.mem_range.mpr hk29)
  have hbridge := bridgeAt T h m1OneQ4Inside
    m1OddQ4BridgeStart e j rfl hexact hcheckj hmatch
  have hbridge' :
      run tm2 j ⟨3,h,T⟩ = some (frameAt T h m1OneQ4Inside e) := by
    simpa [m1OddQ4BridgeStart] using hbridge
  rw [hbridge'] at hd
  have hdeq : frameAt T h m1OneQ4Inside e = d :=
    Option.some.inj hd
  have hinside : m1OneQ4Inside e.head = true := by
    have hh := (List.all_eq_true.mp m1OneQ4Bridge_heads) j
      (List.mem_range.mpr hj)
    simpa [hexact] using hh
  have hlow : -7 ≤ e.head := by
    simp [m1OneQ4Inside] at hinside
    omega
  rw [← hdeq]
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
  have heqHead : h + (j:Int) = d.head := by
    simpa using congrArg (fun c : Config => c.head) (Option.some.inj hd)
  omega

/-- Every head in the 32+12*a fixed n=1 q4 prefix is at least
h-(3*a+1)-7. -/
theorem m1OddResidueOne_q4_prefix_head_bound
    (a b : Nat) (h : Int) :
    ∀ k, k < 32+12*a → ∀ d,
      run tm2 k (s1Config 3 1 1 a 0 b h) = some d →
      h-((3*a+1:Int))-7 ≤ d.head := by
  let T := (s1Config 3 1 1 a 0 b h).tape
  let N := 3*a+1
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m1OneQ4CutTape 3 a b h
  have hbin : binDec 3 1 = d0 ++ d1 ++ d1 := by decide
  have hbaseInputLeft :
      s1LeftFacing 3 1 1 a 0 =
        (d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ d1 ++ d1) ++ lh := by
    simp [s1LeftFacing,binDec_zero,hbin,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 1 1 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 1 1 a 0) i = true := by
      rw [hbaseInputLeft]
      by_cases hi3 : i < 3*a
      · have hbit := sideBit_append_left (d1pow a)
          (markerWord 1 ++ d0 ++ d0 ++ d1 ++ d1 ++ lh) i
          (by simpa [d1pow_length] using hi3)
        have hbit' :
            sideBit (d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ d1 ++ d1 ++ lh) i =
              sideBit (d1pow a) i := by
          simpa [List.append_assoc] using hbit
        rw [hbit']
        exact sideBit_d1pow_true a i hi3
      · have hieq : i = 3*a := by omega
        subst i
        have hbit := sideBit_append_right (d1pow a)
          (markerWord 1 ++ d0 ++ d0 ++ d1 ++ d1 ++ lh) (3*a)
          (by simp [d1pow_length])
        have hbit' :
            sideBit (d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ d1 ++ d1 ++ lh) (3*a) =
              sideBit (markerWord 1 ++ d0 ++ d0 ++ d1 ++ d1 ++ lh) 0 := by
          simpa [List.append_assoc,d1pow_length] using hbit
        rw [hbit']
        simp [markerWord,sideBit]
    rw [hside] at hcell
    exact hcell
  have hright : T (h+1) = false := by
    simpa [T,s1PhysicalRight_source,sideBit] using
      s1Config_right_cell 3 1 1 a 0 b h 0
  have hSweep := counted_left_sweep N T h hOn hright
  have hSweep' :
      run tm2 (3*N) (s1Config 3 1 1 a 0 b h) =
        some (⟨3,hN,T1⟩ : Config) := by
    change run tm2 (3*N) (⟨3,h,T⟩ : Config) =
      some (⟨3,hN,T1⟩ : Config)
    exact hSweep
  have hmatch0 := m1OneQ4Bridge_input_match 3 a b h (by omega)
  have hmatch : ∀ y, m1OneQ4Inside y = true →
      T1 (hN+y) = decide (y ∈ m1OddQ4BridgeStart.marked) := by
    simpa [T1,hN,N,T] using hmatch0
  have hBridge := bridgeAt T1 hN m1OneQ4Inside
    m1OddQ4BridgeStart m1OddQ4BridgeEnd 29 rfl
    m1OddQ4Bridge_exact m1OneQ4Bridge_heads hmatch
  have hBridge0 :
      run tm2 29 ⟨3,hN,T1⟩ =
        some (frameAt T1 hN m1OneQ4Inside m1OddQ4BridgeEnd) := by
    simpa [m1OddQ4BridgeStart] using hBridge
  have hframeConfig :
      frameAt T1 hN m1OneQ4Inside m1OddQ4BridgeEnd =
        (⟨4,hN+5,T2⟩ : Config) := by
    apply config_ext
    · simp [frameAt_state,m1OddQ4BridgeEnd]
    · simp [frameAt_head,m1OddQ4BridgeEnd] <;> omega
    · rfl
  rw [hframeConfig] at hBridge0
  have hBridge' :
      run tm2 29 ⟨3,hN,T1⟩ = some ⟨4,hN+5,T2⟩ := hBridge0
  have hlinear : linearRightOnes T2 (hN+5) (3*a) := by
    intro i hi
    let x := hN+5+(i:Int)
    have houtside : m1OneQ4Inside (x-hN) = false := by
      simp [m1OneQ4Inside,x]
      omega
    have hframe : T2 x = T1 x := by
      change (frameAt T1 hN m1OneQ4Inside m1OddQ4BridgeEnd).tape x = T1 x
      exact frameAt_tape_outside T1 hN m1OneQ4Inside
        m1OddQ4BridgeEnd x houtside
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
        change sweptLeft N T h x = true
        rw [hcoord]
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
            have hcoord : h+1+1 = h+2 := by omega
            simpa [T,hcoord,s0RightFacing,s1PhysicalRight_source,sideBit] using
              s1Config_right_cell 3 1 1 a 0 b h 1
          change sweptLeft N T h (h+2) = true
          rw [hp,hsrc]
        · rw [hx3]
          have hp := sweptLeft_preserves_right N T h (h+3) (by omega)
          have hsrc : T (h+3) = true := by
            have hcoord : h+1+2 = h+3 := by omega
            simpa [T,hcoord,s0RightFacing,s1PhysicalRight_source,sideBit] using
              s1Config_right_cell 3 1 1 a 0 b h 2
          change sweptLeft N T h (h+3) = true
          rw [hp,hsrc]
    simpa [x,T2] using hframe.trans hT1
  intro k hk d hd
  let p1 := 3*N
  let p2 := p1+29
  by_cases hk1 : k < p1
  · have hd' : run tm2 k ⟨3,h,T⟩ = some d := by
      simpa [s1Config,s0Config,T] using hd
    have hlow :=
      BB6Coverage.Agent42M0EvenSixHeadBound.counted_left_sweep_heads
        N T h hOn hright k
        (by dsimp [p1,N] at *; omega) d hd'
    dsimp [hN,N] at *
    omega
  · by_cases hk2 : k < p2
    · let j := k-p1
      have hj : j < 29 := by dsimp [j,p1] at *; omega
      have hkEq : k = p1+j := by dsimp [j,p1]; omega
      rw [hkEq,run_add,hSweep'] at hd
      simp only [Option.bind_some] at hd
      have hlow := m1One_bridge_prefix_lower T1 hN hmatch j hj d hd
      dsimp [hN,N] at *
      omega
    · let j := k-p2
      have hj : j < 3*a := by dsimp [j,p2,p1,N] at *; omega
      have hkEq : k = p1+(29+j) := by dsimp [j,p2,p1]; omega
      rw [hkEq,run_add,hSweep'] at hd
      simp only [Option.bind_some] at hd
      rw [run_add,hBridge'] at hd
      simp only [Option.bind_some] at hd
      have hhead := E_scan_prefix_head T2 (hN+5) (3*a) hlinear j hj d hd
      dsimp [hN,N] at *
      omega

#print axioms m1OddResidueOne_q4_prefix_head_bound

end BB6Coverage.Agent48M1OddResidueOneHeadBound
