import M0EvenSixQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# Head bound for the m=0,n=6 q4 prefix

Expose the half-line bound needed to lift Agent 49's base L=5,n=14
q4 prefix to arbitrary L and n=32*k+14.  The three phases are the
3a counted left sweep, the 39-step bridge with relative head window
[-9,2], and the 3(a-1) E-scan.
-/

namespace BB6Coverage.Agent42M0EvenSixHeadBound

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent42M0EvenSixQ4Bridge
open BB6Coverage.Agent42M0EvenSixQ4Prefix

set_option maxHeartbeats 3000000

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

private theorem m0EvenSix_bridge_prefix_lower
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ y, m0EvenSixInside y = true →
      T (h+y) = decide (y ∈ m0EvenSixBridgeStart.marked))
    (j : Nat) (hj : j < 39) (d : Config)
    (hd : run tm2 j ⟨3,h,T⟩ = some d) :
    h-10 ≤ d.head := by
  obtain ⟨e,hexact⟩ :=
    fRun_prefix_exists m0EvenSixBridge_exact (by omega)
  have hcheckj :
      (List.range j).all (fun k =>
        match fRun tm2 k m0EvenSixBridgeStart with
        | none => true
        | some f => m0EvenSixInside f.head) = true := by
    apply List.all_eq_true.mpr
    intro k hk
    have hk39 : k < 39 := by
      have hmem := List.mem_range.mp hk
      omega
    exact (List.all_eq_true.mp m0EvenSixBridge_heads) k
      (List.mem_range.mpr hk39)
  have hbridge := bridgeAt T h m0EvenSixInside
    m0EvenSixBridgeStart e j rfl hexact hcheckj hmatch
  rw [hbridge] at hd
  have hdeq : d = frameAt T h m0EvenSixInside e :=
    Option.some.inj hd
  have hinside : m0EvenSixInside e.head = true := by
    have hh := (List.all_eq_true.mp m0EvenSixBridge_heads) j
      (List.mem_range.mpr hj)
    simpa [hexact] using hh
  have hlow : -10 ≤ e.head := by
    simp [m0EvenSixInside] at hinside
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

private theorem m0EvenSixQ4LeftFacingPrefixTrue
    (a i : Nat) (ha : 0<a) (hi : i < 3*a) :
    sideBit (m0EvenSixQ4LeftFacing a) i = true := by
  let P : List Bool := [true] ++ d1pow (a-1) ++ [true,true]
  let R : List Bool := [false,true] ++ d0 ++ binDec 3 5 ++ lh
  have hlist : m0EvenSixQ4LeftFacing a = P ++ R := by
    simp [P,R,m0EvenSixQ4LeftFacing,markerWord,List.append_assoc]
  have hP : sideBit P i = true := by
    by_cases hi0 : i = 0
    · subst i
      simp [P,sideBit]
    · have hpos : 1 ≤ i := by omega
      rw [show P = [true] ++ (d1pow (a-1) ++ [true,true]) by rfl]
      rw [sideBit_append_right [true]
        (d1pow (a-1) ++ [true,true]) i (by simp; omega)]
      change sideBit (d1pow (a-1) ++ [true,true]) (i-1) = true
      let j := i-1
      change sideBit (d1pow (a-1) ++ [true,true]) j = true
      by_cases hj : j < 3*(a-1)
      · have hlen : (d1pow (a-1)).length = 3*(a-1) := by
          simp [d1pow_length]
        rw [sideBit_append_left (d1pow (a-1)) [true,true] j (by
          simpa [hlen] using hj)]
        exact sideBit_d1pow_true (a-1) j (by omega)
      · have hlen : (d1pow (a-1)).length = 3*(a-1) := by
          simp [d1pow_length]
        rw [sideBit_append_right (d1pow (a-1)) [true,true] j (by
          rw [hlen]
          omega)]
        rw [hlen]
        have hjCases : j-3*(a-1) = 0 ∨ j-3*(a-1) = 1 := by omega
        rcases hjCases with hj0 | hj1
        · rw [hj0]
          simp [sideBit]
        · rw [hj1]
          simp [sideBit]
  have hlen : P.length = 3*a := by
    simp [P,d1pow_length]
    omega
  rw [hlist]
  rw [sideBit_append_left P R i (by simpa [hlen] using hi)]
  exact hP

/-- Every configuration in the base q4-prefix run has its head at or
to the right of h-(3*a+10). -/
theorem m0EvenSix_q4_prefix_head_bound
    (a b : Nat) (h : Int) (ha : 0<a) :
    ∀ k, k < 36+12*a → ∀ d,
      run tm2 k ⟨3,h,(s1Config 3 6 0 a 0 b h).tape⟩ = some d →
      h-((3*a+10:Int)) ≤ d.head := by
  let T := (s1Config 3 6 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m0EvenSixQ4CutTape a b h
  have hleft :
      s1LeftFacing 3 6 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d0 ++ d0 ++ lh := by
    simp [s1LeftFacing,binDec_zero,
      m0Even_binDec_three_six,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 6 0 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 6 0 a 0) i = true := by
      rw [hleft]
      let R : List Bool := markerWord 0 ++ d0 ++ d1 ++ d0 ++ d0 ++ lh
      simp only [List.append_assoc]
      change sideBit (d1pow a ++ R) i = true
      have hiLen : i < (d1pow a).length := by
        simpa [N,d1pow_length] using hi
      rw [sideBit_append_left (d1pow a) R i hiLen]
      exact sideBit_d1pow_true a i (by simpa [N,d1pow_length] using hi)
    simpa [T,hside] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 6 0 a 0 b h 0
    simpa [T,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m0EvenSixBridge_input_match a b h ha
  have hBridge := bridgeAt T1 hN m0EvenSixInside
    m0EvenSixBridgeStart m0EvenSixBridgeEnd 39 rfl
    m0EvenSixBridge_exact m0EvenSixBridge_heads hmatch
  have hBridge' :
      run tm2 39 ⟨3,hN,T1⟩ = some ⟨4,hN+3,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m0EvenSixInside m0EvenSixBridgeEnd =
          (⟨4,hN+3,T2⟩ : Config) := by
      apply config_ext_by_fields
      · simp [frameAt_state,m0EvenSixBridgeEnd]
      · simp [frameAt_head,m0EvenSixBridgeEnd] <;> omega
      · simp [m0EvenSixQ4CutTape,T,N,T1,hN,T2]
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+3) (3*(a-1)) := by
    intro i hi
    let j : Nat := 3*a-3-i
    have hj : j < 3*a := by dsimp [j]; omega
    have hleftCut := m0EvenSix_q4_prefix_leftFacing a b h ha j
    have htrue := m0EvenSixQ4LeftFacingPrefixTrue a j ha hj
    have hval :
        m0EvenSixQ4CutTape a b h (h-(j:Int)) = true := by
      rw [hleftCut,htrue]
      rfl
    have hcoord : hN+3+(i:Int) = h-(j:Int) := by
      dsimp [hN,N,j]
      omega
    simpa [T2,hcoord] using hval
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
      have hlow := m0EvenSix_bridge_prefix_lower T1 hN hmatch j hj d hd
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

#print axioms m0EvenSix_q4_prefix_head_bound

end BB6Coverage.Agent42M0EvenSixHeadBound
