import M0OddQ4Prefix
import M0EvenSixHeadBound

/-! Sharp source head bound for the base odd marker-0 prefix. Reuse the
already checked counted-sweep head bound, and use the exact 27-step finite
bridge head window. This is the only additional ingredient needed to lift
the base odd prefix to arbitrary width. -/

namespace BB6Coverage.Agent48M0OddHeadBound
open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24M0OddQ4Bridges
open BB6Coverage.Agent24M0OddQ4Prefix
open BB6Coverage.Agent42M0EvenSixHeadBound (counted_left_sweep_heads)
set_option maxHeartbeats 3000000

private theorem binDec_three_five :
    binDec 3 5 = d0 ++ d1 ++ d0 := by
  have h1 : binDec 3 5 = d0 ++ binDec 2 2 := by
    simpa using binDec_odd 2 2 (by decide)
  have h2 : binDec 2 2 = d1 ++ binDec 1 1 := by
    simpa using binDec_even 1 1 (by decide)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private def m0OddSourceLeftSuffix : List Bool :=
  markerWord 0 ++ (d0 ++ (d0 ++ (d1 ++ (d0 ++ lh))))

private theorem m0OddQ4CutTape_eq_swept
    (a b : Nat) (h x : Int)
    (hout : m0OddQ4Bridge27Inside
      (x-(h-((3*a : Nat) : Int))) = false) :
    m0OddQ4CutTape a b h x =
      sweptLeft (3*a) (s1Config 3 5 0 a 0 b h).tape h x := by
  have hcut := frameAt_tape_outside
    (sweptLeft (3*a) (s1Config 3 5 0 a 0 b h).tape h)
    (h-((3*a : Nat):Int)) m0OddQ4Bridge27Inside
    m0OddQ4Bridge27End x hout
  simpa [m0OddQ4CutTape] using hcut

private theorem m0OddQ4CutTape_eq_end_inside
    (a b : Nat) (h x : Int)
    (hin : m0OddQ4Bridge27Inside
      (x-(h-((3*a : Nat):Int))) = true) :
    m0OddQ4CutTape a b h x =
      decide ((x-(h-((3*a : Nat):Int))) ∈
        m0OddQ4Bridge27End.marked) := by
  have hcut := frameAt_tape_inside
    (sweptLeft (3*a) (s1Config 3 5 0 a 0 b h).tape h)
    (h-((3*a : Nat):Int)) m0OddQ4Bridge27Inside
    m0OddQ4Bridge27End x hin
  simpa [m0OddQ4CutTape] using hcut

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
  cases heq
  rfl

private theorem m0Odd_bridge_prefix_lower
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ y, m0OddQ4Bridge27Inside y = true →
      T (h+y) = decide (y ∈ m0OddQ4Bridge27Start.marked))
    (j : Nat) (hj : j < 27) (d : Config)
    (hd : run tm2 j ⟨3,h,T⟩ = some d) :
    h-6 ≤ d.head := by
  obtain ⟨e,hexact⟩ :=
    fRun_prefix_exists (k := j) m0OddQ4Bridge27_exact (by omega)
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
  have hbridgeFrame := bridgeAt T h m0OddQ4Bridge27Inside
    m0OddQ4Bridge27Start e j rfl hexact hcheckj hmatch
  have hbridge : run tm2 j ⟨3,h,T⟩ =
      some (frameAt T h m0OddQ4Bridge27Inside e) := by
    simpa [m0OddQ4Bridge27Start] using hbridgeFrame
  rw [hbridge] at hd
  have hdeq : d = frameAt T h m0OddQ4Bridge27Inside e :=
    (Option.some.inj hd).symm
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

/-- Every strict prefix of the base 24+12a run stays at or right of h-(3a+6). -/
theorem m0Odd_q4_prefix_head_bound_sharp
    (a b : Nat) (h : Int) (ha : 0<a) :
    ∀ k, k < 24+12*a → ∀ d,
      run tm2 k (s1Config 3 5 0 a 0 b h) = some d →
      h-((3*a+6:Nat):Int) ≤ d.head := by
  let T := (s1Config 3 5 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m0OddQ4CutTape a b h
  have hleftFacing :
      s1LeftFacing 3 5 0 a 0 =
        d1pow a ++ m0OddSourceLeftSuffix := by
    simp [s1LeftFacing,binDec_zero,binDec_three_five,
      m0OddSourceLeftSuffix,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 5 0 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 5 0 a 0) i = true := by
      rw [hleftFacing]
      have hiLen : i < (d1pow a).length := by
        simpa [d1pow_length] using hi
      rw [Agent6Q4Prefix.sideBit_append_left (d1pow a)
        m0OddSourceLeftSuffix i hiLen]
      exact sideBit_d1pow_true a i hi
    simpa [T,hside] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 5 0 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep : run tm2 (3*N) (s1Config 3 5 0 a 0 b h) =
      some ⟨3,hN,T1⟩ := by
    exact counted_left_sweep N T h hOn hright
  have hmatch := m0OddQ4Bridge_input_match a b h ha
  have hBridge := m0OddQ4Bridge27At T1 hN hmatch
  have hBridge' :
      run tm2 27 ⟨3,hN,T1⟩ = some ⟨4,hN+3,T2⟩ := by
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
    by_cases hi0 : i = 0
    · subst i
      have hrel : x-(h-((3*a : Nat):Int)) = 3 := by
        dsimp [x,hN,N]
        omega
      have hin : m0OddQ4Bridge27Inside
          (x-(h-((3*a : Nat):Int))) = true := by
        change decide (-6 ≤ x-(h-((3*a : Nat):Int)) ∧
          x-(h-((3*a : Nat):Int)) ≤ 3) = true
        rw [hrel]
        decide
      have hcut := m0OddQ4CutTape_eq_end_inside a b h x hin
      have hmark :
          decide ((x-(h-((3*a : Nat):Int))) ∈
            m0OddQ4Bridge27End.marked) = true := by
        rw [hrel]
        simp [m0OddQ4Bridge27End]
      have hval := hcut.trans hmark
      simpa [T2,x] using hval
    · have hrel : x-(h-((3*a : Nat):Int)) = 3+(i:Int) := by
        dsimp [x,hN,N]
        omega
      have hout : m0OddQ4Bridge27Inside
          (x-(h-((3*a : Nat):Int))) = false := by
        change decide (-6 ≤ x-(h-((3*a : Nat):Int)) ∧
          x-(h-((3*a : Nat):Int)) ≤ 3) = false
        rw [hrel]
        simp [m0OddQ4Bridge27Inside]
        omega
      have hcut := m0OddQ4CutTape_eq_swept a b h x hout
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
      have hval := hcut.trans hblock'
      simpa [T2,x] using hval
  intro k hk d hd
  let p1 := 3*N
  let p2 := p1+27
  by_cases hk1 : k < p1
  · have hlow := counted_left_sweep_heads N T h hOn hright k
      hk1 d hd
    dsimp [hN,N] at hlow ⊢
    omega
  · by_cases hk2 : k < p2
    · let j := k-p1
      have hj : j<27 := by dsimp [j,p1] at *; omega
      have hkEq : k=p1+j := by dsimp [j,p1]; omega
      rw [hkEq,run_append,hSweep] at hd
      simp only [Option.bind_some] at hd
      have hlow := m0Odd_bridge_prefix_lower T1 hN hmatch j hj d hd
      dsimp [hN,N] at hlow ⊢
      omega
    · let j := k-p2
      have hj : j<3*(a-1) := by dsimp [j,p2,p1,N] at *; omega
      have hkEq : k=p1+(27+j) := by dsimp [j,p2,p1]; omega
      rw [hkEq,run_append,hSweep] at hd
      simp only [Option.bind_some] at hd
      rw [run_append,hBridge'] at hd
      simp only [Option.bind_some] at hd
      have hhead := E_scan_prefix_head T2 (hN+3) (3*(a-1)) hlinear j hj d hd
      dsimp [hN,N] at hhead ⊢
      omega

#print axioms m0Odd_q4_prefix_head_bound_sharp

end BB6Coverage.Agent48M0OddHeadBound
