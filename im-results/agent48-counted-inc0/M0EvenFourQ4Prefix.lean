import CountedReset
import CountedSweep
import ChampionRootBridge
import S1Encoder
import CountedQ4Prefix
import Q4Suffix
import M0EvenFourQ4Bridge
import Lean.Elab.Tactic.Omega

/-!
# Base m=0,n=4 even q4 source prefix

This composes the 3a-cell original-table left sweep, the 51-step
m0EvenFour bridge, and the 3(a-1)-cell E-scan. The theorem is the
L=3 base source run needed for the later arbitrary-binary-tail lift.
-/

namespace BB6Coverage.Agent48M0EvenFourQ4Prefix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6ChampionArithmetic
open BB6Coverage.Agent48M0EvenFourQ4Bridge

/-- Explicit tape at the m=0,n=4 even q4 cut. -/
def m0EvenFourQ4CutTape (a b : Nat) (h : Int) : Int → Bool :=
  let T := (s1Config 3 4 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  (frameAt T1 (h-(N:Int)) m0EvenFourInside m0EvenFourBridgeEnd).tape

/-- The fixed bridge frame agrees with the swept source tape outside
its local [-12,3] window. -/
private theorem m0EvenFourQ4CutTape_eq_swept
    (a b : Nat) (h x : Int)
    (hout : m0EvenFourInside (x-(h-((3*a : Nat) : Int))) = false) :
    m0EvenFourQ4CutTape a b h x =
      sweptLeft (3*a) (s1Config 3 4 0 a 0 b h).tape h x := by
  let T := (s1Config 3 4 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_outside T1 (h-(N:Int))
    m0EvenFourInside m0EvenFourBridgeEnd x hout
  simpa [m0EvenFourQ4CutTape,T,N,T1] using hf

private theorem m0EvenFourQ4CutTape_eq_end_inside
    (a b : Nat) (h x : Int)
    (hin : m0EvenFourInside (x-(h-((3*a : Nat) : Int))) = true) :
    m0EvenFourQ4CutTape a b h x =
      decide ((x-(h-((3*a : Nat) : Int))) ∈ m0EvenFourBridgeEnd.marked) := by
  let T := (s1Config 3 4 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  have hf := frameAt_tape_inside T1 (h-(N:Int))
    m0EvenFourInside m0EvenFourBridgeEnd x hin
  simpa [m0EvenFourQ4CutTape,T,N,T1] using hf

private theorem m0EvenFourQ4CutTape_eq_source_right
    (a b : Nat) (h x : Int) (ha : 0 < a) (hx : h+2 ≤ x) :
    m0EvenFourQ4CutTape a b h x =
      (s1Config 3 4 0 a 0 b h).tape x := by
  let T := (s1Config 3 4 0 a 0 b h).tape
  have hgt : 3 < x-(h-((3*a : Nat) : Int)) := by omega
  have hnot : ¬(-12 ≤ x-(h-((3*a : Nat) : Int)) ∧
      x-(h-((3*a : Nat) : Int)) ≤ 3) := by omega
  have hout : m0EvenFourInside
      (x-(h-((3*a : Nat) : Int))) = false := by
    change decide (-12 ≤ _ ∧ _ ≤ 3) = false
    exact decide_eq_false_iff_not.mpr hnot
  have hcut := m0EvenFourQ4CutTape_eq_swept a b h x hout
  have hpres := sweptLeft_preserves_right (3*a) T h x (by omega)
  simpa [T] using hcut.trans hpres

/-- The q4 cut follows a 3a counted sweep, the fixed 51-step bridge,
and a 3(a-1)-cell E-scan. -/
theorem m0EvenFour_q4_prefix_run
    (a b : Nat) (h : Int) (ha : 0 < a) :
    run tm2 (48+12*a)
      ⟨3,h,(s1Config 3 4 0 a 0 b h).tape⟩ =
      some ⟨4,h,m0EvenFourQ4CutTape a b h⟩ := by
  let T := (s1Config 3 4 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := (frameAt T1 hN m0EvenFourInside m0EvenFourBridgeEnd).tape
  have hleftFacing :
      s1LeftFacing 3 4 0 a 0 =
        d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh := by
    simp [s1LeftFacing,binDec_zero,m0Even_binDec_three_four,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 4 0 a 0 b h i
    have hside : sideBit (s1LeftFacing 3 4 0 a 0) i = true := by
      rw [hleftFacing]
      let R : List Bool := markerWord 0 ++ (d0 ++ (d1 ++ (d1 ++ (d0 ++ lh))))
      simp only [List.append_assoc]
      change sideBit (d1pow a ++ R) i = true
      have hiLen : i < (d1pow a).length := by
        simpa [d1pow_length] using hi
      rw [sideBit_append_left (d1pow a) R i hiLen]
      exact sideBit_d1pow_true a i (by simpa [d1pow_length] using hi)
    simpa [T,hside] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 4 0 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch := m0EvenFourBridge_input_match a b h ha
  have hBridge := bridgeAt T1 hN m0EvenFourInside
    m0EvenFourBridgeStart m0EvenFourBridgeEnd 51 rfl
    m0EvenFourBridge_exact m0EvenFourBridge_heads hmatch
  have hBridge' :
      run tm2 51 ⟨3,hN,T1⟩ = some ⟨4,hN+3,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m0EvenFourInside m0EvenFourBridgeEnd =
          (⟨4,hN+3,T2⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,m0EvenFourBridgeEnd]
      · simp [frameAt_head,m0EvenFourBridgeEnd] <;> omega
      · rfl
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+3) (3*(a-1)) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      have hcoord : (hN+3)-(h-((3*a:Nat):Int)) = 3 := by
        dsimp [hN,N]
        omega
      have hin : m0EvenFourInside ((hN+3)-(h-((3*a:Nat):Int))) = true := by
        rw [hcoord]
        decide
      have hcut := m0EvenFourQ4CutTape_eq_end_inside a b h (hN+3) hin
      have hmark :
          decide (((hN+3)-(h-((3*a:Nat):Int))) ∈ m0EvenFourBridgeEnd.marked) = true := by
        rw [hcoord]
        simp [m0EvenFourBridgeEnd]
      have htrue : m0EvenFourQ4CutTape a b h (hN+3) = true :=
        hcut.trans hmark
      simpa [m0EvenFourQ4CutTape,T,N,T1,hN,T2] using htrue
    · let x : Int := hN+3+(i:Int)
      have hgt : 3 < x-hN := by
        dsimp [x]
        omega
      have hout : m0EvenFourInside (x-hN) = false := by
        simp [m0EvenFourInside,hgt]
      have hframe : T2 x = T1 x := by
        simpa [T2] using
          frameAt_tape_outside T1 hN m0EvenFourInside m0EvenFourBridgeEnd x hout
      let j : Nat := 3*a-3-i
      have hj : j+1 < N := by
        dsimp [j,N] at *
        omega
      have hblock := sweptLeft_block N j T h hj
      have hcoord : x = h-(j:Int) := by
        dsimp [x,j,N,hN]
        omega
      have hT1 : T1 x = true := by
        change sweptLeft N T h x = true
        rw [hcoord]
        exact hblock
      simpa [x,T2] using hframe.trans hT1
  have hScan := E_scan T2 (hN+3) (3*(a-1)) hlinear
  have hhead : hN+3+3*((a-1:Nat):Int) = h := by
    dsimp [hN,N]
    omega
  have hscan :
      run tm2 (3*(a-1)) ⟨4,hN+3,T2⟩ = some ⟨4,h,T2⟩ := by
    simpa [hhead] using hScan
  have htotal : run tm2 (3*N+(51+3*(a-1))) ⟨3,h,T⟩ =
      some ⟨4,h,T2⟩ := by
    rw [run_append,hSweep]
    simp only [Option.bind_some]
    rw [run_append,hBridge']
    simp only [Option.bind_some]
    exact hscan
  have hnum : 48+12*a = 3*N+(51+3*(a-1)) := by
    dsimp [N]
    omega
  simpa [T,N,T1,hN,T2,m0EvenFourQ4CutTape,hnum] using htotal


/-- A finite run has a configuration at every earlier transition count. -/

private theorem m0EvenFour_sweptLeft_head_eq_source (q : Nat)
    (T : Int → Bool) (h : Int) :
    sweptLeft q T h (h-(q:Int)) = T (h-(q:Int)) := by
  induction q generalizing T h with
  | zero => simp [sweptLeft]
  | succ q ih =>
    have hcoord : h-(((q+1:Nat):Int)) = (h-1)-(q:Int) := by omega
    change sweptLeft q (holeThree T h) (h-1)
        (h-(((q+1:Nat):Int))) = T (h-(((q+1:Nat):Int)))
    rw [hcoord, ih (holeThree T h) (h-1)]
    have hne1 : (h-1)-(q:Int) ≠ h+1 := by omega
    have hne2 : (h-1)-(q:Int) ≠ h := by omega
    simp [holeThree,hne1,hne2]

private theorem m0EvenFour_sweptLeft_head_plus1_false (q : Nat)
    (T : Int → Bool) (h : Int) :
    sweptLeft (q+1) T h (h-(q:Int)) = false := by
  induction q generalizing T h with
  | zero =>
    simp [sweptLeft,holeThree] <;> omega
  | succ q ih =>
    have hcoord : h-(((q+1:Nat):Int)) = (h-1)-(q:Int) := by omega
    change sweptLeft (q+1) (holeThree T h) (h-1)
      (h-(((q+1:Nat):Int))) = false
    rw [hcoord]
    exact ih (holeThree T h) (h-1)

private theorem m0EvenFour_leftSweep_one (T : Int → Bool) (h : Int)
    (ht : T h = true) :
    run tm2 1 ⟨3,h,T⟩ = some ⟨1,h+1,T⟩ := by
  change rawStep tm2 ⟨3,h,T⟩ = some ⟨1,h+1,T⟩
  simp only [rawStep,readSlot,ht]
  have he : tm2 ((3:Fin 6),true) = some ⟨true,true,1⟩ := rfl
  rw [he]
  simp only [Option.map_some,applyMove]
  apply congrArg (fun f : Int → Bool => some (Config.mk 1 (h+1) f))
  funext x
  by_cases hx : x=h <;> simp [hx,ht]

private theorem m0EvenFour_leftSweep_two (T : Int → Bool) (h : Int)
    (ht : T h = true) (hr : T (h+1) = false) :
    run tm2 2 ⟨3,h,T⟩ =
      some ⟨2,h,(fun x => if x = h+1 then true else T x)⟩ := by
  rw [show 2 = 1+1 by omega,run_append,m0EvenFour_leftSweep_one T h ht]
  simp only [Option.bind_some]
  change rawStep tm2 ⟨1,h+1,T⟩ =
    some ⟨2,h,(fun x => if x = h+1 then true else T x)⟩
  simp only [rawStep,readSlot,hr]
  have he : tm2 ((1:Fin 6),false) = some ⟨true,false,2⟩ := rfl
  rw [he]
  simp only [Option.map_some,applyMove]
  have hcoord : h+1+(-1) = h := by omega
  simpa only [hcoord]

/-- Lower head bound for every prefix of the 3-cell grouped left sweep. -/
private theorem m0EvenFour_counted_left_sweep_heads
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
    rw [show Tq = sweptLeft q T h by rfl,m0EvenFour_sweptLeft_head_eq_source]
    exact hOn q hq
  have hqright : Tq (h-(q:Int)+1) = false := by
    change sweptLeft q T h (h-(q:Int)+1) = false
    by_cases hq0 : q = 0
    · rw [hq0]
      simpa [sweptLeft] using hr
    · obtain ⟨q',hq'⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      rw [hq']
      have hfalse := m0EvenFour_sweptLeft_head_plus1_false q' T h
      convert hfalse using 1 <;> omega
  have hqrun' :
      run tm2 (3*q) ⟨3,h,T⟩ =
        some ⟨3,h-(q:Int),Tq⟩ := by
    simpa [Tq] using hqrun
  rw [hkdecomp,run_add,hqrun'] at hd
  simp only [Option.bind_some] at hd
  have hrlt : r < 3 := Nat.mod_lt _ (by decide)
  have hrCases : r=0 ∨ r=1 ∨ r=2 := by omega
  rcases hrCases with hr0|hr1|hr2
  · rw [hr0] at hd
    simp [run] at hd
    subst d
    change h-(N:Int) ≤ h-(q:Int)
    omega
  · rw [hr1] at hd
    rw [m0EvenFour_leftSweep_one Tq (h-(q:Int)) hqhead] at hd
    have heq := Option.some.inj hd
    subst d
    change h-(N:Int) ≤ h-(q:Int)+1
    omega
  · rw [hr2] at hd
    rw [m0EvenFour_leftSweep_two Tq (h-(q:Int)) hqhead hqright] at hd
    have heq := Option.some.inj hd
    subst d
    change h-(N:Int) ≤ h-(q:Int)
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

/-- Any intermediate configuration in the finite bridge stays above
the lower edge h-12 of its translated frame. -/
private theorem m0EvenFour_bridge_prefix_lower
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ y, m0EvenFourInside y = true →
      T (h+y) = decide (y ∈ m0EvenFourBridgeStart.marked))
    (j : Nat) (hj : j < 51) (d : Config)
    (hd : run tm2 j ⟨3,h,T⟩ = some d) :
    h-12 ≤ d.head := by
  obtain ⟨e,hexact⟩ :=
    fRun_prefix_exists (k := j) m0EvenFourBridge_exact (by omega)
  have hcheckj :
      (List.range j).all (fun k =>
        match fRun tm2 k m0EvenFourBridgeStart with
        | none => true
        | some f => m0EvenFourInside f.head) = true := by
    apply List.all_eq_true.mpr
    intro k hk
    have hk51 : k < 51 := by
      have hmem := List.mem_range.mp hk
      omega
    exact (List.all_eq_true.mp m0EvenFourBridge_heads) k
      (List.mem_range.mpr hk51)
  have hbridgeFrame := bridgeAt T h m0EvenFourInside
    m0EvenFourBridgeStart e j rfl hexact hcheckj hmatch
  have hbridge : run tm2 j ⟨3,h,T⟩ =
      some (frameAt T h m0EvenFourInside e) := by
    simpa [m0EvenFourBridgeStart] using hbridgeFrame
  rw [hbridge] at hd
  have hdeq : d = frameAt T h m0EvenFourInside e :=
    (Option.some.inj hd).symm
  have hinside : m0EvenFourInside e.head = true := by
    have hh := (List.all_eq_true.mp m0EvenFourBridge_heads) j
      (List.mem_range.mpr hj)
    simpa [hexact] using hh
  have hlow : -12 ≤ e.head := by
    simp [m0EvenFourInside] at hinside
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
  cases heq
  rfl

/-- Every intermediate configuration of the base q4 prefix stays in
the half-line x≥h-(3a+12), so the arbitrary high-order left tail is safe
to frame when the base run is lifted to general L,k. -/
theorem m0EvenFour_q4_prefix_head_bound
    (a b : Nat) (h : Int) (ha : 0<a) :
    ∀ k, k < 48+12*a → ∀ d,
      run tm2 k (s1Config 3 4 0 a 0 b h) = some d →
      h-((3*a+12:Int)) ≤ d.head := by
  let T := (s1Config 3 4 0 a 0 b h).tape
  let N := 3*a
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m0EvenFourQ4CutTape a b h
  have hleft :
      s1LeftFacing 3 4 0 a 0 =
        d1pow a ++ (markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh) := by
    simp [s1LeftFacing,binDec_zero,m0Even_binDec_three_four,List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 4 0 a 0 b h i
    rw [hleft] at hcell
    have hbit := Agent6Q4Prefix.sideBit_append_left
      (d1pow a) (markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0 ++ lh) i
      (by rw [d1pow_length]; omega)
    rw [hbit] at hcell
    exact hcell.trans (sideBit_d1pow_true a i hi)
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 4 0 a 0 b h 0
    simpa [T,s1PhysicalRight_source,sideBit] using hc
  have hSweep := counted_left_sweep N T h hOn hright
  have hmatch :
      ∀ y, m0EvenFourInside y = true →
        T1 (hN+y) = decide (y ∈ m0EvenFourBridgeStart.marked) := by
    intro y hy
    have hm := m0EvenFourBridge_input_match a b h ha y hy
    simpa [T1,hN,N] using hm
  have hBridge := bridgeAt T1 hN m0EvenFourInside
    m0EvenFourBridgeStart m0EvenFourBridgeEnd 51 rfl
    m0EvenFourBridge_exact m0EvenFourBridge_heads hmatch
  have hBridge' :
      run tm2 51 ⟨3,hN,T1⟩ =
        some ⟨4,hN+3,T2⟩ := by
    have hframeConfig :
        frameAt T1 hN m0EvenFourInside m0EvenFourBridgeEnd =
          (⟨4,hN+3,T2⟩ : Config) := by
      apply config_ext
      · simp [frameAt_state,m0EvenFourBridgeEnd]
      · simp [frameAt_head,m0EvenFourBridgeEnd] <;> omega
      · rfl
    rw [hframeConfig] at hBridge
    exact hBridge
  have hlinear : linearRightOnes T2 (hN+3) (3*(a-1)) := by
    intro i hi
    by_cases hi0 : i=0
    · subst i
      let x : Int := hN+3
      have hrel : x-hN=3 := by dsimp [x]; omega
      have hin : m0EvenFourInside (x-hN)=true := by
        simp [m0EvenFourInside,hrel]
      have hcut := m0EvenFourQ4CutTape_eq_end_inside a b h x hin
      have hmark :
          decide ((x-hN) ∈ m0EvenFourBridgeEnd.marked) = true := by
        rw [hrel]
        simp [m0EvenFourBridgeEnd]
      simpa [T2,x,hN] using hcut.trans hmark
    · let x : Int := hN+3+(i:Int)
      have hrel : x-hN=3+(i:Int) := by dsimp [x]; omega
      have hout : m0EvenFourInside (x-hN)=false := by
        simp [m0EvenFourInside,hrel]
        omega
      have hcut := m0EvenFourQ4CutTape_eq_swept a b h x hout
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
  let p2 := p1+51
  have hSweepP1 :
      run tm2 p1 (s1Config 3 4 0 a 0 b h) =
        some ⟨3,hN,T1⟩ := by
    change run tm2 (3*N) ⟨3,h,T⟩ = some ⟨3,h-(N:Int),T1⟩
    exact hSweep
  by_cases hk1 : k < p1
  · have hkN : k < 3*N := by simpa [p1] using hk1
    have hlow := m0EvenFour_counted_left_sweep_heads N T h hOn hright k
      hkN d hd
    dsimp [hN,N] at *
    omega
  · by_cases hk2 : k < p2
    · let j := k-p1
      have hj : j<51 := by dsimp [j,p1] at *; omega
      have hkEq : k=p1+j := by dsimp [j,p1]; omega
      rw [hkEq,run_add,hSweepP1] at hd
      simp only [Option.bind_some] at hd
      have hlow := m0EvenFour_bridge_prefix_lower T1 hN hmatch j hj d hd
      dsimp [hN,N] at *
      omega
    · let j := k-p2
      have hj : j<3*(a-1) := by dsimp [j,p2,p1,N] at *; omega
      have hkEq : k=p1+(51+j) := by dsimp [j,p2,p1]; omega
      rw [hkEq,run_add,hSweepP1] at hd
      simp only [Option.bind_some] at hd
      rw [run_add,hBridge'] at hd
      simp only [Option.bind_some] at hd
      have hhead := E_scan_prefix_head T2 (hN+3) (3*(a-1)) hlinear j hj d hd
      dsimp [hN,N] at *
      omega


private theorem sideBit_false_after_length_local (xs : List Bool) (i : Nat)
    (hi : xs.length ≤ i) : sideBit xs i = false := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons a xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by
            simp only [List.length_cons] at hi
            omega
          simpa [sideBit] using ih i hi'

/-- The q4 cut has the standard right guard, unary counter, and blank tail. -/
theorem m0EvenFour_q4_prefix_rightShape (a b : Nat) (h : Int) (ha : 0 < a) :
    BB6Coverage.Agent8Q4Suffix.q4RightShape (m0EvenFourQ4CutTape a b h) h b := by
  unfold BB6Coverage.Agent8Q4Suffix.q4RightShape
  let T := (s1Config 3 4 0 a 0 b h).tape
  constructor
  · intro i hi
    have hiCases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hiCases with h0 | h1 | h2 | h3 | h4
    all_goals subst i
    · by_cases ha1 : a = 1
      · subst a
        have hc : h-(h-(3:Int)) = 3 := by omega
        have hin : m0EvenFourInside (h-(h-(3:Int))) = true := by
          rw [hc]
          decide
        have hcut := m0EvenFourQ4CutTape_eq_end_inside 1 b h h hin
        have hmark :
            decide ((h-(h-(3:Int))) ∈ m0EvenFourBridgeEnd.marked) = true := by
          rw [hc]
          simp [m0EvenFourBridgeEnd]
        simpa using hcut.trans hmark
      · have hnot : ¬(-12 ≤ h-(h-((3*a : Nat) : Int)) ∧
            h-(h-((3*a : Nat) : Int)) ≤ 3) := by omega
        have hout : m0EvenFourInside
            (h-(h-((3*a : Nat) : Int))) = false := by
          change decide (-12 ≤ _ ∧ _ ≤ 3) = false
          exact decide_eq_false_iff_not.mpr hnot
        have hcut := m0EvenFourQ4CutTape_eq_swept a b h h hout
        have hhead : sweptLeft (3*a) T h h = true := by
          have hs := sweptLeft_head (3*a-2) T h
          have hN : 3*a = (3*a-2)+2 := by omega
          rw [← hN] at hs
          exact hs
        have hhead' : sweptLeft (3*a)
            (s1Config 3 4 0 a 0 b h).tape h h = true := by
          simpa [T] using hhead
        simpa [Int.add_zero] using hcut.trans hhead'
    · have hnot : ¬(-12 ≤ (h+1)-(h-((3*a : Nat) : Int)) ∧
          (h+1)-(h-((3*a : Nat) : Int)) ≤ 3) := by omega
      have hout : m0EvenFourInside
          ((h+1)-(h-((3*a : Nat) : Int))) = false := by
        change decide (-12 ≤ _ ∧ _ ≤ 3) = false
        exact decide_eq_false_iff_not.mpr hnot
      have hcut := m0EvenFourQ4CutTape_eq_swept a b h (h+1) hout
      have hplus : sweptLeft (3*a) T h (h+1) = true := by
        have hN : 3*a-1+1 = 3*a := by omega
        simpa [T,hN] using sweptLeft_plus1 (3*a-1) T h
      simpa [T] using hcut.trans hplus
    · have hcut := m0EvenFourQ4CutTape_eq_source_right a b h (h+2) ha (by omega)
      have hsrc : T (h+2) = true := by
        have hcoord : h+1+(1:Int) = h+2 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 4 0 a 0 b h 1
      exact hcut.trans hsrc
    · have hcut := m0EvenFourQ4CutTape_eq_source_right a b h (h+3) ha (by omega)
      have hsrc : T (h+3) = true := by
        have hcoord : h+1+(2:Int) = h+3 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 4 0 a 0 b h 2
      exact hcut.trans hsrc
    · have hcut := m0EvenFourQ4CutTape_eq_source_right a b h (h+4) ha (by omega)
      have hsrc : T (h+4) = true := by
        have hcoord : h+1+(3:Int) = h+4 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 4 0 a 0 b h 3
      exact hcut.trans hsrc
  · constructor
    · have hcut := m0EvenFourQ4CutTape_eq_source_right a b h (h+5) ha (by omega)
      have hsrc : T (h+5) = false := by
        have hcoord : h+1+(4:Int) = h+5 := by omega
        simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
          s1Config_right_cell 3 4 0 a 0 b h 4
      simpa [T] using hcut.trans hsrc
    · constructor
      · have hcut := m0EvenFourQ4CutTape_eq_source_right a b h (h+6) ha (by omega)
        have hsrc : T (h+6) = false := by
          have hcoord : h+1+(5:Int) = h+6 := by omega
          simpa [T,hcoord,s1PhysicalRight_source,sideBit] using
            s1Config_right_cell 3 4 0 a 0 b h 5
        simpa [T] using hcut.trans hsrc
      · constructor
        · intro i hi
          have hcut := m0EvenFourQ4CutTape_eq_source_right a b h (h+7+(i:Int)) ha (by omega)
          have hsrc : T (h+7+(i:Int)) =
              sideBit (s0RightFacing b) (6+i) := by
            have hcoord : h+1+(6+i:Int) = h+7+(i:Int) := by omega
            simpa [T,hcoord,s1PhysicalRight_source,sideBit,s0RightFacing] using
              s1Config_right_cell 3 4 0 a 0 b h (6+i)
          have hside :
              sideBit (s0RightFacing b) (6+i) =
                sideBit (d1pow (b+1)) i := by
            rw [s0RightFacing]
            simpa using sideBit_append_right
              [false,true,true,true,false,false] (d1pow (b+1))
              (6+i) (by simp)
          have hones : sideBit (d1pow (b+1)) i = true :=
            sideBit_d1pow_true (b+1) i (by omega)
          have htarget : T (h+7+(i:Int)) = true := by
            rw [hsrc,hside,hones]
          exact hcut.trans htarget
        · intro i hi
          have hcut := m0EvenFourQ4CutTape_eq_source_right a b h
            (h+10+(3*b:Int)+(i:Int)) ha (by omega)
          have hsrc : T (h+10+(3*b:Int)+(i:Int)) =
              sideBit (s0RightFacing b) (9+3*b+i) := by
            have hcoord : h+1+((9+3*b+i:Int)) =
                h+10+(3*b:Int)+(i:Int) := by omega
            simpa [T,hcoord,s1PhysicalRight_source,sideBit,s0RightFacing] using
              s1Config_right_cell 3 4 0 a 0 b h (9+3*b+i)
          have hlen : (s0RightFacing b).length = 9+3*b := by
            simp [s0RightFacing,d1pow_length]
            omega
          have hblank : sideBit (s0RightFacing b) (9+3*b+i) = false :=
            sideBit_false_after_length_local (s0RightFacing b)
              (9+3*b+i) (by omega)
          have htarget : T (h+10+(3*b:Int)+(i:Int)) = false := by
            rw [hsrc,hblank]
          exact hcut.trans htarget

/-- The cut preserves the entire blank suffix after the finite right-facing
unary counter, not merely the five-cell q4 guard. -/
theorem m0EvenFour_q4_prefix_far_tail (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m0EvenFourQ4CutTape a b h (h+1+(i:Int)) = false := by
  intro i hi
  have hcut := m0EvenFourQ4CutTape_eq_source_right a b h
    (h+1+(i:Int)) ha (by omega)
  have hsrc :
      (s1Config 3 4 0 a 0 b h).tape (h+1+(i:Int)) =
        sideBit (s0RightFacing b) i := by
    simpa [s1PhysicalRight_source,sideBit,s0RightFacing] using
      s1Config_right_cell 3 4 0 a 0 b h i
  have hlen : (s0RightFacing b).length = 9+3*b := by
    simp [s0RightFacing,d1pow_length]
    omega
  have hblank : sideBit (s0RightFacing b) i = false :=
    sideBit_false_after_length_local (s0RightFacing b) i (by omega)
  calc
    m0EvenFourQ4CutTape a b h (h+1+(i:Int)) =
        (s1Config 3 4 0 a 0 b h).tape (h+1+(i:Int)) := hcut
    _ = sideBit (s0RightFacing b) i := hsrc
    _ = false := hblank

/-- Canonical left-facing stream at the m=0,n=4 even q4 cut. -/
def m0EvenFourQ4LeftFacing (a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ binDec 3 3 ++ lh

private theorem sideBit_append_after_local (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  exact BB6Coverage.Agent6Q4Prefix.sideBit_append_right xs ys i hi

private theorem m0EvenFourQ4LeftFacingTail (a i : Nat) (ha : 0 < a)
    (hi : 3*a+13 ≤ i) :
    sideBit (s1LeftFacing 3 4 0 a 0) i =
      sideBit (m0EvenFourQ4LeftFacing a) i := by
  let common : List Bool := [true] ++ lh
  let srcPrefix : List Bool :=
    d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d1 ++ [false,false]
  let tgtPrefix : List Bool :=
    [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ d0 ++ d0 ++ [true,true]
  have hsrc :
      s1LeftFacing 3 4 0 a 0 = srcPrefix ++ common := by
    simp [srcPrefix,common,s1LeftFacing,binDec_zero,
      m0Even_binDec_three_four,d0,d1,List.append_assoc]
  have htgt :
      m0EvenFourQ4LeftFacing a = tgtPrefix ++ common := by
    simp [tgtPrefix,common,m0EvenFourQ4LeftFacing,
      m0Even_binDec_three_three,d0,d1,List.append_assoc]
  have hs := sideBit_append_after_local srcPrefix common i (by
    simp [srcPrefix,d1pow_length,markerWord,d0,d1]
    omega)
  have ht := sideBit_append_after_local tgtPrefix common i (by
    simp [tgtPrefix,d1pow_length,markerWord,d0,d1]
    omega)
  have hlenS : srcPrefix.length = 3*a+13 := by
    simp [srcPrefix,d1pow_length,markerWord,d0,d1]
  have hlenT : tgtPrefix.length = 3*a+13 := by
    simp [tgtPrefix,d1pow_length,markerWord,d0,d1]
    omega
  rw [hsrc,htgt,hs,ht,hlenS,hlenT]

private theorem m0EvenFourQ4LeftFacingPrefixTrue (a i : Nat)
    (hi : i < 3*a) :
    sideBit (m0EvenFourQ4LeftFacing a) i = true := by
  let P : List Bool := [true] ++ d1pow (a-1) ++ [true,true]
  let R : List Bool := [false,true] ++ d0 ++ binDec 3 3 ++ lh
  have hlist : m0EvenFourQ4LeftFacing a = P ++ R := by
    simp [P,R,m0EvenFourQ4LeftFacing,markerWord,List.append_assoc]
  have hP : sideBit P i = true := by
    by_cases hi0 : i = 0
    · subst i
      simp [P,sideBit]
    · have hpos : 1 ≤ i := by omega
      rw [show P = [true] ++ (d1pow (a-1) ++ [true,true]) by rfl]
      rw [sideBit_append_after_local [true]
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
        rw [sideBit_append_after_local (d1pow (a-1)) [true,true] j (by
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

private theorem m0EvenFourQ4LeftFacingBoundaryBit (a k : Nat) (ha : 0 < a)
    (hk1 : 1 ≤ k) (hk12 : k ≤ 12) :
    sideBit (m0EvenFourQ4LeftFacing a) (3*a+k) =
      decide (-(k:Int) ∈ m0EvenFourBridgeEnd.marked) := by
  have hlist :
      m0EvenFourQ4LeftFacing a =
        ([true] ++ d1pow (a-1)) ++
          (markerWord 2 ++ d0 ++ binDec 3 3 ++ lh) := by
    simp [m0EvenFourQ4LeftFacing,List.append_assoc]
  rw [hlist]
  have hlen : ([true] ++ d1pow (a-1)).length = 3*a-2 := by
    simp [d1pow_length]
    omega
  rw [sideBit_append_after_local ([true] ++ d1pow (a-1))
    (markerWord 2 ++ d0 ++ binDec 3 3 ++ lh)
    (3*a+k) (by rw [hlen]; omega)]
  rw [hlen]
  rw [show 3*a+k-(3*a-2)=k+2 by omega]
  have hkCases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨
      k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 := by omega
  rcases hkCases with h1 | h2 | h3 | h4 | h5 | h6 |
      h7 | h8 | h9 | h10 | h11 | h12
  all_goals subst k
  all_goals simp [m0EvenFourBridgeEnd,markerWord,d0,d1,lh,sideBit,
    m0Even_binDec_three_three]

private theorem m0EvenFourQ4CutTape_eq_source_left
    (a b : Nat) (h : Int) (i : Nat) (hi : 3*a+13 ≤ i) :
    m0EvenFourQ4CutTape a b h (h-(i:Int)) =
      sideBit (s1LeftFacing 3 4 0 a 0) i := by
  let T := (s1Config 3 4 0 a 0 b h).tape
  have hnot : ¬(-12 ≤ (h-(i:Int))-(h-((3*a : Nat) : Int)) ∧
      (h-(i:Int))-(h-((3*a : Nat) : Int)) ≤ 3) := by omega
  have hout : m0EvenFourInside
      ((h-(i:Int))-(h-((3*a : Nat) : Int))) = false := by
    change decide (-12 ≤ _ ∧ _ ≤ 3) = false
    exact decide_eq_false_iff_not.mpr hnot
  have hcut := m0EvenFourQ4CutTape_eq_swept a b h (h-(i:Int)) hout
  have hpres := sweptLeft_preserves_left (3*a) T h
    (h-(i:Int)) (by omega)
  have hcell := s1Config_left_cell 3 4 0 a 0 b h i
  simpa [T] using hcut.trans (hpres.trans hcell)

/-- The q4 cut's complete left-facing stream is the canonical next
marker-2 S1 left word. -/
theorem m0EvenFour_q4_prefix_leftFacing (a b : Nat) (h : Int) (ha : 0 < a) :
    ∀ i : Nat, m0EvenFourQ4CutTape a b h (h-(i:Int)) =
      sideBit (m0EvenFourQ4LeftFacing a) i := by
  intro i
  by_cases hi0 : i=0
  · subst i
    have hshape := m0EvenFour_q4_prefix_rightShape a b h ha
    have htrue : m0EvenFourQ4CutTape a b h h = true := by
      simpa using hshape.1 0 (by omega)
    simpa [m0EvenFourQ4LeftFacing,sideBit] using htrue
  · by_cases hsmall : i < 3*a-3
    · let x : Int := h-(i:Int)
      have hout : m0EvenFourInside
          (x-(h-((3*a : Nat):Int))) = false := by
        simp [m0EvenFourInside,x]
        omega
      have hcut := m0EvenFourQ4CutTape_eq_swept a b h x hout
      have hblock := sweptLeft_block (3*a) i
        (s1Config 3 4 0 a 0 b h).tape h (by omega)
      have hblock' :
          sweptLeft (3*a) (s1Config 3 4 0 a 0 b h).tape h x = true := by
        simpa [x] using hblock
      have hval : m0EvenFourQ4CutTape a b h x = true := hcut.trans hblock'
      have htarget := m0EvenFourQ4LeftFacingPrefixTrue a i (by omega)
      simpa [x] using hval.trans htarget.symm
    · by_cases hnear : i = 3*a-3 ∨ i = 3*a-2 ∨ i = 3*a-1
      · rcases hnear with h3 | h2 | h1
        · subst i
          let x : Int := h-((3*a-3:Nat):Int)
          have hin : m0EvenFourInside (x-(h-((3*a:Nat):Int))) = true := by
            simp [m0EvenFourInside,x]
            omega
          have hcut := m0EvenFourQ4CutTape_eq_end_inside a b h x hin
          have hmark :
              decide ((x-(h-((3*a:Nat):Int))) ∈ m0EvenFourBridgeEnd.marked) = true := by
            have hc : x-(h-((3*a:Nat):Int)) = 3 := by dsimp [x]; omega
            rw [hc]
            simp [m0EvenFourBridgeEnd]
          have hval : m0EvenFourQ4CutTape a b h x = true := hcut.trans hmark
          have htarget := m0EvenFourQ4LeftFacingPrefixTrue a (3*a-3) (by omega)
          simpa [x] using hval.trans htarget.symm
        · subst i
          let x : Int := h-((3*a-2:Nat):Int)
          have hin : m0EvenFourInside (x-(h-((3*a:Nat):Int))) = true := by
            simp [m0EvenFourInside,x]
            omega
          have hcut := m0EvenFourQ4CutTape_eq_end_inside a b h x hin
          have hmark :
              decide ((x-(h-((3*a:Nat):Int))) ∈ m0EvenFourBridgeEnd.marked) = true := by
            have hc : x-(h-((3*a:Nat):Int)) = 2 := by dsimp [x]; omega
            rw [hc]
            simp [m0EvenFourBridgeEnd]
          have hval : m0EvenFourQ4CutTape a b h x = true := hcut.trans hmark
          have htarget := m0EvenFourQ4LeftFacingPrefixTrue a (3*a-2) (by omega)
          simpa [x] using hval.trans htarget.symm
        · subst i
          let x : Int := h-((3*a-1:Nat):Int)
          have hin : m0EvenFourInside (x-(h-((3*a:Nat):Int))) = true := by
            simp [m0EvenFourInside,x]
            omega
          have hcut := m0EvenFourQ4CutTape_eq_end_inside a b h x hin
          have hmark :
              decide ((x-(h-((3*a:Nat):Int))) ∈ m0EvenFourBridgeEnd.marked) = true := by
            have hc : x-(h-((3*a:Nat):Int)) = 1 := by dsimp [x]; omega
            rw [hc]
            simp [m0EvenFourBridgeEnd]
          have hval : m0EvenFourQ4CutTape a b h x = true := hcut.trans hmark
          have htarget := m0EvenFourQ4LeftFacingPrefixTrue a (3*a-1) (by omega)
          simpa [x] using hval.trans htarget.symm
      · by_cases hieq : i = 3*a
        · subst i
          let x : Int := h-((3*a:Int))
          have hin : m0EvenFourInside (x-(h-((3*a:Nat):Int))) = true := by
            simp [m0EvenFourInside,x]
          have hcut := m0EvenFourQ4CutTape_eq_end_inside a b h x hin
          have hmark :
              decide ((x-(h-((3*a:Nat):Int))) ∈ m0EvenFourBridgeEnd.marked) = false := by
            have hc : x-(h-((3*a:Nat):Int)) = 0 := by dsimp [x]; omega
            rw [hc]
            simp [m0EvenFourBridgeEnd]
          have htarget :
              sideBit (m0EvenFourQ4LeftFacing a) (3*a) = false := by
            have hlist :
                m0EvenFourQ4LeftFacing a =
                  ([true] ++ d1pow (a-1)) ++
                    (markerWord 2 ++ d0 ++ binDec 3 3 ++ lh) := by
              simp [m0EvenFourQ4LeftFacing,List.append_assoc]
            rw [hlist]
            have hlen : ([true] ++ d1pow (a-1)).length = 3*a-2 := by
              simp [d1pow_length]
              omega
            rw [sideBit_append_after_local ([true] ++ d1pow (a-1))
              (markerWord 2 ++ d0 ++ binDec 3 3 ++ lh) (3*a)
              (by rw [hlen]; omega)]
            rw [hlen]
            rw [show 3*a-(3*a-2)=2 by omega]
            simp [markerWord,sideBit]
          have hval : m0EvenFourQ4CutTape a b h x = false := hcut.trans hmark
          simpa [x] using hval.trans htarget.symm
        · by_cases hbound : i ≤ 3*a+12
          · let k : Nat := i-3*a
            have hk1 : 1 ≤ k := by dsimp [k]; omega
            have hk12 : k ≤ 12 := by dsimp [k]; omega
            let x : Int := h-(i:Int)
            have hrel : x-(h-((3*a:Nat):Int)) = -(k:Int) := by
              dsimp [x,k]
              omega
            have hin : m0EvenFourInside (-(k:Int)) = true := by
              simp [m0EvenFourInside]
              omega
            have hin' : m0EvenFourInside
                (x-(h-((3*a:Nat):Int))) = true := by
              rw [hrel]
              exact hin
            have hcut := m0EvenFourQ4CutTape_eq_end_inside a b h x hin'
            have hi : i=3*a+k := by dsimp [k]; omega
            have htarget := m0EvenFourQ4LeftFacingBoundaryBit a k ha hk1 hk12
            have htarget' :
                sideBit (m0EvenFourQ4LeftFacing a) i =
                  decide (-(k:Int) ∈ m0EvenFourBridgeEnd.marked) := by
              rw [hi]
              exact htarget
            have hmark' : decide
                ((x-(h-((3*a:Nat):Int))) ∈ m0EvenFourBridgeEnd.marked) =
                  decide (-(k:Int) ∈ m0EvenFourBridgeEnd.marked) := by
              rw [hrel]
            have hval :
                m0EvenFourQ4CutTape a b h x =
                  sideBit (m0EvenFourQ4LeftFacing a) i := by
              calc
                m0EvenFourQ4CutTape a b h x =
                    decide ((x-(h-((3*a:Nat):Int))) ∈
                      m0EvenFourBridgeEnd.marked) := hcut
                _ = decide (-(k:Int) ∈ m0EvenFourBridgeEnd.marked) := hmark'
                _ = sideBit (m0EvenFourQ4LeftFacing a) i := htarget'.symm
            exact hval
          · have htail := m0EvenFourQ4CutTape_eq_source_left a b h i (by omega)
            have hbits := m0EvenFourQ4LeftFacingTail a i ha (by omega)
            exact htail.trans hbits

/-- The q4 suffix's d0-sweep reconstructs the next marker-2 left word. -/
theorem m0EvenFourQ4SuffixTargetLeft (a b : Nat) (ha : 0 < a) :
    s1LeftFacing 3 3 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++ (m0EvenFourQ4LeftFacing a).drop 1 := by
  unfold s1LeftFacing m0EvenFourQ4LeftFacing
  have hbin : binDec (a+b+1) (2^b-1) =
      d0pow b ++ d1pow (a+1) := by
    have h := binDec_pow2_sub_one (a-1) b
    have hlen : (a-1)+b+2 = a+b+1 := by omega
    have hval : (a-1)+2 = a+1 := by omega
    simpa [hlen,hval] using h
  rw [hbin]
  have hadd : d1pow (a+1) = d1pow 2 ++ d1pow (a-1) := by
    have h := d1pow_add_right (a-1) 2
    have hval : (a-1)+2 = a+1 := by omega
    simpa [hval] using h
  rw [hadd]
  simp [List.drop,List.append_assoc]

theorem m0EvenFour_resetPrefixCost_eq (a b : Nat) :
    resetPrefixCost 0 4 a b = 87+12*a+3*b := by
  simp [resetPrefixCost,BB6ChampionArithmetic.v2]
  omega

#print axioms m0EvenFour_q4_prefix_run
#print axioms m0EvenFour_q4_prefix_head_bound
#print axioms m0EvenFour_q4_prefix_rightShape
#print axioms m0EvenFour_q4_prefix_far_tail
#print axioms m0EvenFour_q4_prefix_leftFacing
#print axioms m0EvenFourQ4SuffixTargetLeft
#print axioms m0EvenFour_resetPrefixCost_eq

end BB6Coverage.Agent48M0EvenFourQ4Prefix
