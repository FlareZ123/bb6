import M2EvenQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# Uniform m=2, n = 4 (mod 8) source increment

The existing 50-step m=2,n=4 q4 bridge is local: it reads only the first
3*a+15 cells of the S1 left stream.  Since every n=8*k+4 has the same
low-three-bit input word, the bridge can be framed against an arbitrary
higher-order binary tail.  The output tail is preserved, and the generic
q4 suffix plus the source counted drain gives the full original-TM2
increment for every admissible n=8*k+4.

This is an intermediate source theorem, not a complete TM63 itinerary.
-/

namespace BB6Coverage.Agent48M2EvenResidueFour

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent42M2EvenQ4
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

/-- Low-three-bit decomposition for every admissible n=8*k+4. -/
theorem binDec_residue4 (L k : Nat) (hL : 3 ≤ L)
    (hbound : 8*k+4 < 2^L) :
    binDec L (8*k+4) = d1 ++ d1 ++ d0 ++ binDec (L-3) k := by
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
    rw [show L-2 = (L-3)+1 by omega,
      show 2*k = 2*k by omega]
    exact binDec_even (L-3) k hk
  rw [h1,h2,h3]
  simp [List.append_assoc]

private theorem binDec_three_four :
    binDec 3 4 = d1 ++ d1 ++ d0 := by
  have h1 : binDec 3 4 = d1 ++ binDec 2 2 := by
    simpa using binDec_even 2 2 (by decide)
  have h2 : binDec 2 2 = d1 ++ binDec 1 1 := by
    simpa using binDec_even 1 1 (by decide)
  have h3 : binDec 1 1 = d0 ++ binDec 0 0 := by
    simpa using binDec_odd 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private theorem binDec_three_three :
    binDec 3 3 = d0 ++ d0 ++ d1 := by
  have h1 : binDec 3 3 = d0 ++ binDec 2 1 := by
    simpa using binDec_odd 2 1 (by decide)
  have h2 : binDec 2 1 = d0 ++ binDec 1 0 := by
    simpa using binDec_odd 1 0 (by decide)
  have h3 : binDec 1 0 = d1 ++ binDec 0 0 := by
    simpa using binDec_even 0 0 (by decide)
  simp [h1,h2,h3,binDec_zero,d1pow]

private def m2EvenResidueFourInputPrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 2 ++ d0 ++ d1 ++ d1 ++ d0

private def m2EvenResidueFourTargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ d0 ++ d1

private theorem m2EvenResidueFourInputPrefix_length (a : Nat) :
    (m2EvenResidueFourInputPrefix a).length = 3*a+15 := by
  simp [m2EvenResidueFourInputPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m2EvenResidueFourTargetPrefix_length (a : Nat) :
    (m2EvenResidueFourTargetPrefix a).length = 3*a+15 := by
  simp [m2EvenResidueFourTargetPrefix,d1pow_length,markerWord,d0,d1]
  omega

private theorem m2EvenResidueFour_source_base_left (a : Nat) :
    s1LeftFacing 3 4 2 a 0 =
      m2EvenResidueFourInputPrefix a ++ lh := by
  simp [s1LeftFacing,m2EvenResidueFourInputPrefix,
    binDec_three_four,List.append_assoc]

private theorem m2EvenResidueFour_target_base_left (a : Nat) :
    q4LeftFacing 3 3 a =
      m2EvenResidueFourTargetPrefix a ++ lh := by
  simp [q4LeftFacing,m2EvenResidueFourTargetPrefix,
    binDec_three_three,List.append_assoc]

private theorem m2EvenResidueFour_source_left
    (L k a : Nat) (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) :
    s1LeftFacing L (8*k+4) 2 a 0 =
      m2EvenResidueFourInputPrefix a ++
        (binDec (L-3) k ++ lh) := by
  simp [s1LeftFacing,m2EvenResidueFourInputPrefix,
    binDec_residue4 L k hL hbound,List.append_assoc]

private theorem m2EvenResidueFour_target_left
    (L k a : Nat) (hL : 3 ≤ L) (hbound : 8*k+3 < 2^L) :
    q4LeftFacing L (8*k+3) a =
      m2EvenResidueFourTargetPrefix a ++
        (binDec (L-3) k ++ lh) := by
  simp [q4LeftFacing,m2EvenResidueFourTargetPrefix,
    binDec_residue3 L k hL hbound,List.append_assoc]

private theorem m2EvenResidueFour_config_ext (c d : Config)
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

private theorem m2Even_bridge_prefix_lower
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ y, m2EvenQ4Inside y = true →
      T (h+y) = decide (y ∈ m2EvenQ4BridgeStart.marked))
    (j : Nat) (hj : j < 50) (d : Config)
    (hd : run tm2 j ⟨3,h,T⟩ = some d) :
    h-12 ≤ d.head := by
  obtain ⟨e,hexact⟩ :=
    fRun_prefix_exists m2EvenQ4Bridge_exact (by omega)
  have hcheckj :
      (List.range j).all (fun k =>
        match fRun tm2 k m2EvenQ4BridgeStart with
        | none => true
        | some f => m2EvenQ4Inside f.head) = true := by
    apply List.all_eq_true.mpr
    intro k hk
    have hk50 : k < 50 := by
      have hmem := List.mem_range.mp hk
      omega
    exact (List.all_eq_true.mp m2EvenQ4Bridge_heads) k
      (List.mem_range.mpr hk50)
  have hbridge := bridgeAt T h m2EvenQ4Inside
    m2EvenQ4BridgeStart e j rfl hexact hcheckj hmatch
  rw [hbridge] at hd
  have hdeq : d = frameAt T h m2EvenQ4Inside e :=
    Option.some.inj hd
  have hinside : m2EvenQ4Inside e.head = true := by
    have hh := (List.all_eq_true.mp m2EvenQ4Bridge_heads) j
      (List.mem_range.mpr hj)
    simpa [hexact] using hh
  have hlow : -12 ≤ e.head := by
    simp [m2EvenQ4Inside] at hinside
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

/-- Every prefix of the base n=4 source bridge stays above its leftmost
readable cell h-(3*a+2)-12. -/
private theorem m2Even_q4_prefix_head_bound
    (a b : Nat) (h : Int) :
    ∀ k, k < 56+12*a → ∀ d,
      run tm2 k (s1Config 3 4 2 a 0 b h) = some d →
      h-((3*a+2:Int))-12 ≤ d.head := by
  let T := (s1Config 3 4 2 a 0 b h).tape
  let N := 3*a+2
  let T1 := sweptLeft N T h
  let hN : Int := h-(N:Int)
  let T2 := m2EvenQ4CutTape a b h
  have hface : s1LeftFacing 3 4 2 a 0 =
      d1pow a ++ (markerWord 2 ++
        (d0 ++ (d1 ++ (d1 ++ (d0 ++ lh))))) := by
    simp [s1LeftFacing,binDec_zero,binDec_three_four,
      List.append_assoc]
  have hOn : leftOnes T h N := by
    intro i hi
    have hcell := s1Config_left_cell 3 4 2 a 0 b h i
    rw [hface] at hcell
    by_cases hi3 : i < 3*a
    · have hbit := sideBit_append_left (d1pow a)
        (markerWord 2 ++ (d0 ++ (d1 ++ (d1 ++ (d0 ++ lh)))))
        i (by rw [d1pow_length]; omega)
      rw [hbit] at hcell
      exact hcell.trans (sideBit_d1pow_true a i hi3)
    · have hcases : i=3*a ∨ i=3*a+1 := by omega
      rcases hcases with hi0|hi1
      · subst i
        have hbit := sideBit_append_right (d1pow a)
          (markerWord 2 ++ (d0 ++ (d1 ++ (d1 ++ (d0 ++ lh)))))
          (3*a) (by rw [d1pow_length])
        rw [hbit] at hcell
        simpa [markerWord,sideBit] using hcell
      · subst i
        have hbit := sideBit_append_right (d1pow a)
          (markerWord 2 ++ (d0 ++ (d1 ++ (d1 ++ (d0 ++ lh)))))
          (3*a+1) (by rw [d1pow_length])
        rw [hbit] at hcell
        simpa [markerWord,sideBit] using hcell
  have hright : T (h+1) = false := by
    have hc := s1Config_right_cell 3 4 2 a 0 b h 0
    simpa [T,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hc
  have hSweep :
      run tm2 (3*N) ⟨3,h,T⟩ =
        some ⟨3,h-(N:Int),T1⟩ := by
    simpa [T1] using counted_left_sweep N T h hOn hright
  have hmatch := m2EvenQ4Bridge_input_match a b h
  have hBridge :
      run tm2 50 ⟨3,hN,T1⟩ =
        some ⟨4,hN+2,T2⟩ := by
    have hb := bridgeAt T1 hN m2EvenQ4Inside
      m2EvenQ4BridgeStart m2EvenQ4BridgeEnd 50 rfl
      m2EvenQ4Bridge_exact m2EvenQ4Bridge_heads hmatch
    have hframe :
        frameAt T1 hN m2EvenQ4Inside m2EvenQ4BridgeEnd =
          (⟨4,hN+2,T2⟩ : Config) := by
      apply m2EvenResidueFour_config_ext
      · simp [frameAt_state,m2EvenQ4BridgeEnd]
      · simp [frameAt_head,m2EvenQ4BridgeEnd]
      · rfl
    rw [hframe] at hb
    exact hb
  have hlinear : linearRightOnes T2 (hN+2) (3*a) := by
    intro i hi
    let x : Int := hN+2+(i:Int)
    by_cases hi0 : i=0
    · subst i
      have hrel : x-hN=2 := by dsimp [x]; omega
      have hin : m2EvenQ4Inside (x-hN)=true := by
        simp [m2EvenQ4Inside,hrel]
      have hframe := frameAt_tape_inside T1 hN
        m2EvenQ4Inside m2EvenQ4BridgeEnd x hin
      have hmark :
          decide (x-hN ∈ m2EvenQ4BridgeEnd.marked)=true := by
        rw [hrel]
        simp [m2EvenQ4BridgeEnd]
      simpa [T2,x] using hframe.trans hmark
    · have hrel : x-hN=2+(i:Int) := by dsimp [x]; omega
      have hout : m2EvenQ4Inside (x-hN)=false := by
        simp [m2EvenQ4Inside,hrel]
        omega
      have hframe := frameAt_tape_outside T1 hN
        m2EvenQ4Inside m2EvenQ4BridgeEnd x hout
      have hcoord : x = h-((3*a-i : Nat) : Int) := by
        dsimp [x,hN,N]
        omega
      have hj : (3*a-i)+1 < N := by dsimp [N]; omega
      have hblock := sweptLeft_block N (3*a-i) T h hj
      calc
        T2 x = T1 x := by simpa [T2] using hframe
        _ = true := by rw [hcoord]; exact hblock
  intro k hk d hd
  let p1 := 3*N
  let p2 := p1+50
  by_cases hk1 : k < p1
  · have hlow := counted_left_sweep_heads N T h hOn hright k
      (by dsimp [p1] at *; omega) d hd
    dsimp [hN,N] at *
    omega
  · by_cases hk2 : k < p2
    · let j := k-p1
      have hj : j<50 := by dsimp [j,p1] at *; omega
      have hkEq : k=p1+j := by dsimp [j,p1]; omega
      rw [hkEq,run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      have hlow := m2Even_bridge_prefix_lower T1 hN hmatch j hj d hd
      dsimp [hN,N] at *
      omega
    · let j := k-p2
      have hj : j<3*a := by dsimp [j,p2,p1,N] at *; omega
      have hkEq : k=p1+(50+j) := by dsimp [j,p2,p1]; omega
      rw [hkEq,run_add,hSweep] at hd
      simp only [Option.bind_some] at hd
      rw [run_add,hBridge] at hd
      simp only [Option.bind_some] at hd
      have hhead := E_scan_prefix_head T2 (hN+2) (3*a) hlinear j hj d hd
      dsimp [hN,N] at *
      omega

/-- The generalized frame changes only the common low-order half-line. -/
def m2EvenResidueFourInside (a : Nat) (h : Int) : Int → Bool :=
  fun x => decide (h-((3*a+2:Int))-12 ≤ x)

def m2EvenResidueFourCutTape
    (L k a b : Nat) (h : Int) : Int → Bool :=
  (frame (m2EvenResidueFourInside a h)
    (s1Config L (8*k+4) 2 a 0 b h).tape
    (⟨4,h,m2EvenQ4CutTape a b h⟩ : Config)).tape

private theorem m2EvenResidueFour_input_matches
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) :
    ∀ x, m2EvenResidueFourInside a h x = true →
      (s1Config L (8*k+4) 2 a 0 b h).tape x =
      (s1Config 3 4 2 a 0 b h).tape x := by
  have hbin4 := binDec_residue4 L k hL hbound
  have hsourceLeft :=
    m2EvenResidueFour_source_left L k a hL hbound
  have hbaseLeft := m2EvenResidueFour_source_base_left a
  have hprefixLength := m2EvenResidueFourInputPrefix_length a
  intro x hx
  by_cases hleft : x ≤ h
  · let i := Int.toNat (h-x)
    have hnonneg : 0 ≤ h-x := by omega
    have hcast : (i:Int) = h-x := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h-(i:Int)=x := by omega
    have hthreshold :
        h-((3*a+2:Int))-12 ≤ x := by
      simpa [m2EvenResidueFourInside] using hx
    have hi : i ≤ 3*a+14 := by dsimp [i] at *; omega
    have hiPrefix :
        i < (m2EvenResidueFourInputPrefix a).length := by
      rw [hprefixLength]
      omega
    have hsrc := s1Config_left_cell L (8*k+4) 2 a 0 b h i
    have hbase := s1Config_left_cell 3 4 2 a 0 b h i
    rw [hcoord] at hsrc hbase
    rw [hsourceLeft] at hsrc
    rw [hbaseLeft] at hbase
    have hsrcBit := sideBit_append_left
      (m2EvenResidueFourInputPrefix a) (binDec (L-3) k ++ lh)
      i hiPrefix
    have hbaseBit := sideBit_append_left
      (m2EvenResidueFourInputPrefix a) lh i hiPrefix
    rw [hsrcBit] at hsrc
    rw [hbaseBit] at hbase
    exact hsrc.trans hbase.symm
  · let i := Int.toNat (x-h-1)
    have hnonneg : 0 ≤ x-h-1 := by omega
    have hcast : (i:Int) = x-h-1 := by
      dsimp [i]
      exact Int.toNat_of_nonneg hnonneg
    have hcoord : h+1+(i:Int)=x := by omega
    have hsrc := s1Config_right_cell L (8*k+4) 2 a 0 b h i
    have hbase := s1Config_right_cell 3 4 2 a 0 b h i
    rw [hcoord] at hsrc hbase
    exact hsrc.trans hbase.symm

private theorem m2EvenResidueFour_cut_eq_base
    (L k a b : Nat) (h x : Int) (hx : h ≤ x) :
    m2EvenResidueFourCutTape L k a b h x =
      m2EvenQ4CutTape a b h x := by
  have hin : m2EvenResidueFourInside a h x = true := by
    simp [m2EvenResidueFourInside]
    omega
  simp [m2EvenResidueFourCutTape,frame,hin]

private theorem m2EvenResidueFour_cut_eq_input
    (L k a b : Nat) (h x : Int)
    (hout : m2EvenResidueFourInside a h x = false) :
    m2EvenResidueFourCutTape L k a b h x =
      (s1Config L (8*k+4) 2 a 0 b h).tape x := by
  simp [m2EvenResidueFourCutTape,frame,hout]

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

/-- Exact q4 left-facing word after the generalized n=8*k+4 bridge. -/
def m2EvenResidueFourLeftFacing (L k a : Nat) : List Bool :=
  q4LeftFacing L (8*k+3) a

private theorem m2EvenResidueFour_leftFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m2EvenResidueFourCutTape L k a b h (h-(i:Int)) =
        sideBit (m2EvenResidueFourLeftFacing L k a) i := by
  have hbound3 : 8*k+3 < 2^L := by omega
  have hsourceLeft :=
    m2EvenResidueFour_source_left L k a hL hbound
  have htargetLeft :=
    m2EvenResidueFour_target_left L k a hL hbound3
  have hbaseSource :=
    m2EvenResidueFour_source_base_left a
  have hbaseTarget :=
    m2EvenResidueFour_target_base_left a
  have hbaseFace :
      m2EvenQ4LeftFacing a = q4LeftFacing 3 3 a := by
    change [true] ++ (d1pow a ++
      (markerWord 1 ++ (d0 ++ (binDec 3 3 ++ lh)))) =
      q4LeftFacing 3 3 a
    simp [q4LeftFacing,List.append_assoc]
  have hprefixLength := m2EvenResidueFourTargetPrefix_length a
  have hinputLength := m2EvenResidueFourInputPrefix_length a
  have hbaseLeft : ∀ i : Nat,
      m2EvenQ4CutTape a b h (h-(i:Int)) =
        sideBit (m2EvenQ4LeftFacing a) i := by
    obtain ⟨Tq,_,hleft,_,_⟩ := m2Even_q4_prefix_data a b h ha
    have hTq : Tq = m2EvenQ4CutTape a b h := by rfl
    simpa [hTq] using hleft
  intro i
  by_cases hi : i ≤ 3*a+14
  · have hin :
      m2EvenResidueFourInside a h (h-(i:Int)) = true := by
      simp [m2EvenResidueFourInside]
      omega
    rw [m2EvenResidueFour_cut_eq_base L k a b h
      (h-(i:Int)) (by omega)]
    rw [hbaseLeft i]
    rw [hbaseFace]
    have hbaseBit := sideBit_append_left
      (m2EvenResidueFourTargetPrefix a) lh i
      (by rw [hprefixLength]; omega)
    have htargetBit := sideBit_append_left
      (m2EvenResidueFourTargetPrefix a)
      (binDec (L-3) k ++ lh) i
      (by rw [hprefixLength]; omega)
    rw [hbaseTarget]
    rw [htargetLeft]
    rw [hbaseBit,htargetBit]
  · have hout :
      m2EvenResidueFourInside a h (h-(i:Int)) = false := by
      simp [m2EvenResidueFourInside]
      omega
    rw [m2EvenResidueFour_cut_eq_input L k a b h
      (h-(i:Int)) hout]
    have hcell := s1Config_left_cell L (8*k+4) 2 a 0 b h i
    rw [hsourceLeft] at hcell
    rw [m2EvenResidueFourLeftFacing,htargetLeft]
    have hsrcBit := sideBit_append_right
      (m2EvenResidueFourInputPrefix a)
      (binDec (L-3) k ++ lh) i
      (by rw [hinputLength]; omega)
    have htgtBit := sideBit_append_right
      (m2EvenResidueFourTargetPrefix a)
      (binDec (L-3) k ++ lh) i
      (by rw [hprefixLength]; omega)
    rw [hsrcBit] at hcell
    rw [htgtBit]
    exact hcell

private theorem m2EvenResidueFour_rightFacing
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    ∀ i : Nat,
      m2EvenResidueFourCutTape L k a b h (h+1+(i:Int)) =
        sideBit (q4RightFacing b) i := by
  intro i
  have hbase : m2EvenQ4CutTape a b h (h+1+(i:Int)) =
      sideBit (q4RightFacing b) i := by
    obtain ⟨Tq,_,_,_,hright⟩ := m2Even_q4_prefix_data a b h ha
    have hTq : Tq = m2EvenQ4CutTape a b h := by rfl
    simpa [hTq] using hright i
  rw [m2EvenResidueFour_cut_eq_base L k a b h
    (h+1+(i:Int)) (by omega)]
  exact hbase

private theorem m2EvenResidueFour_prefix_rightShape
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    q4RightShape (m2EvenResidueFourCutTape L k a b h) h b := by
  apply q4RightShape_congr
    (m2EvenQ4CutTape a b h)
    (m2EvenResidueFourCutTape L k a b h) h b
  · intro x hx
    exact (m2EvenResidueFour_cut_eq_base L k a b h x hx).symm
  · obtain ⟨Tq,_,_,hshape,_⟩ :=
      m2Even_q4_prefix_data a b h ha
    have hTq : Tq = m2EvenQ4CutTape a b h := by rfl
    simpa [hTq] using hshape

/-- The generalized 56+12*a source prefix, with the entire arbitrary
higher-order input tail preserved outside the finite read half-line. -/
theorem m2Even_residue4_q4_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    run tm2 (56+12*a)
      (s1Config L (8*k+4) 2 a 0 b h) =
      some ⟨4,h,m2EvenResidueFourCutTape L k a b h⟩ := by
  let base : Config := ⟨3,h,(s1Config 3 4 2 a 0 b h).tape⟩
  let background := (s1Config L (8*k+4) 2 a 0 b h).tape
  have hinput := m2EvenResidueFour_input_matches L k a b h hL hbound
  have hstart :
      frame (m2EvenResidueFourInside a h) background base =
        s1Config L (8*k+4) 2 a 0 b h := by
    apply m2EvenResidueFour_config_ext
    · rfl
    · rfl
    · funext x
      by_cases hx : m2EvenResidueFourInside a h x = true
      · simp [frame,background,base,hx,hinput x hx]
      · simp [frame,background,base,hx]
  have hheads :
      ∀ j, j < 56+12*a → ∀ d,
        run tm2 j base = some d →
        m2EvenResidueFourInside a h d.head = true := by
    intro j hj d hd
    have hlow := m2Even_q4_prefix_head_bound a b h j hj d hd
    simpa [m2EvenResidueFourInside] using hlow
  have hlift := run_frame tm2 (m2EvenResidueFourInside a h)
    background base (56+12*a) hheads
  rw [hstart] at hlift
  have hbaseRun :
      run tm2 (56+12*a) base =
        some (⟨4,h,m2EvenQ4CutTape a b h⟩ : Config) := by
    obtain ⟨Tq,hprefix,_,_,_⟩ :=
      m2Even_q4_prefix_data a b h ha
    have hTq : Tq = m2EvenQ4CutTape a b h := by rfl
    simpa [base,hTq] using hprefix
  rw [hbaseRun] at hlift
  simp only [Option.map_some] at hlift
  simpa [m2EvenResidueFourCutTape,background] using hlift

/-- The generalized prefix provides exactly the q4 suffix's four
infinite-tape interfaces. -/
theorem m2Even_residue4_q4_prefix_data
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    ∃ Tq,
      run tm2 (56+12*a) (s1Config L (8*k+4) 2 a 0 b h) =
        some ⟨4,h,Tq⟩ ∧
      (∀ i : Nat, Tq (h-(i:Int)) =
        sideBit (q4LeftFacing L (8*k+3) a) i) ∧
      q4RightShape Tq h b ∧
      (∀ i : Nat, Tq (h+1+(i:Int)) =
        sideBit (q4RightFacing b) i) := by
  refine ⟨m2EvenResidueFourCutTape L k a b h, ?_, ?_, ?_, ?_⟩
  · exact m2Even_residue4_q4_prefix_source L k a b h hL hbound ha
  · simpa [m2EvenResidueFourLeftFacing] using
      m2EvenResidueFour_leftFacing L k a b h hL hbound ha
  · exact m2EvenResidueFour_prefix_rightShape L k a b h hL hbound ha
  · exact m2EvenResidueFour_rightFacing L k a b h hL hbound ha

/-- The full right ray is blank beyond the q4 suffix's nine-cell window. -/
private theorem m2EvenResidueFour_prefix_far_tail
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    ∀ i : Nat, 9+3*b ≤ i →
      m2EvenResidueFourCutTape L k a b h (h+1+(i:Int)) = false := by
  intro i hi
  rw [m2EvenResidueFour_rightFacing L k a b h hL hbound ha i]
  apply sideBit_ge_length
  rw [q4RightFacing_length]
  omega

/-- Full source-level Rst2 reset prefix for every admissible n=8*k+4. -/
theorem m2Even_residue4_q4_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 2 (8*k+4) a b)
      (s1Config L (8*k+4) 2 a 0 b h) =
      some (s1Config L (8*k+3) 1 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  obtain ⟨Tq,hprefix,hleft,hshape,hright⟩ :=
    m2Even_residue4_q4_prefix_data L k a b h hL hbound ha
  have htail : ∀ i : Nat, 9+3*b ≤ i → Tq (h+1+(i:Int)) = false := by
    intro i hi
    rw [hright i]
    apply sideBit_ge_length
    rw [q4RightFacing_length]
    omega
  have happend := q4SuffixTargetLeft L (8*k+3) a b
  have hsuffix := q4_suffix_run_to_s1Config Tq h b
    L (8*k+3) 1 (a+b+2) (2^b-1)
    (q4LeftFacing L (8*k+3) a)
    hshape htail hleft happend
  have hsum :
      resetPrefixCost 2 (8*k+4) a b = (56+12*a)+(39+3*b) := by
    have hv : v2 (8*k+4) = 2 := by
      exact v2_of_odd_factorization (8*k+4) (2*k) 2 (by omega)
    simp [resetPrefixCost,hv]
    omega
  rw [hsum,run_add,hprefix]
  simp only [Option.bind_some]
  exact hsuffix

/-- Complete source-level m=2 increment for every n=8*k+4, including
the exact geometric all-ones drain. -/
theorem m2Even_residue4_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*k+4 < 2^L) (ha : 0 < a) :
    run tm2 (proposedIncrementCost 2 (8*k+4) a b)
      (s1Config L (8*k+4) 2 a 0 b h) =
      some (s1Config L (8*k+3) 1 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m2Even_residue4_q4_reset_prefix_source
    L k a b h hL hbound ha
  have hboundDrain := resetDrainBound a b 2 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*k+3) 1 (a+b+2) b (h+5+3*b)
    (s1Config L (8*k+4) 2 a 0 b h)
    (resetPrefixCost 2 (8*k+4) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms binDec_residue4
#print axioms binDec_residue3
#print axioms m2Even_residue4_q4_prefix_source
#print axioms m2Even_residue4_q4_reset_prefix_source
#print axioms m2Even_residue4_counted_increment_source

end BB6Coverage.Agent48M2EvenResidueFour
