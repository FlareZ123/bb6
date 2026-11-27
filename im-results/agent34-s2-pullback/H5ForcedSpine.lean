import H5Precision
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34H5Spine
open BB6.Agent42ModularCone
open BB6.Agent34H5Precision
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- A certificate specifies the sole inverse branch left unexcluded.
    `none` denotes the direct predecessor, `some n` high predecessor n. -/
def branchBits (b : Nat) : Option Nat → Nat
  | none => b-1
  | some n => b-(n+2)

def branchResidue (b : Nat) (s : Pair) : Option Nat → Pair
  | none => residue (b-1) (direct s)
  | some n => residue (b-(n+2)) (high s n)

/-- Check every non-designated parent with the existing original-source
    sound inverse-cone checker. This is a one-open-leaf certificate. -/
def forcedAt (b : Nat) (s : Pair) (choice : Option Nat) : Bool :=
  decide (2≤b) &&
  decide (ValValid b s (valuation b (q s))) &&
  (if s.y%2=0 then decide (choice=none) || excluded (b-1) (direct s) else true) &&
  (List.range (valuation b (q s)+1)).all (fun n =>
    if Allowed s (valuation b (q s)) n then
      decide (HighValid s n) &&
        (if choice=some n then true else excluded (b-(n+2)) (high s n))
    else true)

/-- The exact arithmetic equation witnessed by the selected original-source inverse edge. -/
def StepEq (choice : Option Nat) (a k x y : Nat) : Prop :=
  match choice with
  | none => a+2=x+y ∧ 2*k+2=y
  | some n =>
      x+y+(x+y)%2 = P (n+1)*(a+2+(x+y)%2) ∧
      2*k+a+7+3*n = x+2*y

/-- Each successful one-open-leaf certificate transports original blank
    reachability into the uniquely designated parent, retaining the exact
    lower height bound and congruence data for the next certificate. -/
theorem source_forced_one (b : Nat) (s : Pair) (choice : Option Nat)
    (hc : forcedAt b s choice = true) (x y : Nat)
    (hr : BB6.Agent3.CReach x y)
    (hl : Large b y) (hm : Matches b x y s) :
    ∃ a k, BB6.Agent3.CReach a k ∧
      Large (branchBits b choice) k ∧
      Matches (branchBits b choice) a k (branchResidue b s choice) ∧
      StepEq choice a k x y := by
  simp only [forcedAt, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨hb,hv⟩,hd⟩,hh⟩
  let v := valuation b (q s)
  have hactual := actual_val hb hl hm hv
  obtain ⟨a,k,hrp,hinv⟩ :=
    source_parent x y v hr (large_y hb hl) hactual.1 hactual.2
  rcases hinv with ⟨hy,ha,hk⟩ | ⟨n,hn,hpar,hq,hw⟩
  · have hye : s.y%2=0 := by
      have hh := cong_nat_mod (cong_weaken (by omega : 1≤b) hm.2)
      change ((y%2:Nat):Int)=s.y%2 at hh
      omega
    have hbranch : choice=none ∨ excluded (b-1) (direct s)=true := by
      simpa only [hye, ite_true, Bool.or_eq_true, decide_eq_true_eq] using hd
    have hchildLarge := large_direct (by omega : 1≤b) hl hk
    have hchildMatches := direct_matches (by omega : 1≤b) hm ha hk hye
    rcases hbranch with hchosen | hcert
    · subst choice
      exact ⟨a,k,hrp,hchildLarge,matches_residue hchildMatches,⟨ha,hk⟩⟩
    · exact False.elim
        ((source_excluded (b-1) (direct s) hcert a k hchildLarge hchildMatches) hrp)
  · have hallowed : Allowed s v n := allowed_actual hb hm hn hpar
    have hnmem : n ∈ List.range (v+1) := List.mem_range.mpr (by omega)
    have hline :
        (decide (HighValid s n)=true) ∧
        ((if choice=some n then true else excluded (b-(n+2)) (high s n))=true) := by
      have hline0 := List.all_eq_true.mp hh n hnmem
      have hline1 :
          (decide (HighValid s n) &&
            (if choice=some n then true else excluded (b-(n+2)) (high s n)))=true := by
        simpa only [hallowed, ite_true] using hline0
      simpa only [Bool.and_eq_true] using hline1
    have hvalid : HighValid s n := by
      simpa only [decide_eq_true_eq] using hline.1
    have hchildLarge := large_high (by have := hv.1; omega : n+2≤b) hl hq hw
    have hchildMatches :=
      high_matches (by have := hv.1; omega : n+2≤b) hm hq hw hvalid
    by_cases hchosen : choice=some n
    · refine ⟨a,k,hrp,?_,?_,?_⟩
      · simpa [branchBits,hchosen] using hchildLarge
      · simpa [branchBits,branchResidue,hchosen] using
          (matches_residue hchildMatches)
      · simpa only [StepEq,hchosen] using (And.intro hq hw)
    · have hcert : excluded (b-(n+2)) (high s n)=true := by
        simpa only [hchosen, ite_false] using hline.2
      exact False.elim
        ((source_excluded (b-(n+2)) (high s n) hcert a k
          hchildLarge hchildMatches) hrp)

/-- Compose an arbitrary list of source-faithful one-open-leaf certificates. -/
def spineCert : List (Option Nat) → Nat → Pair → Bool
  | [], _, _ => true
  | choice::rest, b, s =>
      forcedAt b s choice &&
      spineCert rest (branchBits b choice) (branchResidue b s choice)

def spineBits : List (Option Nat) → Nat → Nat
  | [], b => b
  | choice::rest, b => spineBits rest (branchBits b choice)

def spineResidue : List (Option Nat) → Nat → Pair → Pair
  | [], _, s => s
  | choice::rest, b, s =>
      spineResidue rest (branchBits b choice) (branchResidue b s choice)

theorem source_spine_sound (choices : List (Option Nat)) (b : Nat) (s : Pair)
    (hc : spineCert choices b s=true)
    (x y : Nat) (hr : BB6.Agent3.CReach x y)
    (hl : Large b y) (hm : Matches b x y s) :
    ∃ a k, BB6.Agent3.CReach a k ∧
      Large (spineBits choices b) k ∧
      Matches (spineBits choices b) a k (spineResidue choices b s) := by
  induction choices generalizing b s x y with
  | nil =>
      exact ⟨x,y,hr,hl,hm⟩
  | cons choice rest ih =>
      have hs : forcedAt b s choice=true ∧
          spineCert rest (branchBits b choice) (branchResidue b s choice)=true := by
        simpa only [spineCert, Bool.and_eq_true] using hc
      obtain ⟨a,k,hrp,hlp,hmp,_⟩ :=
        source_forced_one b s choice hs.1 x y hr hl hm
      simpa only [spineBits,spineResidue] using
        (ih (branchBits b choice) (branchResidue b s choice)
          hs.2 a k hrp hlp hmp)

/-- Unique designated predecessor word, including the two high alternate
    branches and three direct alternate branches certified absent. -/
def h5Spine : List (Option Nat) :=
  [some 1,some 2,some 0,none,some 0,none,none,some 1,none,some 0]

theorem h5SpineCert :
    spineCert h5Spine 23 (stopResidue (J 0) (M 0 0))=true := by decide

theorem h5_spine_terminal_bits : spineBits h5Spine 23=3 := by decide
theorem h5_spine_terminal_residue :
    spineResidue h5Spine 23 (stopResidue (J 0) (M 0 0)) = ⟨7,0⟩ := by decide

private theorem h5_root_matches23 (r w k : Nat)
    (he : k+J r+3*M r w+4=2^(2*M r w+2)*(J r+2)) :
    Matches 23 (2*J r+1) k (stopResidue (J 0) (M 0 0)) := by
  have hsource : Matches 23 (2*J r+1) k (stopResidue (J r) (M r w)) :=
    stop_matches 23 (J r) (M r w) k (by unfold M; omega) he
  have hx : Cong 23 (stopResidue (J r) (M r w)).x
      (stopResidue (J 0) (M 0 0)).x := by
    unfold Cong
    refine ⟨(r:Int), ?_⟩
    change _ = (8388608:Int) * _
    simp only [stopResidue, J, M, Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int]
    omega
  have hy : Cong 23 (stopResidue (J r) (M r w)).y
      (stopResidue (J 0) (M 0 0)).y := by
    unfold Cong
    refine ⟨-2*(r:Int)-3*(w:Int), ?_⟩
    change _ = (8388608:Int) * _
    simp only [stopResidue, J, M, Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int]
    omega
  exact ⟨cong_trans hsource.1 hx,cong_trans hsource.2 hy⟩

/-- Original Machine C source: ten successive exact inverse steps from
    *any* blank-reachable H5 odd-coset high stop necessarily end in the
    residual state (left mod 8=7, right mod 8=0), with right counter ≥22.
    No finite simulation or unproved root decision is used. -/
theorem h5_ten_forced_ancestor (r w k : Nat)
    (he : k+J r+3*M r w+4=2^(2*M r w+2)*(J r+2))
    (hr : BB6.Agent3.CReach (2*J r+1) k) :
    ∃ a t, BB6.Agent3.CReach a t ∧
      Large 3 t ∧ Matches 3 a t ⟨7,0⟩ := by
  have hl : Large 23 k :=
    large_weaken (by unfold M; omega : 23≤2*M r w+1)
      (stop_size (J r) (M r w) k he)
  have hm := h5_root_matches23 r w k he
  have h := source_spine_sound h5Spine 23
    (stopResidue (J 0) (M 0 0)) h5SpineCert
    (2*J r+1) k hr hl hm
  rw [h5_spine_terminal_bits,h5_spine_terminal_residue] at h
  exact h

#print axioms source_forced_one
#print axioms source_spine_sound
#print axioms h5SpineCert
#print axioms h5_ten_forced_ancestor
end BB6.Agent34H5Spine
