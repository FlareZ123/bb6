import RootShift
import ChampionRootBridge
import CountedSweep
import CountedOddBase
import S1Encoder
import CountedReset
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent46Rst1Prime

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset

/-- A finite interval in head-relative coordinates. -/
def inWindow (lo hi : Int) : Int → Bool :=
  fun x => decide (lo ≤ x ∧ x ≤ hi)

/-- Recenter an infinite tape at the current head. -/
def centerTape (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => T (h+x)

/-- The exact infinite-tape result of applying a finite local frame at head h. -/
def frameAt (T : Int → Bool) (h : Int) (inside : Int → Bool)
    (c : FConfig) : Config :=
  shiftConfig h (frame inside (centerTape T h) (embed c))

@[simp] theorem frameAt_state (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) :
    (frameAt T h inside c).state = c.state := by
  rfl

@[simp] theorem frameAt_head (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) :
    (frameAt T h inside c).head = h + c.head := by
  rfl

@[simp] theorem frameAt_tape (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) (x : Int) :
    (frameAt T h inside c).tape x =
      (if inside (x-h) then decide (x-h ∈ c.marked) else T x) := by
  simp [frameAt, frame, shiftConfig, centerTape, embed]

/-- Lift finite trace head bounds to the original infinite-tape semantics. -/
theorem finiteHeads (inside : Int → Bool) (c : FConfig) (n : Nat)
    (hcheck : (List.range n).all (fun k =>
      match fRun tm2 k c with
      | none => true
      | some f => inside f.head) = true) :
    ∀ k, k<n → ∀ d, run tm2 k (embed c) = some d → inside d.head = true := by
  intro k hk d hd
  have hitem := List.all_eq_true.mp hcheck k (List.mem_range.mpr hk)
  have hsource := finite_run_source tm2 k c
  cases hrun : fRun tm2 k c with
  | none =>
      simp only [hrun, Option.map_none] at hsource
      rw [← hsource] at hd
      cases hd
  | some f =>
      simp only [hrun, Option.map_some] at hsource
      have hd' := Option.some.inj (hsource.trans hd)
      subst d
      simpa [hrun, embed] using hitem

/-- A finite TM63 trace, together with a head-window certificate, acts on
an arbitrary surrounding tape without any finite-tape approximation. -/
theorem finiteBridgeFrame (inside background : Int → Bool)
    (c d : FConfig) (n : Nat)
    (hexact : fRun tm2 n c = some d)
    (hcheck : (List.range n).all (fun k =>
      match fRun tm2 k c with
      | none => true
      | some f => inside f.head) = true) :
    run tm2 n (frame inside background (embed c)) =
      some (frame inside background (embed d)) := by
  have hheads := finiteHeads inside c n hcheck
  rw [run_frame tm2 inside background (embed c) n hheads]
  rw [← finite_run_source tm2 n c, hexact]
  rfl

/-- Translate a local finite trace to any absolute head coordinate. The
hypothesis only specifies cells in the finite region actually queried. -/
theorem bridgeAt (T : Int → Bool) (h : Int) (inside : Int → Bool)
    (c d : FConfig) (n : Nat)
    (hc : c.head = 0)
    (hexact : fRun tm2 n c = some d)
    (hcheck : (List.range n).all (fun k =>
      match fRun tm2 k c with
      | none => true
      | some f => inside f.head) = true)
    (hmatch : ∀ x, inside x = true →
      T (h+x) = decide (x ∈ c.marked)) :
    run tm2 n ⟨c.state,h,T⟩ = some (frameAt T h inside d) := by
  have hframe :
      frame inside (centerTape T h) (embed c) =
        ({state := c.state, head := 0, tape := centerTape T h} : Config) := by
    cases c with
    | mk s ch marks =>
      have hch : ch = 0 := hc
      subst ch
      apply Config.ext
      · rfl
      · rfl
      · funext x
        by_cases hx : inside x = true
        · simp [frame, embed, centerTape, hx, hmatch x hx]
        · simp [frame, embed, centerTape, hx]
  have hrun := finiteBridgeFrame inside (centerTape T h) c d n hexact hcheck
  rw [hframe] at hrun
  have hshift :
      shiftConfig h
        ({state := c.state, head := 0, tape := centerTape T h} : Config)
        = ⟨c.state,h,T⟩ := by
    apply Config.ext
    · rfl
    · simp [shiftConfig]
    · funext x
      simp [shiftConfig, centerTape]
  rw [← hshift, shift_run, hrun]
  rfl

/-! The five fixed bridges in the Rst1' itinerary. Their finite traces are
exact computations of the published TM63 transition table. -/

def inside8 : Int → Bool := inWindow (-3) 0
def bridge8Start : FConfig := ⟨3,0,[-1]⟩
def bridge8End : FConfig := ⟨3,-2,[0,-2,-3]⟩

theorem bridge8_exact : fRun tm2 8 bridge8Start = some bridge8End := by decide

theorem bridge8_heads :
    (List.range 8).all (fun k =>
      match fRun tm2 k bridge8Start with
      | none => true
      | some f => inside8 f.head) = true := by decide

theorem bridge8_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, inside8 x = true →
      T (h+x) = decide (x ∈ bridge8Start.marked)) :
    run tm2 8 ⟨3,h,T⟩ = some (frameAt T h inside8 bridge8End) := by
  exact bridgeAt T h inside8 bridge8Start bridge8End 8 rfl
    bridge8_exact bridge8_heads hmatch

def inside20 : Int → Bool := inWindow (-5) 3
def bridge20Start : FConfig := ⟨3,0,[-3,-2,-1,2,3]⟩
def bridge20End : FConfig := ⟨3,4,[1,0,-1,-3,-4,-5]⟩

theorem bridge20_exact :
    fRun tm2 20 bridge20Start = some bridge20End := by decide

theorem bridge20_heads :
    (List.range 20).all (fun k =>
      match fRun tm2 k bridge20Start with
      | none => true
      | some f => inside20 f.head) = true := by decide

theorem bridge20_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, inside20 x = true →
      T (h+x) = decide (x ∈ bridge20Start.marked)) :
    run tm2 20 ⟨3,h,T⟩ = some (frameAt T h inside20 bridge20End) := by
  exact bridgeAt T h inside20 bridge20Start bridge20End 20 rfl
    bridge20_exact bridge20_heads hmatch

def inside9 : Int → Bool := inWindow (-2) 2
def bridge9Start : FConfig := ⟨3,0,[0,2]⟩
def bridge9End : FConfig := ⟨3,3,[0,-1,-2]⟩

theorem bridge9_exact : fRun tm2 9 bridge9Start = some bridge9End := by decide

theorem bridge9_heads :
    (List.range 9).all (fun k =>
      match fRun tm2 k bridge9Start with
      | none => true
      | some f => inside9 f.head) = true := by decide

theorem bridge9_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, inside9 x = true →
      T (h+x) = decide (x ∈ bridge9Start.marked)) :
    run tm2 9 ⟨3,h,T⟩ = some (frameAt T h inside9 bridge9End) := by
  exact bridgeAt T h inside9 bridge9Start bridge9End 9 rfl
    bridge9_exact bridge9_heads hmatch

def inside6 : Int → Bool := inWindow (-1) 3
def bridge6Start : FConfig := ⟨3,0,[2,3]⟩
def bridge6End : FConfig := ⟨3,4,[1,0,-1]⟩

theorem bridge6_exact : fRun tm2 6 bridge6Start = some bridge6End := by decide

theorem bridge6_heads :
    (List.range 6).all (fun k =>
      match fRun tm2 k bridge6Start with
      | none => true
      | some f => inside6 f.head) = true := by decide

theorem bridge6_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, inside6 x = true →
      T (h+x) = decide (x ∈ bridge6Start.marked)) :
    run tm2 6 ⟨3,h,T⟩ = some (frameAt T h inside6 bridge6End) := by
  exact bridgeAt T h inside6 bridge6Start bridge6End 6 rfl
    bridge6_exact bridge6_heads hmatch

def inside30 : Int → Bool := inWindow (-3) 5
def bridge30Start : FConfig := ⟨3,0,[-3,0]⟩
def bridge30End : FConfig := ⟨3,-4,[-2,-1,0,3,4,5]⟩

theorem bridge30_exact :
    fRun tm2 30 bridge30Start = some bridge30End := by decide

theorem bridge30_heads :
    (List.range 30).all (fun k =>
      match fRun tm2 k bridge30Start with
      | none => true
      | some f => inside30 f.head) = true := by decide

theorem bridge30_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, inside30 x = true →
      T (h+x) = decide (x ∈ bridge30Start.marked)) :
    run tm2 30 ⟨3,h,T⟩ = some (frameAt T h inside30 bridge30End) := by
  exact bridgeAt T h inside30 bridge30Start bridge30End 30 rfl
    bridge30_exact bridge30_heads hmatch

/-- Exact arithmetic for the proposed ten-phase Rst1' itinerary. -/
theorem rst1Prime_cost_decomposition (L a b : Nat) :
    3*(3*a+1) + 8 + 3*(3*L+5) + 20 + 3*(L+1) + 9 +
      3*(a+1) + 6 + 3*b + 30 =
        97 + 12*(L+a) + 3*b := by omega

#print axioms bridge8_at
#print axioms bridge20_at
#print axioms bridge9_at
#print axioms bridge6_at
#print axioms bridge30_at
#print axioms rst1Prime_cost_decomposition

end BB6Coverage.Agent46Rst1Prime
