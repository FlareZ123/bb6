import ChampionRootBridge
import Lean.Elab.Tactic.Omega

/-!
# Positive-z q4/S0 first-cycle short macros

This module isolates the fixed q4 entry bridge and the state-3 left-one
postlude.  The q4 entry bridge is intended to compose with the existing
state-4 scan, state-1 three-one scan, and q4 tail in Agent8Q4Suffix.
The postlude is an original-TM2 run theorem over an arbitrary exterior
tape.  The complete checkpoint-to-S0 and S0-to-checkpoint tape identities
are separate obligations.
-/

namespace BB6Coverage.Agent48Q4S0Macros

open BB6Coverage
open BB6Coverage.Agent48Champion

set_option maxHeartbeats 4000000


private theorem q4FrameConfigExt {c d : Config}
    (hs : c.state = d.state) (hh : c.head = d.head)
    (ht : c.tape = d.tape) : c = d := by
  cases c with
  | mk cs ch ct =>
    cases d with
    | mk ds dh dt =>
      simp only at hs hh ht
      subst ds
      subst dh
      subst dt
      rfl

/-- A finite frame replaces only the specified head-relative interval. -/
def q4Frame (inside : Int → Bool) (background : Int → Bool)
    (c : Config) : Config :=
  { state := c.state, head := c.head,
    tape := fun x => if inside x then c.tape x else background x }

/-- Recenter an infinite tape at a chosen head coordinate. -/
def q4CenterTape (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => T (h+x)

/-- Embed a finite trace frame at an absolute tape coordinate. -/
def q4FrameAt (T : Int → Bool) (h : Int) (inside : Int → Bool)
    (c : FConfig) : Config :=
  shiftConfig h (q4Frame inside (q4CenterTape T h) (embed c))

@[simp] theorem q4FrameAt_tape (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) (x : Int) :
    (q4FrameAt T h inside c).tape x =
      (if inside (x-h) then decide (x-h ∈ c.marked) else T x) := by
  have hcoord : h + (x-h) = x := by omega
  simp [q4FrameAt,q4Frame,q4CenterTape,shiftConfig,embed,hcoord]

private theorem q4Embed_fMove (c : FConfig) (t : Move) :
    embed (fMove c t) = applyMove (embed c) t := by
  cases c with
  | mk q h marks =>
    cases t with
    | mk w d q' =>
      cases w <;> cases d <;>
        simp only [embed, fMove, applyMove] <;>
        apply congrArg (fun f : Int → Bool => Config.mk q' _ f) <;>
        funext x <;>
        (by_cases hx : x = h <;> simp [hx])

private theorem q4Embed_fStep (m : Machine) (c : FConfig) :
    (fStep m c).map embed = rawStep m (embed c) := by
  simp only [fStep,rawStep,readSlot,embed,Option.map_map]
  congr 1
  funext t
  simpa only [Function.comp_def,embed] using q4Embed_fMove c t

private theorem q4Embed_fRun (m : Machine) (n : Nat) (c : FConfig) :
    (fRun m n c).map embed = run m n (embed c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fRun,run]
    rw [← ih]
    cases h : fRun m n c with
    | none => simp [h]
    | some d => simp [h,q4Embed_fStep]

private theorem q4RawStepFrame (m : Machine) (inside background : Int → Bool)
    (c : Config) (hinside : inside c.head = true) :
    rawStep m (q4Frame inside background c) =
      (rawStep m c).map (q4Frame inside background) := by
  have hslot : readSlot (q4Frame inside background c) = readSlot c := by
    simp [readSlot,q4Frame,hinside]
  simp only [rawStep,hslot]
  cases h : m (readSlot c) with
  | none => simp
  | some t =>
    simp only [Option.map_some]
    congr 1
    apply q4FrameConfigExt
    · rfl
    · rfl
    · funext x
      by_cases hx : x = c.head
      · subst x
        simp [q4Frame,applyMove,hinside]
      · simp [q4Frame,applyMove,hx]

private theorem q4RunFrame (m : Machine) (inside background : Int → Bool)
    (c : Config) (n : Nat)
    (hheads : ∀ k, k<n → ∀ d, run m k c = some d → inside d.head = true) :
    run m n (q4Frame inside background c) =
      (run m n c).map (q4Frame inside background) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : ∀ k, k<n → ∀ d, run m k c = some d → inside d.head = true := by
      intro k hk d hd
      exact hheads k (by omega) d hd
    change (run m n (q4Frame inside background c)).bind (rawStep m) =
      ((run m n c).bind (rawStep m)).map (q4Frame inside background)
    rw [ih hprev]
    cases hrun : run m n c with
    | none => simp [hrun]
    | some d =>
      have hi := hheads n (by omega) d hrun
      simp [hrun,q4RawStepFrame m inside background d hi]

private theorem q4FiniteHeads (inside : Int → Bool) (c : FConfig) (n : Nat)
    (hcheck : (List.range n).all (fun k =>
      match fRun tm2 k c with
      | none => true
      | some f => inside f.head) = true) :
    ∀ k, k<n → ∀ d, run tm2 k (embed c) = some d → inside d.head = true := by
  intro k hk d hd
  have hitem := List.all_eq_true.mp hcheck k (List.mem_range.mpr hk)
  have hsource := q4Embed_fRun tm2 k c
  cases hrun : fRun tm2 k c with
  | none =>
    simp only [hrun,Option.map_none] at hsource
    rw [← hsource] at hd
    cases hd
  | some f =>
    simp only [hrun,Option.map_some] at hsource
    have hd' := Option.some.inj (hsource.trans hd)
    subst d
    simpa [hrun,embed] using hitem

private theorem q4FiniteBridgeFrame (inside background : Int → Bool)
    (c d : FConfig) (n : Nat)
    (hexact : fRun tm2 n c = some d)
    (hcheck : (List.range n).all (fun k =>
      match fRun tm2 k c with
      | none => true
      | some f => inside f.head) = true) :
    run tm2 n (q4Frame inside background (embed c)) =
      some (q4Frame inside background (embed d)) := by
  have hheads := q4FiniteHeads inside c n hcheck
  rw [q4RunFrame tm2 inside background (embed c) n hheads]
  rw [← q4Embed_fRun tm2 n c,hexact]
  rfl

/-- Lift a finite TM2 trace to an arbitrary surrounding tape. -/
theorem q4BridgeAt (T : Int → Bool) (h : Int) (inside : Int → Bool)
    (c d : FConfig) (n : Nat)
    (hc : c.head = 0)
    (hexact : fRun tm2 n c = some d)
    (hcheck : (List.range n).all (fun k =>
      match fRun tm2 k c with
      | none => true
      | some f => inside f.head) = true)
    (hmatch : ∀ x, inside x = true →
      T (h+x) = decide (x ∈ c.marked)) :
    run tm2 n ⟨c.state,h,T⟩ = some (q4FrameAt T h inside d) := by
  have hframe :
      q4Frame inside (q4CenterTape T h) (embed c) =
        ({state := c.state, head := 0, tape := q4CenterTape T h} : Config) := by
    cases c with
    | mk s ch marks =>
      have hch : ch = 0 := hc
      subst ch
      apply q4FrameConfigExt
      · rfl
      · rfl
      · funext x
        have hcoord : h + (x-h) = x := by omega
        by_cases hx : inside x = true
        · simp [q4Frame,embed,q4CenterTape,hx,hmatch x hx]
        · simp [q4Frame,embed,q4CenterTape,hx]
  have hrun := q4FiniteBridgeFrame inside (q4CenterTape T h) c d n hexact hcheck
  rw [hframe] at hrun
  have hshift :
      shiftConfig h
        ({state := c.state, head := 0, tape := q4CenterTape T h} : Config)
        = ⟨c.state,h,T⟩ := by
    apply q4FrameConfigExt
    · rfl
    · simp [shiftConfig]
    · funext x
      have hcoord : h + (x-h) = x := by omega
      simp [shiftConfig,q4CenterTape,hcoord]
  rw [← hshift,shift_run,hrun]
  rfl



/-- The fixed 22-step entry bridge only reads the eight-cell window
[-4,3] around the checkpoint-1 head. -/
def q4S0Prefix22Inside (x : Int) : Bool :=
  decide (-4 ≤ x ∧ x ≤ 3)

def q4S0Prefix22Start : FConfig :=
  ⟨4, 0, [-2,-1]⟩

def q4S0Prefix22End : FConfig :=
  ⟨4, 4, [3,1,-2,-3,-4]⟩

theorem q4S0Prefix22_exact :
    fRun tm2 22 q4S0Prefix22Start = some q4S0Prefix22End := by
  decide

theorem q4S0Prefix22_heads :
    (List.range 22).all (fun k =>
      match fRun tm2 k q4S0Prefix22Start with
      | none => true
      | some f => q4S0Prefix22Inside f.head) = true := by
  decide

/-- Exact local input needed by the 22-step q4 entry bridge. -/
def q4S0Prefix22Input (T : Int → Bool) (h : Int) : Prop :=
  ∀ x, q4S0Prefix22Inside x = true →
    T (h+x) = decide (x = -2 ∨ x = -1)

/-- The 22-step bridge is valid with arbitrary tape exterior. -/
theorem q4S0Prefix22_at (T : Int → Bool) (h : Int)
    (hin : q4S0Prefix22Input T h) :
    run tm2 22 ⟨4,h,T⟩ =
      some (q4FrameAt T h q4S0Prefix22Inside q4S0Prefix22End) := by
  apply q4BridgeAt T h q4S0Prefix22Inside
    q4S0Prefix22Start q4S0Prefix22End 22 rfl
    q4S0Prefix22_exact q4S0Prefix22_heads
  intro x hx
  have hlocal := hin x hx
  simpa [q4S0Prefix22Start] using hlocal

/-- The 22-step entry bridge leaves every cell at or to the right of
the first unary sweep untouched. -/
theorem q4S0Prefix22_preserves_after
    (T : Int → Bool) (h y : Int) (hy : h+4 ≤ y) :
    (q4FrameAt T h q4S0Prefix22Inside q4S0Prefix22End).tape y = T y := by
  rw [q4FrameAt_tape]
  have hnot : q4S0Prefix22Inside (y-h) = false := by
    simp [q4S0Prefix22Inside]
    omega
  simp [q4FrameAt_tape,hnot]

/-- One state-3 leftward microcycle shifts a one one cell to the right:
3 at h on 1, then state 1 reads the zero at h+1, then state 2
clears h and moves left. -/
def afterS0LeftOne (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x = h then false else if x = h+1 then true else T x

private theorem q4S0ConfigExt {c d : Config}
    (hs : c.state = d.state) (hh : c.head = d.head)
    (ht : c.tape = d.tape) : c = d := by
  cases c with
  | mk cs ch ct =>
    cases d with
    | mk ds dh dt =>
      simp only at hs hh ht
      subst ds
      subst dh
      subst dt
      rfl

theorem state3_left_one_block (T : Int → Bool) (h : Int)
    (h0 : T h = true) (h1 : T (h+1) = false) :
    run tm2 3 ⟨3,h,T⟩ =
      some ⟨3,h-1,afterS0LeftOne T h⟩ := by
  have t31 : tm2 ((3 : Fin 6), true) = some ⟨true,true,1⟩ := rfl
  have t10 : tm2 ((1 : Fin 6), false) = some ⟨true,false,2⟩ := rfl
  have t21 : tm2 ((2 : Fin 6), true) = some ⟨false,false,3⟩ := rfl
  have hstep0 : rawStep tm2 ⟨3,h,T⟩ = some ⟨1,h+1,T⟩ := by
    simp only [rawStep, readSlot, h0, t31, Option.map_some]
    apply congrArg some
    apply q4S0ConfigExt
    · rfl
    · simp [applyMove]
    · funext x
      by_cases hx : x = h
      · subst x
        simp [applyMove,h0]
      · simp [applyMove,hx]
  let T1 : Int → Bool := fun x => if x = h+1 then true else T x
  have hstep1 : rawStep tm2 ⟨1,h+1,T⟩ = some ⟨2,h,T1⟩ := by
    simp only [rawStep, readSlot, h1, t10, Option.map_some]
    apply congrArg some
    apply q4S0ConfigExt
    · rfl
    · simp [applyMove]
      omega
    · funext x
      by_cases hx : x = h+1
      · subst x
        simp [applyMove,T1]
      · simp [applyMove,T1,hx]
  have hT1h : T1 h = true := by
    have hne : h ≠ h+1 := by omega
    simp [T1,h0,hne]
  have hstep2 : rawStep tm2 ⟨2,h,T1⟩ =
      some ⟨3,h-1,afterS0LeftOne T h⟩ := by
    simp only [rawStep, readSlot, hT1h, t21, Option.map_some]
    apply congrArg some
    apply q4S0ConfigExt
    · rfl
    · simp [applyMove]
      omega
    · funext x
      by_cases hx0 : x = h
      · subst x
        simp [applyMove,afterS0LeftOne]
      · by_cases hx1 : x = h+1
        · subst x
          simp [applyMove,afterS0LeftOne,T1]
        · simp [applyMove,afterS0LeftOne,T1,hx0,hx1]
  simp [run,hstep0,hstep1,hstep2]

/-- The next k cells to the left of h are all one. -/
def s0LeftOnes (T : Int → Bool) (h : Int) (k : Nat) : Prop :=
  ∀ i, i < k → T (h-(i:Int)) = true

/-- Tape after k successive state-3 left-one microcycles. -/
def s0LeftSweep : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0, T, _ => T
  | k+1, T, h => s0LeftSweep k (afterS0LeftOne T h) (h-1)

theorem state3_left_ones_scan (k : Nat) (T : Int → Bool) (h : Int)
    (hones : s0LeftOnes T h k) (hright : T (h+1) = false) :
    run tm2 (3*k) ⟨3,h,T⟩ =
      some ⟨3,h-(k:Int),s0LeftSweep k T h⟩ := by
  induction k generalizing T h with
  | zero =>
      simp [s0LeftSweep,run]
  | succ k ih =>
      have h0 : T h = true := by
        have := hones 0 (by omega)
        simpa using this
      have hleft : s0LeftOnes (afterS0LeftOne T h) (h-1) k := by
        intro i hi
        have hval := hones (i+1) (by omega)
        have heq : h-1-(i:Int) = h-((i+1:Int)) := by omega
        rw [heq]
        have hne0 : h-((i+1:Int)) ≠ h := by omega
        have hne1 : h-((i+1:Int)) ≠ h+1 := by omega
        simp [afterS0LeftOne,hne0,hne1]
        exact hval
      have hstep := state3_left_one_block T h h0 hright
      have hnextRight :
          afterS0LeftOne T h ((h-1)+1) = false := by
        have heq : (h-1)+1 = h := by omega
        rw [heq]
        simp [afterS0LeftOne]
      have htail := ih (afterS0LeftOne T h) (h-1) hleft hnextRight
      have hnum : 3*(k+1) = 3+3*k := by omega
      rw [hnum,run_append,hstep]
      simp only [Option.bind_some]
      have hhead : h-1-(k:Int) = h-((k+1:Int)) := by omega
      simpa [s0LeftSweep,hhead] using htail

/-- The left-one scan shifts the k-cell one-run right by one position.
The leftmost processed cell is cleared; the following k cells are one. -/
theorem s0LeftSweep_shift (k : Nat) (T : Int → Bool) (h : Int)
    (hk : 0 < k) :
    ∀ x, s0LeftSweep k T h x =
      if x = h-(k:Int)+1 then false
      else if h-(k:Int)+2 ≤ x ∧ x ≤ h+1 then true
      else T x := by
  induction k generalizing T h with
  | zero => omega
  | succ k ih =>
      intro x
      by_cases hk0 : k = 0
      · subst k
        have hlow : h-(1:Int)+1 = h := by omega
        have hlow2 : h-(1:Int)+2 = h+1 := by omega
        by_cases hx0 : x = h
        · subst x
          simp [s0LeftSweep,afterS0LeftOne,hlow]
        · by_cases hx1 : x = h+1
          · subst x
            simp [s0LeftSweep,afterS0LeftOne,hlow,hlow2]
          · simp [s0LeftSweep,afterS0LeftOne,hlow,hlow2,hx0,hx1] <;> omega
      · have hkpos : 0 < k := by omega
        have ih' := ih (afterS0LeftOne T h) (h-1) hkpos x
        have hlow : (h-1)-(k:Int)+1 = h-(k+1:Int)+1 := by omega
        have hlow2 : (h-1)-(k:Int)+2 = h-(k+1:Int)+2 := by omega
        rw [hlow,hlow2] at ih'
        change s0LeftSweep k (afterS0LeftOne T h) (h-1) x = _
        rw [ih']
        by_cases hx0 : x = h
        · subst x
          have hbound : h-(k+1:Int)+2 ≤ h := by omega
          have hneLow : h ≠ h-(k+1:Int)+1 := by omega
          simp [afterS0LeftOne,hbound,hneLow] <;> omega
        · by_cases hx1 : x = h+1
          · subst x
            have hbound : h-(k+1:Int)+2 ≤ h+1 := by omega
            have hneLow : h+1 ≠ h-(k+1:Int)+1 := by omega
            simp [afterS0LeftOne,hbound,hneLow] <;> omega
          · have hbound : (x ≤ h+1) ↔ x ≤ h := by omega
            simp [afterS0LeftOne,hx0,hx1,hbound]

/-- The final four moves return state 3/head 3 to state 4/head 1
when the local bits are 0,1,0,0. -/
def q4S0Final4Inside (x : Int) : Bool :=
  decide (-3 ≤ x ∧ x ≤ 0)

def q4S0Final4Start : FConfig :=
  ⟨3, 0, [-1]⟩

def q4S0Final4End : FConfig :=
  ⟨4, -2, [-3]⟩

theorem q4S0Final4_exact :
    fRun tm2 4 q4S0Final4Start = some q4S0Final4End := by
  decide

theorem q4S0Final4_heads :
    (List.range 4).all (fun k =>
      match fRun tm2 k q4S0Final4Start with
      | none => true
      | some f => q4S0Final4Inside f.head) = true := by
  decide

def q4S0Final4Input (T : Int → Bool) (h : Int) : Prop :=
  T (h-3) = false ∧ T (h-2) = false ∧
  T (h-1) = true ∧ T h = false

theorem q4S0Final4_at (T : Int → Bool) (h : Int)
    (hin : q4S0Final4Input T h) :
    run tm2 4 ⟨3,h,T⟩ =
      some (q4FrameAt T h q4S0Final4Inside q4S0Final4End) := by
  apply q4BridgeAt T h q4S0Final4Inside
    q4S0Final4Start q4S0Final4End 4 rfl
    q4S0Final4_exact q4S0Final4_heads
  intro x hx
  have hrange : -3 ≤ x ∧ x ≤ 0 := by
    simpa [q4S0Final4Inside] using hx
  have hcases : x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 := by omega
  rcases hcases with hx0|hx1|hx2|hx3 <;> subst x
  · have heq : h+(-3:Int) = h-3 := by omega
    rw [heq]
    simpa [q4S0Final4Start] using hin.1
  · have heq : h+(-2:Int) = h-2 := by omega
    rw [heq]
    simpa [q4S0Final4Start] using hin.2.1
  · have heq : h+(-1:Int) = h-1 := by omega
    rw [heq]
    simpa [q4S0Final4Start] using hin.2.2.1
  · simpa [q4S0Final4Start] using hin.2.2.2

/-- The q4/S0 postlude is a counted left-one scan followed by the
fixed four-step state-4 return. -/
theorem q4S0Postlude_at (k : Nat) (T : Int → Bool) (h : Int)
    (hones : s0LeftOnes T h k)
    (hright : T (h+1) = false)
    (hguard :
      q4S0Final4Input (s0LeftSweep k T h) (h-(k:Int))) :
    run tm2 (3*k+4) ⟨3,h,T⟩ =
      some (q4FrameAt (s0LeftSweep k T h) (h-(k:Int))
        q4S0Final4Inside q4S0Final4End) := by
  have hscan := state3_left_ones_scan k T h hones hright
  have htail := q4S0Final4_at (s0LeftSweep k T h) (h-(k:Int)) hguard
  calc
    run tm2 (3*k+4) ⟨3,h,T⟩ =
        (run tm2 (3*k) ⟨3,h,T⟩).bind
          (fun d => run tm2 4 d) := by rw [run_append]
    _ = run tm2 4 ⟨3,h-(k:Int),s0LeftSweep k T h⟩ := by
        rw [hscan]
        rfl
    _ = some (q4FrameAt (s0LeftSweep k T h) (h-(k:Int))
          q4S0Final4Inside q4S0Final4End) := htail

#print axioms q4S0Prefix22_at
#print axioms state3_left_one_block
#print axioms state3_left_ones_scan
#print axioms s0LeftSweep_shift
#print axioms q4S0Final4_at
#print axioms q4S0Postlude_at

end BB6Coverage.Agent48Q4S0Macros
