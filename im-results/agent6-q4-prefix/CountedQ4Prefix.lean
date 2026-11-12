import CountedSweep
import CountedResetOddBase
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent6Q4Prefix

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset

/-! The q4 prefix for the m=2, odd-inner-counter Rst2 branch.

The proof is decomposed into:
* a counted left sweep over the 3*a+2 leading ones;
* a fixed 26-step bridge at the translated marker/BinDec boundary;
* an E-state scan over the 3*a shifted ones.

The output is state E at the original head, with the exact q4 right word
1^4 00 1^(3(b+1)) and arbitrary left context.
-/

/-- The exact tape after a left sweep of the specified length. -/
theorem sweptLeft_preserves_left (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : x ≤ h - (n : Int)) :
    sweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero =>
      simp [sweptLeft]
  | succ n ih =>
      rw [sweptLeft]
      have hx' : x ≤ (h - 1) - (n : Int) := by omega
      rw [ih (holeThree T h) (h - 1) x hx']
      have hx0 : x ≠ h := by omega
      have hx1 : x ≠ h + 1 := by omega
      simp [holeThree, hx0, hx1]

/-- The leftmost one consumed by a sweep is left blank. -/
theorem sweptLeft_leftmost (n : Nat) (T : Int → Bool) (h : Int) :
    sweptLeft (n+1) T h (h - (n : Int)) = false := by
  induction n generalizing T h with
  | zero =>
      simp [sweptLeft, holeThree]
  | succ n ih =>
      rw [sweptLeft]
      have heq : h - ((n+1 : Nat) : Int) = (h - 1) - (n : Int) := by omega
      rw [heq]
      exact ih (holeThree T h) (h - 1)

/-- A left sweep never changes cells strictly to the right of h+1. -/
theorem sweptLeft_preserves_right (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : h + 2 ≤ x) :
    sweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero =>
      simp [sweptLeft]
  | succ n ih =>
      rw [sweptLeft]
      have hx' : (h - 1) + 2 ≤ x := by omega
      rw [ih (holeThree T h) (h - 1) x hx']
      have hx0 : x ≠ h := by omega
      have hx1 : x ≠ h + 1 := by omega
      simp [holeThree, hx0, hx1]

/-- The first sweep step sets h+1, and later left sweeps preserve it. -/
theorem sweptLeft_plus1 (n : Nat) (T : Int → Bool) (h : Int) :
    sweptLeft (n+1) T h (h+1) = true := by
  cases n with
  | zero =>
      simp [sweptLeft, holeThree]
  | succ n =>
      rw [sweptLeft]
      have hp := sweptLeft_preserves_right (n+1) (holeThree T h) (h-1) (h+1)
        (by omega)
      rw [hp]
      simp [holeThree]

/-- After at least two left-sweep cells, the original head cell is one. -/
theorem sweptLeft_head (n : Nat) (T : Int → Bool) (h : Int) :
    sweptLeft (n+2) T h h = true := by
  rw [sweptLeft]
  have hp := sweptLeft_plus1 (n+1) (holeThree T h) (h-1)
  have heq : (h-1)+1 = h := by omega
  simpa [heq] using hp

/-- Every swept cell except the leftmost one is one in the output run. -/
theorem sweptLeft_block (N j : Nat) (T : Int → Bool) (h : Int)
    (hj : j+1 < N) :
    sweptLeft N T h (h - (j : Int)) = true := by
  induction N generalizing T h j with
  | zero =>
      omega
  | succ N ih =>
      rw [sweptLeft]
      by_cases hj0 : j = 0
      · subst j
        have hN : 0 < N := by omega
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
        have hp := sweptLeft_plus1 k (holeThree T h) (h-1)
        have heq : (h-1)+1 = h := by omega
        simpa [heq] using hp
      · obtain ⟨j', rfl⟩ : j = j'+1 := by omega
        have hj' : j'+1 < N := by omega
        have hp := ih (holeThree T h) (h-1) j' hj'
        have heq : h - ((j'+1 : Nat) : Int) = (h-1) - (j' : Int) := by omega
        rw [heq]
        exact hp

/-- sideBit on an append, before the first list ends. -/
theorem sideBit_append_left (xs ys : List Bool) (i : Nat)
    (hi : i < xs.length) :
    sideBit (xs ++ ys) i = sideBit xs i := by
  induction xs generalizing i with
  | nil =>
      simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < xs.length := by simp at hi; omega
          simpa [sideBit] using ih ys i hi'

/-- sideBit on an append, after the first list ends. -/
theorem sideBit_append_right (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  induction xs generalizing i with
  | nil =>
      simp [sideBit]
  | cons x xs ih =>
      cases i with
      | zero =>
          simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by simp at hi; omega
          simpa [sideBit] using ih ys i hi'

/-- Every position of d1^a is marked. -/
theorem sideBit_d1pow_true (a i : Nat) (hi : i < 3*a) :
    sideBit (d1pow a) i = true := by
  induction a generalizing i with
  | zero =>
      omega
  | succ a ih =>
      by_cases hi3 : i < 3
      · interval_cases i <;> simp [d1pow, d1, sideBit]
      · have hrem : i-3 < 3*a := by omega
        have heq : i = (i-3)+3 := by omega
        rw [heq]
        simpa [d1pow, d1, sideBit] using ih (i-3) hrem

/-- Remove the leading d1^a word from a source-facing lookup. -/
theorem sideBit_d1pow_append (a i : Nat) (ys : List Bool)
    (hi : 3*a ≤ i) :
    sideBit (d1pow a ++ ys) i = sideBit ys (i-3*a) := by
  have hlen := d1pow_length a
  rw [sideBit_append_right (d1pow a) ys i (by omega), hlen]

/-- The seven source bits immediately beyond d1^a at an odd m=2 reset. -/
theorem s1LeftFacing_q4_bits (L n a : Nat)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    sideBit (s1LeftFacing L n 2 a 0) (3*a+2) = false ∧
    sideBit (s1LeftFacing L n 2 a 0) (3*a+3) = true ∧
    sideBit (s1LeftFacing L n 2 a 0) (3*a+4) = false ∧
    sideBit (s1LeftFacing L n 2 a 0) (3*a+5) = false ∧
    sideBit (s1LeftFacing L n 2 a 0) (3*a+6) = true ∧
    sideBit (s1LeftFacing L n 2 a 0) (3*a+7) = false ∧
    sideBit (s1LeftFacing L n 2 a 0) (3*a+8) = false := by
  have hface : s1LeftFacing L n 2 a 0 =
      d1pow a ++ (markerWord 2 ++ d0 ++ binDec L n ++ lh) := by
    simp [s1LeftFacing, binDec_zero]
  have hbin := binDec_odd_head L n hn hbound
  have hbit : ∀ i, 3*a ≤ i →
      sideBit (s1LeftFacing L n 2 a 0) i =
        sideBit (markerWord 2 ++ d0 ++ binDec L n ++ lh) (i-3*a) := by
    intro i hi
    rw [hface]
    exact sideBit_d1pow_append a i _ hi
  constructor
  · rw [hbit (3*a+2) (by omega)]
    simp [markerWord, sideBit]
  constructor
  · rw [hbit (3*a+3) (by omega)]
    simp [markerWord, sideBit]
  constructor
  · rw [hbit (3*a+4) (by omega)]
    simp [markerWord, d0, sideBit]
  constructor
  · rw [hbit (3*a+5) (by omega)]
    simp [markerWord, d0, sideBit]
  constructor
  · rw [hbit (3*a+6) (by omega)]
    simp [markerWord, d0, sideBit]
  constructor
  · rw [hbit (3*a+7) (by omega)]
    simp [markerWord, d0, sideBit, hbin]
  · rw [hbit (3*a+8) (by omega)]
    simp [markerWord, d0, sideBit, hbin]

/-- The initial S1 left side contains the 3a+2 consecutive ones consumed
by the first counted left sweep. -/
theorem s1Config_q4_leftOnes (L n a b : Nat) (h : Int)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    leftOnes (s1Config L n 2 a 0 b h).tape h (3*a+2) := by
  intro i hi
  rw [s1Config_left_cell]
  have hface : s1LeftFacing L n 2 a 0 =
      d1pow a ++ (markerWord 2 ++ d0 ++ binDec L n ++ lh) := by
    simp [s1LeftFacing, binDec_zero]
  rw [hface]
  by_cases hi0 : i < 3*a
  · rw [sideBit_append_left (d1pow a)
        (markerWord 2 ++ d0 ++ binDec L n ++ lh) i (by
          rw [d1pow_length]
          exact hi0)]
    exact sideBit_d1pow_true a i hi0
  · have hiEq : i = 3*a ∨ i = 3*a+1 := by omega
    rcases hiEq with hiEq | hiEq
    · subst i
      rw [sideBit_d1pow_append a (3*a) _ (by omega)]
      simp [markerWord, sideBit]
    · subst i
      rw [sideBit_d1pow_append a (3*a+1) _ (by omega)]
      simp [markerWord, sideBit]

/-- The q4 local frame interval, relative to its starting head. -/
def q4Inside (x : Int) : Bool := decide (-6 ≤ x ∧ x ≤ 1)

/-- The fixed 26-step bridge from the post-sweep marker boundary to state E. -/
def q4BridgeStart : FConfig := ⟨3,0,[-4,-1]⟩
def q4BridgeEnd : FConfig := ⟨4,2,[1,-1,-4,-5,-6]⟩

theorem q4Bridge_exact :
    fRun tm2 26 q4BridgeStart = some q4BridgeEnd := by decide

theorem q4Bridge_heads :
    (List.range 26).all (fun k =>
      match fRun tm2 k q4BridgeStart with
      | none => true
      | some f => q4Inside f.head) = true := by decide

/-- Recenter a tape at an arbitrary absolute head. -/
def centerTape (T : Int → Bool) (h : Int) : Int → Bool := fun x => T (h+x)

/-- Lift a finite local frame to an arbitrary bi-infinite tape. -/
def frameAt (T : Int → Bool) (h : Int) (inside : Int → Bool)
    (c : FConfig) : Config :=
  shiftConfig h (frame inside (centerTape T h) (embed c))

@[simp] theorem frameAt_state (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) :
    (frameAt T h inside c).state = c.state := rfl

@[simp] theorem frameAt_head (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) :
    (frameAt T h inside c).head = c.head + h := rfl

@[simp] theorem frameAt_tape (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) (x : Int) :
    (frameAt T h inside c).tape x =
      (if inside (x-h) then decide (x-h ∈ c.marked) else T x) := by
  simp [frameAt, frame, shiftConfig, centerTape, embed]

/-- A finite local trace acts on any tape agreeing on its query interval. -/
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

/-- Source-connected arbitrary-background lifting for the fixed bridge. -/
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

/-- Translate a local finite bridge to any absolute tape/head. -/
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

/-- The q4 local bridge input matches the tape after the 3a+2 left sweep. -/
theorem q4Bridge_input_match (L n a b : Nat) (h : Int)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    ∀ y, q4Inside y = true →
      (sweptLeft (3*a+2) (s1Config L n 2 a 0 b h).tape h)
        (h - ((3*a+2 : Nat) : Int) + y) =
          decide (y ∈ q4BridgeStart.marked) := by
  intro y hy
  have hcases : y = -6 ∨ y = -5 ∨ y = -4 ∨ y = -3 ∨
      y = -2 ∨ y = -1 ∨ y = 0 ∨ y = 1 := by
    have hy' : -6 ≤ y ∧ y ≤ 1 := by simpa [q4Inside] using hy
    omega
  rcases s1LeftFacing_q4_bits L n a hn hbound with
    ⟨h2,h3,h4,h5,h6,h7,h8⟩
  have hcell : ∀ i, (s1Config L n 2 a 0 b h).tape (h-(i:Int)) =
      sideBit (s1LeftFacing L n 2 a 0) i := by
    intro i
    exact s1Config_left_cell L n 2 a 0 b h i
  rcases hcases with hy | hy | hy | hy | hy | hy | hy | hy
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+2 : Nat) : Int) - 6) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) - 6 =
        h - ((3*a+8 : Nat) : Int) := by omega
    rw [hp, heq, hcell]
    simpa [q4BridgeStart] using h8
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+2 : Nat) : Int) - 5) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) - 5 =
        h - ((3*a+7 : Nat) : Int) := by omega
    rw [hp, heq, hcell]
    simpa [q4BridgeStart] using h7
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+2 : Nat) : Int) - 4) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) - 4 =
        h - ((3*a+6 : Nat) : Int) := by omega
    rw [hp, heq, hcell]
    simpa [q4BridgeStart] using h6
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+2 : Nat) : Int) - 3) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) - 3 =
        h - ((3*a+5 : Nat) : Int) := by omega
    rw [hp, heq, hcell]
    simpa [q4BridgeStart] using h5
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+2 : Nat) : Int) - 2) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) - 2 =
        h - ((3*a+4 : Nat) : Int) := by omega
    rw [hp, heq, hcell]
    simpa [q4BridgeStart] using h4
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+2 : Nat) : Int) - 1) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) - 1 =
        h - ((3*a+3 : Nat) : Int) := by omega
    rw [hp, heq, hcell]
    simpa [q4BridgeStart] using h3
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+2 : Nat) : Int)) (by omega)
    rw [hp, hcell]
    simpa [q4BridgeStart] using h2
  · subst y
    have hp := sweptLeft_leftmost (3*a+1)
      (s1Config L n 2 a 0 b h).tape h
    have heq : h - ((3*a+2 : Nat) : Int) + 1 =
        h - ((3*a+1 : Nat) : Int) := by omega
    rw [heq, hp]
    simp [q4BridgeStart]

/-- The q4 right-facing word after the head, with the first blank of S1
filled by the left sweep. -/
def q4RightFacing (b : Nat) : List Bool :=
  [true,true,true,true,false,false] ++ d1pow (b+1)

theorem q4RightFacing_succ (b i : Nat) :
    sideBit (q4RightFacing b) (i+1) =
      sideBit (s0RightFacing b) (i+1) := by
  simp [q4RightFacing, s0RightFacing, sideBit]

/-- The source TM63 reaches state E at the same head with the exact q4
right word for every odd n, every a,b, and arbitrary absolute head. -/
theorem oddRst2_q4_prefix (L n a b : Nat) (h : Int)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    ∃ Tq,
      run tm2 (32+12*a) (s1Config L n 2 a 0 b h) =
        some ⟨4,h,Tq⟩ ∧
      Tq h = true ∧
      ∀ i, Tq (h+1+(i:Int)) = sideBit (q4RightFacing b) i := by
  let T := (s1Config L n 2 a 0 b h).tape
  let N := 3*a+2
  let T1 := sweptLeft N T h
  let h' := h - (N : Int)
  let T2 := frameAt T1 h' q4Inside q4BridgeEnd
  have hOn : leftOnes T h N := by
    simpa [N] using s1Config_q4_leftOnes L n a b h hn hbound
  have hr : T (h+1) = false := by
    change (s1Config L n 2 a 0 b h).tape (h+1) = false
    rw [s1Config_right_cell]
    simp [s1PhysicalRight, s0PhysicalRight, s0RightFacing, sideBit]
  have hSweep :
      run tm2 (3*N) ⟨3,h,T⟩ = some ⟨3,h-(N:Int),T1⟩ := by
    simpa [T1] using counted_left_sweep N T h hOn hr
  have hmatch := q4Bridge_input_match L n a b h hn hbound
  have hBridge :
      run tm2 26 ⟨3,h-(N:Int),T1⟩ =
        some ⟨4,h-(3*a:Int),T2⟩ := by
    have hhead : h' + 2 = h - (3*a:Int) := by
      dsimp [h',N]
      omega
    simpa [T2,h',N,hhead] using
      bridgeAt T1 h' q4Inside q4BridgeStart q4BridgeEnd 26 rfl
        q4Bridge_exact q4Bridge_heads hmatch
  have hlinear : linearRightOnes T2 (h-(3*a:Int)) (3*a) := by
    intro i hi
    have hcoord : h-(3*a:Int)+(i:Int) =
        h-((3*a-i : Nat) : Int) := by omega
    have hx : 1 <
        (h-(3*a:Int)+(i:Int))-(h-(N:Int)) := by
      dsimp [N]
      omega
    have hnot : q4Inside
        ((h-(3*a:Int)+(i:Int))-(h-(N:Int))) = false := by
      have hfalse : ¬ (-6 ≤
          (h-(3*a:Int)+(i:Int))-(h-(N:Int)) ∧
          (h-(3*a:Int)+(i:Int))-(h-(N:Int)) ≤ 1) := by omega
      simp [q4Inside,hfalse]
    have hframe : T2 (h-(3*a:Int)+(i:Int)) =
        T1 (h-(3*a:Int)+(i:Int)) := by
      simp only [T2,frameAt_tape]
      simp [hnot]
    have hj : (3*a-i)+1 < N := by dsimp [N]; omega
    have hs : T1 (h-(3*a:Int)+(i:Int)) = true := by
      rw [hcoord]
      exact sweptLeft_block N (3*a-i) T h hj
    rw [hframe]
    exact hs
  have hScan :
      run tm2 (3*a) ⟨4,h-(3*a:Int),T2⟩ = some ⟨4,h,T2⟩ := by
    simpa [show h-(3*a:Int)+(3*a:Int)=h by omega] using
      E_scan T2 (h-(3*a:Int)) (3*a) hlinear
  have h12 :
      run tm2 (3*N+26) ⟨3,h,T⟩ = some ⟨4,h-(3*a:Int),T2⟩ := by
    rw [run_append,hSweep]
    simp only [Option.bind_some]
    exact hBridge
  have htotal :
      run tm2 (3*N+26+3*a) ⟨3,h,T⟩ = some ⟨4,h,T2⟩ := by
    rw [run_append,h12]
    simp only [Option.bind_some]
    exact hScan
  have hcost : 32+12*a = 3*N+26+3*a := by
    dsimp [N]
    omega
  have hheadT : T2 h = true := by
    have hfalse : ¬ (-6 ≤ h-(h-(N:Int)) ∧
        h-(h-(N:Int)) ≤ 1) := by dsimp [N]; omega
    have hnot : q4Inside (h-(h-(N:Int))) = false := by
      simp [q4Inside,hfalse]
    have hs : T1 h = true := by
      simpa [T1,N] using sweptLeft_head (3*a) T h
    simp only [T2,frameAt_tape]
    simp [hnot,hs]
  have hplusT : T2 (h+1) = true := by
    have hfalse : ¬ (-6 ≤ (h+1)-(h-(N:Int)) ∧
        (h+1)-(h-(N:Int)) ≤ 1) := by dsimp [N]; omega
    have hnot : q4Inside ((h+1)-(h-(N:Int))) = false := by
      simp [q4Inside,hfalse]
    have hs : T1 (h+1) = true := by
      simpa [T1,N] using sweptLeft_plus1 (3*a+1) T h
    simp only [T2,frameAt_tape]
    simp [hnot,hs]
  have hrightT : ∀ i, T2 (h+1+(i:Int)) =
      sideBit (q4RightFacing b) i := by
    intro i
    cases i with
    | zero =>
        simpa using hplusT
    | succ i =>
        have xge : h+2 ≤ h+1+((i+1:Int)) := by omega
        have hfalse : ¬ (-6 ≤
            (h+1+((i+1:Int)))-(h-(N:Int)) ∧
            (h+1+((i+1:Int)))-(h-(N:Int)) ≤ 1) := by
          dsimp [N]
          omega
        have hnot : q4Inside
            ((h+1+((i+1:Int)))-(h-(N:Int))) = false := by
          simp [q4Inside,hfalse]
        have hframe : T2 (h+1+((i+1:Int))) =
            T1 (h+1+((i+1:Int))) := by
          simp only [T2,frameAt_tape]
          simp [hnot]
        have hpres : T1 (h+1+((i+1:Int))) =
            T (h+1+((i+1:Int))) := by
          simpa [T1] using
            sweptLeft_preserves_right N T h (h+1+((i+1:Int))) xge
        have hsource :
            T (h+1+((i+1:Int))) =
              sideBit (s0RightFacing b) (i+1) := by
          simpa [T,s1PhysicalRight,s0PhysicalRight] using
            s1Config_right_cell L n 2 a 0 b h (i+1)
        rw [hframe,hpres,hsource]
        exact q4RightFacing_succ b i
  refine ⟨T2, ?_, hheadT, hrightT⟩
  calc
    run tm2 (32+12*a) (s1Config L n 2 a 0 b h)
        = run tm2 (3*N+26+3*a) ⟨3,h,T⟩ := by
            rw [hcost]
            rfl
    _ = some ⟨4,h,T2⟩ := htotal

#print axioms oddRst2_q4_prefix

end BB6Coverage.Agent6Q4Prefix
