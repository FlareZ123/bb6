import CountedSweep
import CountedOddBase
import S1Encoder
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent6Q4Prefix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder

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
      rw [ih (T := holeThree T h) (h := h - 1) hx']
      have hx0 : x ≠ h := by omega
      have hx1 : x ≠ h + 1 := by omega
      simp [holeThree, hx0, hx1]

/-- The leftmost one consumed by a sweep is left blank. -/
theorem sweptLeft_leftmost (n : Nat) (T : Int → Bool) (h : Int) :
    sweptLeft (n+1) T h (h - (n : Int)) = false := by
  induction n generalizing T h with
  | zero =>
      have hne : h ≠ h+1 := by omega
      simp [sweptLeft, holeThree, hne]
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
      rw [ih (holeThree T h) (h - 1) hx']
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
  have hp := sweptLeft_plus1 n (holeThree T h) (h-1)
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
      · obtain ⟨j', hjEq⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        subst j
        have hj' : j'+1 < N := by omega
        have hp := ih j' (holeThree T h) (h-1) hj'
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
          simpa [sideBit] using ih i hi'

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
          simpa [sideBit] using ih i hi'

/-- Every position of d1^a is marked. -/
theorem sideBit_d1pow_true (a i : Nat) (hi : i < 3*a) :
    sideBit (d1pow a) i = true := by
  induction a generalizing i with
  | zero =>
      omega
  | succ a ih =>
      by_cases hi3 : i < 3
      · have hcases : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hcases with h | h | h
        · subst i
          simp [d1pow, d1, sideBit]
        · subst i
          simp [d1pow, d1, sideBit]
        · subst i
          simp [d1pow, d1, sideBit]
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


/-- Canonical q4 left-facing source word, kept local so the prefix proof
has no dependency on the suffix module. -/
def q4LeftFacing (L n a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 1 ++ d0 ++ binDec L n ++ lh

/-- The exact right-half contract consumed by the independent q4 suffix. -/
def q4RightShape (T : Int → Bool) (h : Int) (b : Nat) : Prop :=
  (∀ i : Nat, i<5 → T (h+(i:Int)) = true) ∧
  T (h+5) = false ∧
  T (h+6) = false ∧
  (∀ i : Nat, i<3*(b+1) → T (h+7+(i:Int)) = true) ∧
  (∀ i : Nat, i≤4 → T (h+10+(3*b:Int)+(i:Int)) = false)

/-- Odd BinDec has a d0 head. This local derivation uses only the encoder
recurrence, avoiding the currently broken CountedResetBase dependency. -/
theorem binDec_odd_head_local (L n : Nat)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    binDec L n = d0 ++ binDec (L-1) (n/2) := by
  have hL : 0 < L := by
    cases L with
    | zero =>
        have hn0 : n = 0 := by
          have hsmall : n < 1 := by simpa using hbound
          omega
        simp [hn0] at hn
    | succ L => omega
  have hLid : L = (L-1)+1 := by omega
  have hpow : 2^L = 2^(L-1)*2 := by
    calc
      2^L = 2^((L-1)+1) := by congr 1 <;> omega
      _ = 2^(L-1)*2 := by rw [Nat.pow_succ]
  have hq : n/2 < 2^(L-1) := by
    have hb' : n < 2^(L-1)*2 := by simpa [hpow] using hbound
    omega
  have hnEq : n = 2*(n/2)+1 := by omega
  calc
    binDec L n = binDec ((L-1)+1) (2*(n/2)+1) := by
      congr 1 <;> omega
    _ = d0 ++ binDec (L-1) (n/2) :=
      binDec_odd (L-1) (n/2) hq

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
  have hbin := binDec_odd_head_local L n hn hbound
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
    simp [markerWord, d0, d1, sideBit, hbin]
  · rw [hbit (3*a+8) (by omega)]
    simp [markerWord, d0, d1, sideBit, hbin]

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

theorem config_ext {c d : Config}
    (hs : c.state = d.state) (hh : c.head = d.head)
    (ht : c.tape = d.tape) : c = d := by
  cases c with
  | mk cs ch ct =>
    cases d with
    | mk ds dh dt =>
      simp only at hs hh ht
      cases hs
      cases hh
      cases ht
      rfl

@[simp] theorem frameAt_tape (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) (x : Int) :
    (frameAt T h inside c).tape x =
      (if inside (x-h) then decide (x-h ∈ c.marked) else T x) := by
  have hcoord : h + (x-h) = x := by omega
  simp [frameAt, frame, shiftConfig, centerTape, embed, hcoord]

theorem frameAt_tape_outside (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) (x : Int)
    (hout : inside (x-h) = false) :
    (frameAt T h inside c).tape x = T x := by
  simp [frameAt_tape, hout]

theorem frameAt_tape_inside (T : Int → Bool) (h : Int)
    (inside : Int → Bool) (c : FConfig) (x : Int)
    (hin : inside (x-h) = true) :
    (frameAt T h inside c).tape x = decide (x-h ∈ c.marked) := by
  simp [frameAt_tape, hin]

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
      apply config_ext
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
    apply config_ext
    · rfl
    · simp [shiftConfig]
    · funext x
      have hcoord : h + (x-h) = x := by omega
      simp [shiftConfig, centerTape, hcoord]
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
  have hcell : ∀ i : Nat, (s1Config L n 2 a 0 b h).tape (h-(i:Int)) =
      sideBit (s1LeftFacing L n 2 a 0) i := by
    intro i
    exact s1Config_left_cell L n 2 a 0 b h i
  rcases hcases with hy | hy | hy | hy | hy | hy | hy | hy
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+8 : Nat) : Int)) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) + (-6) =
        h - ((3*a+8 : Nat) : Int) := by omega
    rw [heq,hp,hcell]
    simpa [q4BridgeStart] using h8
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+7 : Nat) : Int)) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) + (-5) =
        h - ((3*a+7 : Nat) : Int) := by omega
    rw [heq, hp, hcell]
    simpa [q4BridgeStart] using h7
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+6 : Nat) : Int)) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) + (-4) =
        h - ((3*a+6 : Nat) : Int) := by omega
    rw [heq, hp, hcell]
    simpa [q4BridgeStart] using h6
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+5 : Nat) : Int)) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) + (-3) =
        h - ((3*a+5 : Nat) : Int) := by omega
    rw [heq, hp, hcell]
    simpa [q4BridgeStart] using h5
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+4 : Nat) : Int)) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) + (-2) =
        h - ((3*a+4 : Nat) : Int) := by omega
    rw [heq, hp, hcell]
    simpa [q4BridgeStart] using h4
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+3 : Nat) : Int)) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) + (-1) =
        h - ((3*a+3 : Nat) : Int) := by omega
    rw [heq, hp, hcell]
    simpa [q4BridgeStart] using h3
  · subst y
    have hp := sweptLeft_preserves_left (3*a+2)
      (s1Config L n 2 a 0 b h).tape h
      (h - ((3*a+2 : Nat) : Int)) (by omega)
    have heq : h - ((3*a+2 : Nat) : Int) + 0 =
        h - ((3*a+2 : Nat) : Int) := by omega
    rw [heq,hp,hcell]
    simpa [q4BridgeStart] using h2
  · subst y
    have hlen : 3*a+2 = (3*a+1)+1 := by omega
    rw [hlen]
    have hp := sweptLeft_leftmost (3*a+1)
      (s1Config L n 2 a 0 b h).tape h
    have heq : h - (((3*a+1)+1 : Nat) : Int) + 1 =
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

/-- For odd n, the binary counter for n-1 begins with d1 and has the
same remaining suffix as the counter for n after its leading d0 block. -/
theorem binDec_odd_predecessor_head (L n : Nat)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    binDec L (n-1) = d1 ++ binDec (L-1) (n/2) := by
  have hL : 0 < L := by
    cases L with
    | zero =>
        have hn0 : n = 0 := by
          have hsmall : n < 1 := by simpa using hbound
          omega
        simp [hn0] at hn
    | succ L => omega
  have hLid : L = (L-1)+1 := by omega
  have hpow : 2^L = 2^(L-1)*2 := by
    calc
      2^L = 2^((L-1)+1) := by congr 1 <;> omega
      _ = 2^(L-1)*2 := by rw [Nat.pow_succ]
  have hq : n/2 < 2^(L-1) := by
    have hb' : n < 2^(L-1)*2 := by simpa [hpow] using hbound
    omega
  have hnEq : n-1 = 2*(n/2) := by omega
  calc
    binDec L (n-1) = binDec ((L-1)+1) (2*(n/2)) := by
      congr 1 <;> omega
    _ = d1 ++ binDec (L-1) (n/2) :=
      binDec_even (L-1) (n/2) hq

/-- The eight-cell marker/counter boundary in the q4 left-facing word. -/
theorem q4LeftFacing_mid_bits (L n a : Nat)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    sideBit (q4LeftFacing L (n-1) a) (3*a+1) = true ∧
    sideBit (q4LeftFacing L (n-1) a) (3*a+2) = false ∧
    sideBit (q4LeftFacing L (n-1) a) (3*a+3) = true ∧
    sideBit (q4LeftFacing L (n-1) a) (3*a+4) = false ∧
    sideBit (q4LeftFacing L (n-1) a) (3*a+5) = false ∧
    sideBit (q4LeftFacing L (n-1) a) (3*a+6) = true ∧
    sideBit (q4LeftFacing L (n-1) a) (3*a+7) = true ∧
    sideBit (q4LeftFacing L (n-1) a) (3*a+8) = true := by
  have hface : q4LeftFacing L (n-1) a =
      ([true] ++ d1pow a) ++
        (markerWord 1 ++ d0 ++ binDec L (n-1) ++ lh) := by
    simp [q4LeftFacing, List.append_assoc]
  have hlen : ([true] ++ d1pow a).length = 3*a+1 := by
    simp [d1pow_length]
  have hbin := binDec_odd_predecessor_head L n hn hbound
  have hbit : ∀ i, 3*a+1 ≤ i →
      sideBit (q4LeftFacing L (n-1) a) i =
        sideBit (markerWord 1 ++ d0 ++ binDec L (n-1) ++ lh)
          (i-(3*a+1)) := by
    intro i hi
    rw [hface]
    simpa [hlen] using
      sideBit_append_right ([true] ++ d1pow a)
        (markerWord 1 ++ d0 ++ binDec L (n-1) ++ lh) i (by
          rw [hlen]
          exact hi)
  constructor
  · rw [hbit (3*a+1) (by omega)]
    simp [markerWord, sideBit]
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
    simp [markerWord, d0, d1, sideBit, hbin]
  · rw [hbit (3*a+8) (by omega)]
    simp [markerWord, d0, d1, sideBit, hbin]

def q4SourcePrefix (a : Nat) : List Bool :=
  d1pow a ++ markerWord 2 ++ d0 ++ d0

def q4TargetPrefix (a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 1 ++ d0 ++ d1

def q4SharedTail (L n : Nat) : List Bool :=
  binDec (L-1) (n/2) ++ lh

/-- Beyond the two changed low-order counter bits, the source and q4
left-facing words have exactly the same suffix. -/
theorem q4LeftFacing_source_tail (L n a i : Nat)
    (hn : n % 2 = 1) (hbound : n < 2^L)
    (hi : 3*a+9 ≤ i) :
    sideBit (s1LeftFacing L n 2 a 0) i =
      sideBit (q4LeftFacing L (n-1) a) i := by
  have hsrc : s1LeftFacing L n 2 a 0 =
      q4SourcePrefix a ++ q4SharedTail L n := by
    unfold s1LeftFacing
    rw [binDec_zero a, binDec_odd_head_local L n hn hbound]
    simp [q4SourcePrefix, q4SharedTail, List.append_assoc]
  have htgt : q4LeftFacing L (n-1) a =
      q4TargetPrefix a ++ q4SharedTail L n := by
    unfold q4LeftFacing
    rw [binDec_odd_predecessor_head L n hn hbound]
    simp [q4TargetPrefix, q4SharedTail, List.append_assoc]
  have hlenS : (q4SourcePrefix a).length = 3*a+10 := by
    simp [q4SourcePrefix, d1pow_length, markerWord, d0]
  have hlenT : (q4TargetPrefix a).length = 3*a+10 := by
    simp [q4TargetPrefix, d1pow_length, markerWord, d0, d1]
  have hsrcLast : sideBit (q4SourcePrefix a) (3*a+9) = true := by
    simp only [q4SourcePrefix, List.append_assoc]
    rw [sideBit_d1pow_append a (3*a+9) (markerWord 2 ++ (d0 ++ d0)) (by omega)]
    have hidx : 3*a+9-3*a = 9 := by omega
    rw [hidx]
    have h1 : sideBit (markerWord 2 ++ (d0 ++ d0)) 9 =
        sideBit (d0 ++ d0) 5 := by
      exact sideBit_append_right (markerWord 2) (d0 ++ d0) 9 (by
        simp [markerWord])
    rw [h1]
    have h2 : sideBit (d0 ++ d0) 5 = sideBit d0 2 := by
      exact sideBit_append_right d0 d0 5 (by simp [d0])
    rw [h2]
    simp [d0, sideBit]
  have htgtLast : sideBit (q4TargetPrefix a) (3*a+9) = true := by
    simp only [q4TargetPrefix, List.append_assoc]
    have h0 := sideBit_append_right [true]
      (d1pow a ++ (markerWord 1 ++ (d0 ++ d1))) (3*a+9) (by simp)
    have hidx0 : 3*a+9 - [true].length = 3*a+8 := by simp; omega
    rw [hidx0] at h0
    rw [h0]
    rw [sideBit_d1pow_append a (3*a+8) (markerWord 1 ++ (d0 ++ d1)) (by omega)]
    have hidx1 : 3*a+8-3*a = 8 := by omega
    rw [hidx1]
    have h1 : sideBit (markerWord 1 ++ (d0 ++ d1)) 8 =
        sideBit (d0 ++ d1) 5 := by
      exact sideBit_append_right (markerWord 1) (d0 ++ d1) 8 (by
        simp [markerWord])
    rw [h1]
    have h2 : sideBit (d0 ++ d1) 5 = sideBit d1 2 := by
      exact sideBit_append_right d0 d1 5 (by simp [d0])
    rw [h2]
    simp [d1, sideBit]
  by_cases hlast : i = 3*a+9
  · subst i
    rw [hsrc, htgt]
    have hs : sideBit (q4SourcePrefix a ++ q4SharedTail L n)
        (3*a+9) = true := by
      rw [sideBit_append_left (q4SourcePrefix a) (q4SharedTail L n)
        (3*a+9) (by rw [hlenS]; omega)]
      exact hsrcLast
    have ht : sideBit (q4TargetPrefix a ++ q4SharedTail L n)
        (3*a+9) = true := by
      rw [sideBit_append_left (q4TargetPrefix a) (q4SharedTail L n)
        (3*a+9) (by rw [hlenT]; omega)]
      exact htgtLast
    rw [hs, ht]
  · have hi' : 3*a+10 ≤ i := by omega
    rw [hsrc, htgt]
    rw [sideBit_append_right (q4SourcePrefix a) (q4SharedTail L n) i
      (by rw [hlenS]; omega)]
    rw [sideBit_append_right (q4TargetPrefix a) (q4SharedTail L n) i
      (by rw [hlenT]; omega)]
    rw [hlenS, hlenT]

/-- sideBit is blank beyond the finite word. -/
theorem sideBit_ge_length (xs : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit xs i = false := by
  induction xs generalizing i with
  | nil =>
      simp [sideBit]
  | cons x xs ih =>
      cases i with
      | zero =>
          simp at hi
      | succ i =>
          have hi' : xs.length ≤ i := by simp at hi; omega
          simpa [sideBit] using ih i hi'

theorem q4RightFacing_length (b : Nat) :
    (q4RightFacing b).length = 9+3*b := by
  simp [q4RightFacing, d1pow_length]
  omega

theorem q4RightFacing_first4 (b i : Nat) (hi : i < 4) :
    sideBit (q4RightFacing b) i = true := by
  have hcases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hcases with h0 | h1 | h2 | h3 <;> subst i <;>
    simp [q4RightFacing, sideBit]

theorem q4RightFacing_at4 (b : Nat) :
    sideBit (q4RightFacing b) 4 = false := by
  simp [q4RightFacing, sideBit]

theorem q4RightFacing_at5 (b : Nat) :
    sideBit (q4RightFacing b) 5 = false := by
  simp [q4RightFacing, sideBit]

theorem q4RightFacing_suffix (b i : Nat) (hi : i < 3*(b+1)) :
    sideBit (q4RightFacing b) (6+i) = true := by
  change sideBit ([true,true,true,true,false,false] ++ d1pow (b+1))
    (6+i) = true
  have happ := sideBit_append_right
    [true,true,true,true,false,false] (d1pow (b+1)) (6+i) (by simp)
  have hlen : ([true,true,true,true,false,false] : List Bool).length = 6 := by simp
  rw [hlen] at happ
  have hidx : 6+i-6 = i := by omega
  rw [hidx] at happ
  exact happ.trans (sideBit_d1pow_true (b+1) i hi)

theorem oddRst2_q4_prefix (L n a b : Nat) (h : Int)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    ∃ Tq,
      run tm2 (32+12*a) (s1Config L n 2 a 0 b h) =
        some ⟨4,h,Tq⟩ ∧
      Tq h = true ∧
      (∀ i : Nat, Tq (h-(i:Int)) = sideBit (q4LeftFacing L (n-1) a) i) ∧
      q4RightShape Tq h b := by
  let T := (s1Config L n 2 a 0 b h).tape
  let N := 3*a+2
  let T1 := sweptLeft N T h
  let h' := h - (N : Int)
  let T2 := (frameAt T1 h' q4Inside q4BridgeEnd).tape
  have hOn : leftOnes T h N := by
    simpa [N] using s1Config_q4_leftOnes L n a b h hn hbound
  have hr : T (h+1) = false := by
    have hright0 := s1Config_right_cell L n 2 a 0 b h 0
    simpa [T,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hright0
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
    have hb := bridgeAt T1 h' q4Inside q4BridgeStart q4BridgeEnd 26 rfl
      q4Bridge_exact q4Bridge_heads hmatch
    simpa [T2,h',N,q4BridgeStart,q4BridgeEnd,hhead] using hb
  have hlinear : linearRightOnes T2 (h-(3*a:Int)) (3*a) := by
    intro i hi
    have hcoord : h-(3*a:Int)+(i:Int) =
        h-((3*a-i : Nat) : Int) := by omega
    have hrel : (h-(3*a:Int)+(i:Int))-h' = 2+(i:Int) := by
      dsimp [h',N]
      omega
    have hnot : q4Inside ((h-(3*a:Int)+(i:Int))-h') = false := by
      simp [q4Inside,hrel]
      omega
    have hframe : T2 (h-(3*a:Int)+(i:Int)) =
        T1 (h-(3*a:Int)+(i:Int)) := by
      dsimp [T2]
      exact frameAt_tape_outside T1 h' q4Inside q4BridgeEnd
        (h-(3*a:Int)+(i:Int)) hnot
    have hj : (3*a-i)+1 < N := by dsimp [N]; omega
    have hs : T1 (h-(3*a:Int)+(i:Int)) = true := by
      rw [hcoord]
      exact sweptLeft_block N (3*a-i) T h hj
    exact hframe.trans hs
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
    have hrel : h-h' = (N:Int) := by dsimp [h',N]; omega
    have hnot : q4Inside (h-h') = false := by
      simp [q4Inside,hrel,N]
      omega
    have hframe : T2 h = T1 h := by
      dsimp [T2]
      exact frameAt_tape_outside T1 h' q4Inside q4BridgeEnd h hnot
    have hs : T1 h = true := by
      simpa [T1,N] using sweptLeft_head (3*a) T h
    exact hframe.trans hs
  have hplusT : T2 (h+1) = true := by
    have hrel : (h+1)-h' = (N:Int)+1 := by dsimp [h',N]; omega
    have hnot : q4Inside ((h+1)-h') = false := by
      simp [q4Inside,hrel,N]
      omega
    have hframe : T2 (h+1) = T1 (h+1) := by
      dsimp [T2]
      exact frameAt_tape_outside T1 h' q4Inside q4BridgeEnd (h+1) hnot
    have hs : T1 (h+1) = true := by
      simpa [T1,N] using sweptLeft_plus1 (3*a+1) T h
    exact hframe.trans hs
  have hrightT : ∀ i : Nat, T2 (h+1+(i:Int)) =
      sideBit (q4RightFacing b) i := by
    intro i
    cases i with
    | zero =>
        simpa [q4RightFacing,sideBit] using hplusT
    | succ i =>
        let x : Int := h+1+((i+1:Int))
        have hrel : x-h' = (N:Int)+2+(i:Int) := by
          dsimp [x,h',N]
          omega
        have hnot : q4Inside (x-h') = false := by
          simp [q4Inside,hrel,N]
          omega
        have hframe : T2 x = T1 x := by
          dsimp [T2]
          exact frameAt_tape_outside T1 h' q4Inside q4BridgeEnd x hnot
        have hpres : T1 x = T x := by
          simpa [T1] using
            sweptLeft_preserves_right N T h x (by dsimp [x]; omega)
        have hsource : T x = sideBit (s0RightFacing b) (i+1) := by
          simpa [T,s1PhysicalRight,s0PhysicalRight] using
            s1Config_right_cell L n 2 a 0 b h (i+1)
        calc
          T2 (h+1+((i+1:Int))) = T2 x := by rfl
          _ = T1 x := hframe
          _ = T x := hpres
          _ = sideBit (s0RightFacing b) (i+1) := hsource
          _ = sideBit (q4RightFacing b) (i+1) :=
            (q4RightFacing_succ b i).symm
  have hleftT : ∀ i : Nat, T2 (h-(i:Int)) =
      sideBit (q4LeftFacing L (n-1) a) i := by
    intro i
    by_cases hi0 : i = 0
    · subst i
      simpa [q4LeftFacing,sideBit] using hheadT
    · by_cases hiblock : i ≤ 3*a
      · let x : Int := h-(i:Int)
        have hrel : x-h' = (N:Int)-(i:Int) := by dsimp [x,h',N]; omega
        have hnot : q4Inside (x-h') = false := by
          simp [q4Inside,hrel]
          omega
        have hframe : T2 x = T1 x := by
          dsimp [T2]
          exact frameAt_tape_outside T1 h' q4Inside q4BridgeEnd x hnot
        have hj : i+1 < N := by dsimp [N]; omega
        have hs : T1 x = true := by
          dsimp [x]
          exact sweptLeft_block N i T h hj
        have hprefix : sideBit (q4LeftFacing L (n-1) a) i =
            sideBit (d1pow a ++ (markerWord 1 ++ (d0 ++
              (binDec L (n-1) ++ lh)))) (i-1) := by
          simpa only [q4LeftFacing,List.append_assoc] using
            sideBit_append_right [true]
              (d1pow a ++ (markerWord 1 ++ (d0 ++
                (binDec L (n-1) ++ lh)))) i (by simp; omega)
        have hi' : i-1 < 3*a := by omega
        have htarget : sideBit (q4LeftFacing L (n-1) a) i = true := by
          rw [hprefix]
          have happ := sideBit_append_left (d1pow a)
            (markerWord 1 ++ (d0 ++ (binDec L (n-1) ++ lh)))
            (i-1) (by rw [d1pow_length]; exact hi')
          exact happ.trans (sideBit_d1pow_true a (i-1) hi')
        calc
          T2 x = T1 x := hframe
          _ = true := hs
          _ = sideBit (q4LeftFacing L (n-1) a) i := htarget.symm
      · by_cases himid : i ≤ 3*a+8
        · have hcases : i=3*a+1 ∨ i=3*a+2 ∨ i=3*a+3 ∨
              i=3*a+4 ∨ i=3*a+5 ∨ i=3*a+6 ∨
              i=3*a+7 ∨ i=3*a+8 := by omega
          rcases q4LeftFacing_mid_bits L n a hn hbound with
            ⟨hq1,hq2,hq3,hq4,hq5,hq6,hq7,hq8⟩
          rcases hcases with hc1 | hc2 | hc3 | hc4 | hc5 | hc6 | hc7 | hc8
          · subst i
            have hrel : (h-((3*a+1:Int)))-h' = 1 := by
              dsimp [h',N]
              omega
            have hinside : q4Inside ((h-((3*a+1:Int)))-h') = true := by
              simp [q4Inside,hrel]
            have hframe : T2 (h-((3*a+1:Int))) = true := by
              have hv := frameAt_tape_inside T1 h' q4Inside q4BridgeEnd
                (h-((3*a+1:Int))) hinside
              simpa [T2,q4BridgeEnd,hrel] using hv
            exact hframe.trans hq1.symm
          · subst i
            have hrel : (h-((3*a+2:Int)))-h' = 0 := by
              dsimp [h',N]
              omega
            have hinside : q4Inside ((h-((3*a+2:Int)))-h') = true := by
              simp [q4Inside,hrel]
            have hframe : T2 (h-((3*a+2:Int))) = false := by
              have hv := frameAt_tape_inside T1 h' q4Inside q4BridgeEnd
                (h-((3*a+2:Int))) hinside
              simpa [T2,q4BridgeEnd,hrel] using hv
            exact hframe.trans hq2.symm
          · subst i
            have hrel : (h-((3*a+3:Int)))-h' = -1 := by
              dsimp [h',N]
              omega
            have hinside : q4Inside ((h-((3*a+3:Int)))-h') = true := by
              simp [q4Inside,hrel]
            have hframe : T2 (h-((3*a+3:Int))) = true := by
              have hv := frameAt_tape_inside T1 h' q4Inside q4BridgeEnd
                (h-((3*a+3:Int))) hinside
              simpa [T2,q4BridgeEnd,hrel] using hv
            exact hframe.trans hq3.symm
          · subst i
            have hrel : (h-((3*a+4:Int)))-h' = -2 := by
              dsimp [h',N]
              omega
            have hinside : q4Inside ((h-((3*a+4:Int)))-h') = true := by
              simp [q4Inside,hrel]
            have hframe : T2 (h-((3*a+4:Int))) = false := by
              have hv := frameAt_tape_inside T1 h' q4Inside q4BridgeEnd
                (h-((3*a+4:Int))) hinside
              simpa [T2,q4BridgeEnd,hrel] using hv
            exact hframe.trans hq4.symm
          · subst i
            have hrel : (h-((3*a+5:Int)))-h' = -3 := by
              dsimp [h',N]
              omega
            have hinside : q4Inside ((h-((3*a+5:Int)))-h') = true := by
              simp [q4Inside,hrel]
            have hframe : T2 (h-((3*a+5:Int))) = false := by
              have hv := frameAt_tape_inside T1 h' q4Inside q4BridgeEnd
                (h-((3*a+5:Int))) hinside
              simpa [T2,q4BridgeEnd,hrel] using hv
            exact hframe.trans hq5.symm
          · subst i
            have hrel : (h-((3*a+6:Int)))-h' = -4 := by
              dsimp [h',N]
              omega
            have hinside : q4Inside ((h-((3*a+6:Int)))-h') = true := by
              simp [q4Inside,hrel]
            have hframe : T2 (h-((3*a+6:Int))) = true := by
              have hv := frameAt_tape_inside T1 h' q4Inside q4BridgeEnd
                (h-((3*a+6:Int))) hinside
              simpa [T2,q4BridgeEnd,hrel] using hv
            exact hframe.trans hq6.symm
          · subst i
            have hrel : (h-((3*a+7:Int)))-h' = -5 := by
              dsimp [h',N]
              omega
            have hinside : q4Inside ((h-((3*a+7:Int)))-h') = true := by
              simp [q4Inside,hrel]
            have hframe : T2 (h-((3*a+7:Int))) = true := by
              have hv := frameAt_tape_inside T1 h' q4Inside q4BridgeEnd
                (h-((3*a+7:Int))) hinside
              simpa [T2,q4BridgeEnd,hrel] using hv
            exact hframe.trans hq7.symm
          · subst i
            have hrel : (h-((3*a+8:Int)))-h' = -6 := by
              dsimp [h',N]
              omega
            have hinside : q4Inside ((h-((3*a+8:Int)))-h') = true := by
              simp [q4Inside,hrel]
            have hframe : T2 (h-((3*a+8:Int))) = true := by
              have hv := frameAt_tape_inside T1 h' q4Inside q4BridgeEnd
                (h-((3*a+8:Int))) hinside
              simpa [T2,q4BridgeEnd,hrel] using hv
            exact hframe.trans hq8.symm
        · let x : Int := h-(i:Int)
          have htailbound : 3*a+9 ≤ i := by omega
          have hrel : x-h' = (N:Int)-(i:Int) := by dsimp [x,h',N]; omega
          have hnot : q4Inside (x-h') = false := by
            simp [q4Inside,hrel]
            omega
          have hframe : T2 x = T1 x := by
            dsimp [T2]
            exact frameAt_tape_outside T1 h' q4Inside q4BridgeEnd x hnot
          have hpres : T1 x = T x := by
            simpa [T1] using
              sweptLeft_preserves_left N T h x (by dsimp [x,N]; omega)
          have hcell : T x = sideBit (s1LeftFacing L n 2 a 0) i := by
            simpa [T] using s1Config_left_cell L n 2 a 0 b h i
          have htail := q4LeftFacing_source_tail L n a i hn hbound htailbound
          calc
            T2 x = T1 x := hframe
            _ = T x := hpres
            _ = sideBit (s1LeftFacing L n 2 a 0) i := hcell
            _ = sideBit (q4LeftFacing L (n-1) a) i := htail
  have hshape : q4RightShape T2 h b := by
    unfold q4RightShape
    constructor
    · intro i hi
      by_cases hi0 : i = 0
      · subst i
        simpa using hheadT
      · have hidx : i-1 < 4 := by omega
        have hq : sideBit (q4RightFacing b) (i-1) = true :=
          q4RightFacing_first4 b (i-1) hidx
        have hr := hrightT (i-1)
        have heq : h+1+((i-1:Int)) = h+(i:Int) := by omega
        calc
          T2 (h+(i:Int)) = T2 (h+1+((i-1:Int))) := by rw [heq]
          _ = sideBit (q4RightFacing b) (i-1) := hr
          _ = true := hq
    · constructor
      · have hr := hrightT 4
        rw [q4RightFacing_at4] at hr
        have heq : h+1+(4:Int) = h+5 := by omega
        simpa [heq] using hr
      · constructor
        · have hr := hrightT 5
          rw [q4RightFacing_at5] at hr
          have heq : h+1+(5:Int) = h+6 := by omega
          simpa [heq] using hr
        · constructor
          · intro i hi
            have hq := q4RightFacing_suffix b i hi
            have hr := hrightT (6+i)
            rw [hq] at hr
            have heq : h+1+((6+i:Int)) = h+7+(i:Int) := by omega
            simpa [heq] using hr
          · intro i hi
            have hq : sideBit (q4RightFacing b) (9+3*b+i) = false := by
              apply sideBit_ge_length
              rw [q4RightFacing_length]
              omega
            have hr := hrightT (9+3*b+i)
            rw [hq] at hr
            have heq : h+1+((9+3*b+i:Int)) =
                h+10+(3*b:Int)+(i:Int) := by omega
            simpa [heq] using hr
  refine ⟨T2, ?_, hheadT, hleftT, hshape⟩
  calc
    run tm2 (32+12*a) (s1Config L n 2 a 0 b h)
        = run tm2 (3*N+26+3*a) ⟨3,h,T⟩ := by
            rw [hcost]
            rfl
    _ = some ⟨4,h,T2⟩ := htotal

#print axioms oddRst2_q4_prefix

end BB6Coverage.Agent6Q4Prefix
