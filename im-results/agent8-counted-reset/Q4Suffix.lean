import CountedRst1Prime
import Lean.Elab.Tactic.Omega

/-!
# TM63 Rst2 q4 suffix: source-connected counted frame composition

This formalizes the q4/head-0 suffix discovered in
`agent24-champion-time/LCIncQ4Cut.md`.  It is an original-infinite-tape
run theorem, not a finite-tape extrapolation.

The suffix is split into:
* 10 fixed moves from state E/head 0 to state B/head 10;
* 3 moves per extra three-one block, scanning in states B/F/C;
* a fixed 29-move framed tail from state B, whose read window is [-4,4].

The q4 prefix-to-cut theorem is deliberately not assumed here.  The input
hypothesis `q4RightShape` is the exact right-half condition the prefix must
supply; the left exterior is arbitrary.
-/

namespace BB6Coverage.Agent8Q4Suffix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent8Rst1Prime

/-- The fixed first ten moves only inspect cells 0 through 9. -/
def q4First10Inside (x : Int) : Bool :=
  decide (0 ≤ x ∧ x ≤ 9)

def q4First10Start : FConfig :=
  ⟨4, 0, [0,1,2,3,4,7,8,9]⟩

def q4First10End : FConfig :=
  ⟨1, 10, [5,6,9]⟩

theorem q4First10_exact :
    fRun tm2 10 q4First10Start = some q4First10End := by
  decide

theorem q4First10_heads :
    (List.range 10).all (fun k =>
      match fRun tm2 k q4First10Start with
      | none => true
      | some f => q4First10Inside f.head) = true := by
  decide

/-- The ten-step q4 prefix is valid with arbitrary tape exterior. -/
theorem q4First10_at (T : Int → Bool) (h : Int)
    (h0 : ∀ i : Nat, i < 5 → T (h+(i:Int)) = true)
    (h56 : T (h+5) = false ∧ T (h+6) = false)
    (h79 : ∀ i : Nat, i < 3 → T (h+7+(i:Int)) = true) :
    run tm2 10 ⟨4,h,T⟩ =
      some (frameAt T h q4First10Inside q4First10End) := by
  apply bridgeAt T h q4First10Inside q4First10Start q4First10End 10 rfl
    q4First10_exact q4First10_heads
  intro x hx
  have hrange : 0 ≤ x ∧ x ≤ 9 := by
    simpa [q4First10Inside] using hx
  have hcases :
      x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 ∨
      x=5 ∨ x=6 ∨ x=7 ∨ x=8 ∨ x=9 := by omega
  rcases hcases with hx0|hx1|hx2|hx3|hx4|hx5|hx6|hx7|hx8|hx9 <;> subst x
  · simpa [q4First10Start] using h0 0 (by omega)
  · simpa [q4First10Start] using h0 1 (by omega)
  · simpa [q4First10Start] using h0 2 (by omega)
  · simpa [q4First10Start] using h0 3 (by omega)
  · simpa [q4First10Start] using h0 4 (by omega)
  · simpa [q4First10Start] using h56.1
  · simpa [q4First10Start] using h56.2
  · simpa [q4First10Start] using h79 0 (by omega)
  · simpa [q4First10Start] using h79 1 (by omega)
  · simpa [q4First10Start] using h79 2 (by omega)

/-- After the first ten moves, the five-cell q4 output is fixed. -/
theorem q4First10_cells (T : Int → Bool) (h : Int) :
    (frameAt T h q4First10Inside q4First10End).tape (h+5) = true ∧
    (frameAt T h q4First10Inside q4First10End).tape (h+6) = true ∧
    (frameAt T h q4First10Inside q4First10End).tape (h+7) = false ∧
    (frameAt T h q4First10Inside q4First10End).tape (h+8) = false ∧
    (frameAt T h q4First10Inside q4First10End).tape (h+9) = true := by
  have h5 : (frameAt T h q4First10Inside q4First10End).tape (h+5) = true := by
    rw [frameAt_tape]
    have heq : (h+5)-h = 5 := by omega
    rw [heq]
    simp [q4First10Inside,q4First10End]
  have h6 : (frameAt T h q4First10Inside q4First10End).tape (h+6) = true := by
    rw [frameAt_tape]
    have heq : (h+6)-h = 6 := by omega
    rw [heq]
    simp [q4First10Inside,q4First10End]
  have h7 : (frameAt T h q4First10Inside q4First10End).tape (h+7) = false := by
    rw [frameAt_tape]
    have heq : (h+7)-h = 7 := by omega
    rw [heq]
    simp [q4First10Inside,q4First10End]
  have h8 : (frameAt T h q4First10Inside q4First10End).tape (h+8) = false := by
    rw [frameAt_tape]
    have heq : (h+8)-h = 8 := by omega
    rw [heq]
    simp [q4First10Inside,q4First10End]
  have h9 : (frameAt T h q4First10Inside q4First10End).tape (h+9) = true := by
    rw [frameAt_tape]
    have heq : (h+9)-h = 9 := by omega
    rw [heq]
    simp [q4First10Inside,q4First10End]
  exact ⟨h5,h6,h7,h8,h9⟩

private theorem q4First10_preserves_after (T : Int → Bool) (h y : Int)
    (hy : h+10 ≤ y) :
    (frameAt T h q4First10Inside q4First10End).tape y = T y := by
  rw [frameAt_tape]
  have hnot : ¬ (0 ≤ y-h ∧ y-h ≤ 9) := by omega
  simp [q4First10Inside,hnot]

/-- A state-1 head scans one three-one block in exactly three moves.
The physical output block is 001 and the head advances three cells. -/
def afterD1Block (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x =>
    if x=h then false
    else if x=h+1 then false
    else if x=h+2 then true
    else T x

theorem state1_one_d1_block (T : Int → Bool) (h : Int)
    (h0 : T h = true) (h1 : T (h+1) = true) (h2 : T (h+2) = true) :
    run tm2 3 ⟨1,h,T⟩ =
      some ⟨1,h+3,afterD1Block T h⟩ := by
  have t1 : tm2 ((1:Fin 6),true) = some ⟨false,true,5⟩ := rfl
  have t5 : tm2 ((5:Fin 6),true) = some ⟨false,true,3⟩ := rfl
  have t3 : tm2 ((3:Fin 6),true) = some ⟨true,true,1⟩ := rfl
  have neq1 : h+1 ≠ h := by omega
  have neq2 : h+2 ≠ h := by omega
  have neq3 : h+2 ≠ h+1 := by omega
  have hh : h+1+1 = h+2 := by omega
  have neh1 : h ≠ h+1 := by omega
  have neh2 : h ≠ h+2 := by omega
  simp [run,rawStep,readSlot,applyMove,h0,h1,h2,hh,t1,t5,t3,
    neq1,neq2,neq3]
  constructor
  · omega
  · funext x
    by_cases hx1 : x=h+1 <;> by_cases hx2 : x=h+2 <;>
      by_cases hx0 : x=h <;>
      simp [afterD1Block,hx1,hx2,hx0,h0,neh1,neh2]

/-- The next b three-one blocks are the only cells changed by the repeated
state-1 digit scan. -/
def d1BlocksOn (T : Int → Bool) (h : Int) (n : Nat) : Prop :=
  ∀ i : Nat, i<n →
    T (h+3*(i:Int)) = true ∧
    T (h+3*(i:Int)+1) = true ∧
    T (h+3*(i:Int)+2) = true

private theorem d1BlocksOn_tail (T : Int → Bool) (h : Int) (n : Nat)
    (hon : d1BlocksOn T h (n+1)) :
    d1BlocksOn (afterD1Block T h) (h+3) n := by
  intro i hi
  obtain ⟨a,b,c⟩ := hon (i+1) (by omega)
  have e0 : h+3+3*(i:Int) = h+3*((i+1:Int)) := by omega
  have e1 : h+3+3*(i:Int)+1 = h+3*((i+1:Int))+1 := by omega
  have e2 : h+3+3*(i:Int)+2 = h+3*((i+1:Int))+2 := by omega
  have n0 : h+3+3*(i:Int) ≠ h := by omega
  have n1 : h+3+3*(i:Int)+1 ≠ h := by omega
  have n2 : h+3+3*(i:Int)+2 ≠ h := by omega
  have n3 : h+3+3*(i:Int) ≠ h+1 := by omega
  have n4 : h+3+3*(i:Int)+1 ≠ h+1 := by omega
  have n5 : h+3+3*(i:Int)+2 ≠ h+1 := by omega
  have n6 : h+3+3*(i:Int) ≠ h+2 := by omega
  have n7 : h+3+3*(i:Int)+1 ≠ h+2 := by omega
  have n8 : h+3+3*(i:Int)+2 ≠ h+2 := by omega
  constructor
  · simpa [afterD1Block,e0,n0,n3,n6] using a
  constructor
  · simpa [afterD1Block,e1,n1,n4,n7] using b
  · simpa [afterD1Block,e2,n2,n5,n8] using c

/-- Tape after b successive state-1 three-one scans. -/
def d0Sweep : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0, T, _ => T
  | n+1, T, h => d0Sweep n (afterD1Block T h) (h+3)

theorem d0Sweep_before (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : x < h) :
    d0Sweep n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
      simp only [d0Sweep]
      have hx' : x < h+3 := by omega
      rw [ih (afterD1Block T h) (h+3) x hx']
      have n0 : x ≠ h := by omega
      have n1 : x ≠ h+1 := by omega
      have n2 : x ≠ h+2 := by omega
      simp [afterD1Block,n0,n1,n2]

theorem d0Sweep_after (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : h+(3*n:Int) ≤ x) :
    d0Sweep n T h x = T x := by
  induction n generalizing T h with
  | zero => simp [d0Sweep]
  | succ n ih =>
      simp only [d0Sweep]
      have hx' : h+3+(3*n:Int) ≤ x := by omega
      rw [ih (afterD1Block T h) (h+3) x hx']
      have n0 : x ≠ h := by omega
      have n1 : x ≠ h+1 := by omega
      have n2 : x ≠ h+2 := by omega
      simp [afterD1Block,n0,n1,n2]

theorem d0Sweep_block (n : Nat) (T : Int → Bool) (h : Int)
    (i : Nat) (hi : i<n) :
    d0Sweep n T h (h+3*(i:Int)) = false ∧
    d0Sweep n T h (h+3*(i:Int)+1) = false ∧
    d0Sweep n T h (h+3*(i:Int)+2) = true := by
  induction n generalizing T h i with
  | zero => omega
  | succ n ih =>
      by_cases hi0 : i=0
      · subst i
        have h0 : d0Sweep n (afterD1Block T h) (h+3) h = false := by
          rw [d0Sweep_before n (afterD1Block T h) (h+3) h (by omega)]
          simp [afterD1Block]
        have h1 : d0Sweep n (afterD1Block T h) (h+3) (h+1) = false := by
          rw [d0Sweep_before n (afterD1Block T h) (h+3) (h+1) (by omega)]
          simp [afterD1Block]
        have h2 : d0Sweep n (afterD1Block T h) (h+3) (h+2) = true := by
          rw [d0Sweep_before n (afterD1Block T h) (h+3) (h+2) (by omega)]
          simp [afterD1Block]
        simpa [d0Sweep] using ⟨h0,h1,h2⟩
      · obtain ⟨j,rfl⟩ : ∃ j, i=j+1 := by omega
        have hsub := ih (afterD1Block T h) (h+3) j (by omega)
        have e0 : h+3+3*(j:Int) = h+3*((j+1:Int)) := by omega
        have e1 : h+3+3*(j:Int)+1 = h+3*((j+1:Int))+1 := by omega
        have e2 : h+3+3*(j:Int)+2 = h+3*((j+1:Int))+2 := by omega
        simpa [d0Sweep,e0,e1,e2] using hsub

/-- Original-run theorem for a repeated block scan in state 1. -/
theorem state1_d1_blocks_right (n : Nat) (T : Int → Bool) (h : Int)
    (hon : d1BlocksOn T h n) :
    run tm2 (3*n) ⟨1,h,T⟩ =
      some ⟨1,h+(3*n:Int),d0Sweep n T h⟩ := by
  induction n generalizing T h with
  | zero => simp [run,d0Sweep]
  | succ n ih =>
      obtain ⟨h0,h1,h2⟩ := hon 0 (by omega)
      have hstep := state1_one_d1_block T h h0 h1 h2
      have htail := ih (afterD1Block T h) (h+3)
        (d1BlocksOn_tail T h n hon)
      have hnum : 3*(n+1) = 3+3*n := by omega
      rw [hnum,run_append,hstep]
      simp only [Option.bind_some]
      rw [htail]
      have hhead : h+3+(3*n:Int) = h+(3*(n+1:Int)) := by omega
      simpa [d0Sweep,hhead]

/-- The final 29 moves only inspect the seven-cell local pattern
1 0 0 1 | 0 0 0 0 0 around the state-1 head. -/
def q4TailInside (x : Int) : Bool :=
  decide (-4 ≤ x ∧ x ≤ 4)

def q4TailStart : FConfig :=
  ⟨1, 0, [-4,-1]⟩

def q4TailEnd : FConfig :=
  ⟨3, -5, [-3,-2,-1,2,3,4]⟩

theorem q4Tail_exact :
    fRun tm2 29 q4TailStart = some q4TailEnd := by
  decide

theorem q4Tail_heads :
    (List.range 29).all (fun k =>
      match fRun tm2 k q4TailStart with
      | none => true
      | some f => q4TailInside f.head) = true := by
  decide

def q4TailInput (T : Int → Bool) (h : Int) : Prop :=
  T (h-4) = true ∧
  T (h-3) = false ∧
  T (h-2) = false ∧
  T (h-1) = true ∧
  (∀ i : Nat, i≤4 → T (h+(i:Int)) = false)

/-- The fixed 29-move tail is valid over an arbitrary exterior tape. -/
theorem q4Tail_at (T : Int → Bool) (h : Int)
    (hin : q4TailInput T h) :
    run tm2 29 ⟨1,h,T⟩ =
      some (frameAt T h q4TailInside q4TailEnd) := by
  apply bridgeAt T h q4TailInside q4TailStart q4TailEnd 29 rfl
    q4Tail_exact q4Tail_heads
  intro x hx
  have hrange : -4 ≤ x ∧ x ≤ 4 := by
    simpa [q4TailInside] using hx
  have hcases :
      x=(-4) ∨ x=(-3) ∨ x=(-2) ∨ x=(-1) ∨
      x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 := by omega
  rcases hcases with hx0|hx1|hx2|hx3|hx4|hx5|hx6|hx7|hx8 <;> subst x
  · simpa [q4TailStart] using hin.1
  · simpa [q4TailStart] using hin.2.1
  · simpa [q4TailStart] using hin.2.2.1
  · simpa [q4TailStart] using hin.2.2.2.1
  · simpa [q4TailStart] using hin.2.2.2.2 0 (by omega)
  · simpa [q4TailStart] using hin.2.2.2.2 1 (by omega)
  · simpa [q4TailStart] using hin.2.2.2.2 2 (by omega)
  · simpa [q4TailStart] using hin.2.2.2.2 3 (by omega)
  · simpa [q4TailStart] using hin.2.2.2.2 4 (by omega)

/-- Exact right-half shape at the q4/head-0 cut.  The first five cells are
ones, then 00, then 3(b+1) ones, then at least five blank cells. -/
def q4RightShape (T : Int → Bool) (h : Int) (b : Nat) : Prop :=
  (∀ i : Nat, i<5 → T (h+(i:Int)) = true) ∧
  T (h+5) = false ∧
  T (h+6) = false ∧
  (∀ i : Nat, i<3*(b+1) → T (h+7+(i:Int)) = true) ∧
  (∀ i : Nat, i≤4 → T (h+10+(3*b:Int)+(i:Int)) = false)

/-- The q4 suffix is a composition of the 10-step entry, the counted
three-one scan, and the 29-step local tail.  The left exterior of the q4
input is unrestricted. -/
theorem q4_suffix_frame (T : Int → Bool) (h : Int) (b : Nat)
    (hshape : q4RightShape T h b) :
    run tm2 (39+3*b) ⟨4,h,T⟩ =
      some (frameAt
        (d0Sweep b
          (frameAt T h q4First10Inside q4First10End).tape
          (h+10))
        (h+10+(3*b:Int)) q4TailInside q4TailEnd) := by
  rcases hshape with ⟨h0,h56,h79,hzeros⟩
  have h79first : ∀ i : Nat, i<3 → T (h+7+(i:Int)) = true := by
    intro i hi
    exact h79 i (by omega)
  have hfirst := q4First10_at T h h0 h56 h79first
  let T1 := (frameAt T h q4First10Inside q4First10End).tape
  let T2 := d0Sweep b T1 (h+10)
  let g : Int := h+10+(3*b:Int)
  have hblocks : d1BlocksOn T1 (h+10) b := by
    intro i hi
    constructor
    · change (frameAt T h q4First10Inside q4First10End).tape
        (h+10+3*(i:Int)) = true
      rw [q4First10_preserves_after T h (h+10+3*(i:Int)) (by omega)]
      have heq : h+10+3*(i:Int) = h+7+((3*i+3:Int)) := by omega
      rw [heq]
      exact h79 (3*i+3) (by omega)
    constructor
    · change (frameAt T h q4First10Inside q4First10End).tape
        (h+10+3*(i:Int)+1) = true
      rw [q4First10_preserves_after T h (h+10+3*(i:Int)+1) (by omega)]
      have heq : h+10+3*(i:Int)+1 = h+7+((3*i+4:Int)) := by omega
      rw [heq]
      exact h79 (3*i+4) (by omega)
    · change (frameAt T h q4First10Inside q4First10End).tape
        (h+10+3*(i:Int)+2) = true
      rw [q4First10_preserves_after T h (h+10+3*(i:Int)+2) (by omega)]
      have heq : h+10+3*(i:Int)+2 = h+7+((3*i+5:Int)) := by omega
      rw [heq]
      exact h79 (3*i+5) (by omega)
  have hscan : run tm2 (3*b)
      (frameAt T h q4First10Inside q4First10End) =
        some ⟨1,g,T2⟩ := by
    have hscan' := state1_d1_blocks_right b T1 (h+10) hblocks
    simpa [T1,T2,g,frameAt_state,frameAt_head] using hscan'
  rcases q4First10_cells T h with ⟨h5,h6,h7,h8,h9⟩
  have htail : q4TailInput T2 g := by
    constructor
    · change d0Sweep b T1 (h+10) (g-4) = true
      by_cases hb : b<2
      · rw [d0Sweep_before b T1 (h+10) (g-4) (by dsimp [g]; omega)]
        have heq : g-4 = h+6+3*b := by dsimp [g]; omega
        rw [heq]
        by_cases hb0 : b=0
        · subst b
          simpa using h6
        · have hb1 : b=1 := by omega
          subst b
          simpa using h9
      · have hb2 : 2≤b := by omega
        let i := b-2
        have hi : i<b := by dsimp [i]; omega
        obtain ⟨_,_,hc⟩ := d0Sweep_block b T1 (h+10) i hi
        have heq : h+10+(3*(i:Int))+2 = g-4 := by dsimp [i,g]; omega
        rw [← heq]
        exact hc
    constructor
    · change d0Sweep b T1 (h+10) (g-3) = false
      by_cases hb : b=0
      · subst b
        rw [d0Sweep_before 0 T1 (h+10) (h+7) (by omega)]
        exact h7
      · let i := b-1
        have hi : i<b := by dsimp [i]; omega
        obtain ⟨hc,_,_⟩ := d0Sweep_block b T1 (h+10) i hi
        have heq : h+10+(3*(i:Int)) = g-3 := by dsimp [i,g]; omega
        rw [← heq]
        exact hc
    constructor
    · change d0Sweep b T1 (h+10) (g-2) = false
      by_cases hb : b=0
      · subst b
        rw [d0Sweep_before 0 T1 (h+10) (h+8) (by omega)]
        exact h8
      · let i := b-1
        have hi : i<b := by dsimp [i]; omega
        obtain ⟨_,hc,_⟩ := d0Sweep_block b T1 (h+10) i hi
        have heq : h+10+(3*(i:Int))+1 = g-2 := by dsimp [i,g]; omega
        rw [← heq]
        exact hc
    constructor
    · change d0Sweep b T1 (h+10) (g-1) = true
      by_cases hb : b=0
      · subst b
        rw [d0Sweep_before 0 T1 (h+10) (h+9) (by omega)]
        exact h9
      · let i := b-1
        have hi : i<b := by dsimp [i]; omega
        obtain ⟨_,_,hc⟩ := d0Sweep_block b T1 (h+10) i hi
        have heq : h+10+(3*(i:Int))+2 = g-1 := by dsimp [i,g]; omega
        rw [← heq]
        exact hc
    · intro i hi
      change d0Sweep b T1 (h+10) (g+(i:Int)) = false
      rw [d0Sweep_after b T1 (h+10) (g+(i:Int)) (by dsimp [g]; omega)]
      have hpres : T1 (g+(i:Int)) = T (g+(i:Int)) := by
        change (frameAt T h q4First10Inside q4First10End).tape
          (g+(i:Int)) = T (g+(i:Int))
        exact q4First10_preserves_after T h (g+(i:Int)) (by dsimp [g]; omega)
      rw [hpres]
      exact hzeros i hi
  have htailrun := q4Tail_at T2 g htail
  calc
    run tm2 (39+3*b) ⟨4,h,T⟩ =
        run tm2 (10+(3*b+29)) ⟨4,h,T⟩ := by congr 1 <;> omega
    _ = (run tm2 10 ⟨4,h,T⟩).bind
          (fun d => run tm2 (3*b+29) d) :=
        by rw [run_append]
    _ = run tm2 (3*b+29)
          (frameAt T h q4First10Inside q4First10End) := by
        rw [hfirst]
        rfl
    _ = (run tm2 (3*b)
          (frameAt T h q4First10Inside q4First10End)).bind
          (fun d => run tm2 29 d) :=
        by rw [run_append]
    _ = run tm2 29 ⟨1,g,T2⟩ := by
        rw [hscan]
        rfl
    _ = some (frameAt T2 g q4TailInside q4TailEnd) := htailrun

#print axioms q4First10_at
#print axioms state1_one_d1_block
#print axioms state1_d1_blocks_right
#print axioms q4Tail_at
#print axioms q4_suffix_frame

end BB6Coverage.Agent8Q4Suffix
