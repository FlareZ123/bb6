import Root56Coverage
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace BB6.Agent5Q0Coarse138Sweep
open Root56 (Side z push hd tl c right left)
abbrev Config := Root56.Config

def step : Config → Option Config
  | (0,l,false,r) => some (right 1 l true r)
  | (0,l,true,r) => some (left 2 l true r)
  | (1,l,false,r) => some (right 2 l true r)
  | (1,l,true,r) => some (left 3 l false r)
  | (2,l,false,r) => some (left 0 l false r)
  | (2,l,true,r) => some (left 0 l true r)
  | (3,l,false,r) => some (right 4 l false r)
  | (3,l,true,r) => some (right 3 l false r)
  | (4,l,true,r) => some (right 5 l true r)
  | (5,l,false,r) => some (right 1 l false r)
  | (5,l,true,r) => some (right 1 l true r)
  | _ => none

def run : Nat → Config → Option Config
  | 0,s => some s
  | n+1,s => (step s).bind (run n)

theorem run_add (n m : Nat) (s : Config) : run (n+m) s = (run n s).bind (run m) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    rw [Nat.succ_add]; simp only [run]
    cases h : step s with
    | none => rfl
    | some t => exact ih t

def ones : Nat → Side → Side
  | 0,s => s
  | n+1,s => true ::: ones n s

theorem ones_add (n m : Nat) (s : Side) : ones (n+m) s = ones n (ones m s) := by
  induction n with
  | zero => simp [ones]
  | succ n ih => simp only [Nat.succ_add,ones,ih]

def blocks : Nat → Side → Side
  | 0,s => s
  | n+1,s => false ::: false ::: true ::: blocks n s

theorem blocks_add (n m : Nat) (s : Side) : blocks (n+m) s = blocks n (blocks m s) := by
  induction n with
  | zero => simp [blocks]
  | succ n ih => simp only [Nat.succ_add,blocks,ih]

theorem eTriple (l r : Side) :
    run 5 (c 4 l true (ones 3 r)) = some (c 4 (blocks 1 l) true r) := by rfl

theorem eSweep (n : Nat) (l r : Side) :
    run (5*n) (c 4 l true (ones (3*n) r)) = some (c 4 (blocks n l) true r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 5*(n+1)=5+5*n by omega,run_add,show 3*(n+1)=3+3*n by omega,ones_add,eTriple]
    simp only [Option.bind_some]
    rw [ih,← blocks_add, Nat.add_comm n 1]

theorem aTriple (l r : Side) :
    run 7 (c 0 (blocks 1 l) true r) = some (c 0 l true (ones 3 r)) := by rfl

theorem aSweep (n : Nat) (l r : Side) :
    run (7*n) (c 0 (blocks n l) true r) = some (c 0 l true (ones (3*n) r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 7*(n+1)=7+7*n by omega,run_add,show n+1=1+n by omega,blocks_add,aTriple]
    simp only [Option.bind_some]
    rw [ih,← ones_add]
    congr 3 <;> omega

theorem turn2 (l : Side) :
    run 6 (c 4 l true (ones 1 z)) = some (c 0 l true (ones 2 z)) := by rfl

theorem turn1 (l : Side) :
    run 6 (c 4 l true z) = some (c 0 l true (false ::: true ::: z)) := by rfl

theorem turn1101 (l : Side) :
    run 6 (c 4 l true (true ::: false ::: true ::: z)) = some (c 0 l true (ones 3 z)) := by rfl

theorem finish (r : Side) :
    run 11 (c 0 z true r) = some (c 4 z true (ones 1 r)) := by rfl

theorem pass (n : Nat) (tail out : Side)
    (ht : ∀ l : Side, run 6 (c 4 l true tail) = some (c 0 l true out)) :
    run (17+12*n) (c 4 z true (ones (3*n) tail)) =
      some (c 4 z true (ones 1 (ones (3*n) out))) := by
  rw [show 17+12*n=5*n+(6+(7*n+11)) by omega,run_add,eSweep]
  simp only [Option.bind_some]
  rw [run_add,ht]
  simp only [Option.bind_some]
  rw [run_add,aSweep]
  exact finish _

def sec (n : Nat) : Config := c 4 z true (ones (6*n+4) z)
def sec1 (n : Nat) : Config := c 4 z true (ones (6*n+6) z)
def sec2 (n : Nat) : Config := c 4 z true (ones (6*n+7) (false ::: true ::: z))

theorem phase1 (n : Nat) : run (29+24*n) (sec n) = some (sec1 n) := by
  have hp := pass (2*n+1) (ones 1 z) (ones 2 z) turn2
  simp only [← ones_add] at hp
  simpa only [sec,sec1,show 17+12*(2*n+1)=29+24*n by omega,
    show 3*(2*n+1)+1=6*n+4 by omega,
    show 1+(3*(2*n+1)+2)=6*n+6 by omega,
    show 1+3*(2*n+1)+2=6*n+6 by omega] using hp

theorem phase2 (n : Nat) : run (41+24*n) (sec1 n) = some (sec2 n) := by
  have hp := pass (2*n+2) z (false ::: true ::: z) turn1
  simp only [← ones_add] at hp
  simpa only [sec1,sec2,show 17+12*(2*n+2)=41+24*n by omega,
    show 3*(2*n+2)=6*n+6 by omega,show 1+(6*n+6)=6*n+7 by omega,
    show 1+3*(2*n+2)=6*n+7 by omega] using hp

theorem phase3 (n : Nat) : run (41+24*n) (sec2 n) = some (sec (n+1)) := by
  have hp := pass (2*n+2) (ones 1 (false ::: true ::: z)) (ones 3 z) turn1101
  simp only [← ones_add] at hp
  simpa only [sec2,sec,show 17+12*(2*n+2)=41+24*n by omega,
    show 3*(2*n+2)+1=6*n+7 by omega,
    show 1+(3*(2*n+2)+3)=6*(n+1)+4 by omega,
    show 1+3*(2*n+2)+3=6*(n+1)+4 by omega] using hp

theorem advance (n : Nat) : run (111+72*n) (sec n) = some (sec (n+1)) := by
  rw [show 111+72*n=(29+24*n)+((41+24*n)+(41+24*n)) by omega,run_add,phase1]
  simp only [Option.bind_some]
  rw [run_add,phase2]
  exact phase3 n

theorem seed : run 43 Root56.blank = some (sec 0) := by rfl

def clock : Nat → Nat
  | 0 => 43
  | n+1 => clock n + (111+72*n)

theorem at_clock (n : Nat) : run (clock n) Root56.blank = some (sec n) := by
  induction n with
  | zero => exact seed
  | succ n ih =>
    simp only [clock]
    rw [run_add,ih]
    exact advance n

theorem clock_ge (n : Nat) : n ≤ clock n := by
  induction n with
  | zero => omega
  | succ n ih => simp only [clock]; omega

theorem never (n : Nat) : run n Root56.blank ≠ none := by
  intro h
  have hs := at_clock n
  have hx := run_add n (clock n-n) Root56.blank
  rw [Nat.add_sub_of_le (clock_ge n),hs,h] at hx
  contradiction

open BB6Coverage BB6.Agent13BlankDelay
open Root56Coverage (center center_right center_left center_blank)

def table : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨false,true,4⟩)
  | 3,true => some (some ⟨false,true,3⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem step_center {m : Machine} (hm : compatible table m) (s : BB6Coverage.Config) (r : Config)
    (h : step (center s) = some r) :
    ∃ t, rawStep m s = some t ∧ center t = r := by
  have hq : s.state.val = 0 ∨ s.state.val = 1 ∨ s.state.val = 2 ∨ s.state.val = 3 ∨ s.state.val = 4 ∨ s.state.val = 5 := by omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> cases hb : s.tape s.head <;>
    simp [center,Root56.c,step,hq,hb] at h
  all_goals
    have ht := hm (readSlot s) _ (by simp only [table,hq,hb]; rfl)
    simp only [rawStep,ht,Bool.false_eq_true,ite_false,ite_true]
    exact ⟨_,rfl,by first | rw [center_right]; exact h | rw [center_left]; exact h⟩

theorem run_center {m : Machine} (hm : compatible table m) (n : Nat) (s : BB6Coverage.Config) (r : Config)
    (h : run n (center s) = some r) :
    ∃ t, BB6Coverage.run m n s = some t ∧ center t = r := by
  induction n generalizing r with
  | zero => exact ⟨s,rfl,Option.some.inj h⟩
  | succ n ih =>
    rw [run_add] at h
    cases hr : run n (center s) with
    | none => simp [hr] at h
    | some r' =>
      obtain ⟨t,ht,hc⟩ := ih r' hr
      have hstep : step (center t) = some r := by
        rw [hc]
        simpa [hr,run] using h
      obtain ⟨t',ht',hc'⟩ := step_center hm t r hstep
      exact ⟨t',by rw [BB6Coverage.run.eq_2,ht]; exact ht',hc'⟩

theorem never_compatible (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  have hn := never n
  rw [← center_blank] at hn
  cases h : run n (center blank) with
  | none => exact False.elim (hn h)
  | some r =>
    obtain ⟨s,hs,_⟩ := run_center hm n blank r h
    rw [hs]; rfl

theorem weighted (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never_compatible m hm)

#print axioms advance
#print axioms never_compatible
#print axioms weighted
end BB6.Agent5Q0Coarse138Sweep
