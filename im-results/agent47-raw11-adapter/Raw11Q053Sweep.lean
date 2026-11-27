import Root56Coverage
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace BB6.Agent47Q053Sweep
open Root56 (Side z push hd tl c right left)
abbrev Config := Root56.Config

def step : Config → Option Config
  | (0,l,false,r) => some (right 1 l true r)
  | (0,l,true,r) => some (right 3 l true r)
  | (1,l,false,r) => some (right 2 l true r)
  | (1,l,true,r) => some (right 4 l true r)
  | (2,l,false,r) => some (left 0 l false r)
  | (3,l,false,r) => some (left 0 l true r)
  | (3,l,true,r) => some (left 3 l true r)
  | (4,l,false,r) => some (left 5 l true r)
  | (4,l,true,r) => some (right 5 l false r)
  | (5,l,false,r) => some (right 0 l true r)
  | (5,l,true,r) => some (left 5 l false r)
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

def sec (n : Nat) : Config := c 2 (true ::: true ::: true ::: false ::: ones (11+6*n) z) false z

theorem enter (l : Side) : run 10 (c 2 (true ::: true ::: true ::: false ::: true ::: l) false z) = some (c 3 (true ::: l) true (ones 4 z)) := by rfl

theorem dSweep (n : Nat) (l r : Side) :
    run n (c 3 (ones n l) true r) = some (c 3 l true (ones n r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=1+n by omega,run_add]
    rw [ones_add 1 n]
    change (run 1 (c 3 (true ::: ones n l) true r)).bind (run n) = _
    change run n (c 3 (ones n l) true (true ::: r)) = _
    rw [ih]
    change some (c 3 l true (ones n (ones 1 r))) = some (c 3 l true (ones (1+n) r))
    rw [← ones_add, Nat.add_comm n 1]

theorem turn (r : Side) : run 4 (c 3 z true (true ::: true ::: r)) = some (c 4 (ones 2 z) true (true ::: true ::: r)) := by rfl

theorem triple (l r : Side) : run 5 (c 4 l true (ones 3 r)) = some (c 4 (ones 3 l) true r) := by rfl

theorem eSweep (n : Nat) (l r : Side) : run (5*n) (c 4 l true (ones (3*n) r)) = some (c 4 (ones (3*n) l) true r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 5*(n+1)=5+5*n by omega,run_add,show 3*(n+1)=3+3*n by omega,ones_add,triple]
    simp only [Option.bind_some]
    rw [ih,← ones_add, Nat.add_comm (3*n) 3]

theorem finish (l : Side) : run 4 (c 4 l true z) = some (c 2 (true ::: true ::: true ::: false ::: l) false z) := by rfl

theorem advance (n : Nat) : run (54+16*n) (sec n) = some (sec (n+1)) := by
  unfold sec
  rw [show 54+16*n=10+((11+6*n)+(4+(5*(5+2*n)+4))) by omega,run_add]
  rw [show 11+6*n=1+(10+6*n) by omega,ones_add 1 (10+6*n)]
  change (run 10 (c 2 (true ::: true ::: true ::: false ::: true ::: ones (10+6*n) z) false z)).bind _ = _
  rw [enter]
  simp only [Option.bind_some]
  change run ((1+(10+6*n))+(4+(5*(5+2*n)+4))) (c 3 (ones 1 (ones (10+6*n) z)) true (ones 4 z)) = _
  rw [← ones_add 1 (10+6*n),show 1+(10+6*n)=11+6*n by omega]
  rw [run_add,dSweep]
  simp only [Option.bind_some]
  rw [← ones_add,show 11+6*n+4=3*(5+2*n) by omega,run_add]
  have ht : run 4 (c 3 z true (ones (3*(5+2*n)) z)) = some (c 4 (ones 2 z) true (ones (3*(5+2*n)) z)) := by
    rw [show 3*(5+2*n)=2+(13+6*n) by omega,ones_add]
    exact turn _
  rw [ht]
  simp only [Option.bind_some]
  rw [run_add,eSweep]
  simp only [Option.bind_some]
  rw [finish,← ones_add,show 3*(5+2*n)+2=11+6*(n+1) by omega]

theorem seed : run 88 Root56.blank = some (sec 0) := by rfl

def clock : Nat → Nat
  | 0 => 88
  | n+1 => clock n + (54+16*n)

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
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
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
end BB6.Agent47Q053Sweep
