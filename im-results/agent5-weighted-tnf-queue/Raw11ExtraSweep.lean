import Root56
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace Raw11ExtraSweep
open Root56 (Side z push hd tl c right left alt10)
abbrev Config := Root56.Config
/-- false: extra92; true: extra124. -/
def step (v : Bool) : Config → Option Config
  | (0,l,false,r) => some (right 1 l true r)
  | (0,l,true,r) => some (right 3 l true r)
  | (1,l,false,r) => some (right 2 l true r)
  | (1,l,true,r) => some (left 3 l false r)
  | (2,l,false,r) => some (left 0 l false r)
  | (2,l,true,r) => some (right 4 l v r)
  | (3,l,false,r) => some (left 0 l true r)
  | (3,l,true,r) => some (left 1 l true r)
  | (4,l,false,r) => some (if v then left 4 l false r else right 0 l false r)
  | (4,l,true,r) => some (right 5 l false r)
  | (5,l,false,r) => some (if v then right 0 l false r else left 0 l true r)
  | _ => none

def run (v : Bool) : Nat → Config → Option Config
  | 0,s => some s
  | n+1,s => (step v s).bind (run v n)

theorem run_add (v : Bool) (n m : Nat) (s : Config) : run v (n+m) s = (run v n s).bind (run v m) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    rw [Nat.succ_add]; simp only [run]
    cases h : step v s with
    | none => rfl
    | some t => exact ih t

def alt01 : Nat → Side → Side
  | 0,s => s
  | n+1,s => false ::: true ::: alt01 n s

theorem alt01_add (n m : Nat) (s : Side) : alt01 (n+m) s = alt01 n (alt01 m s) := by
  induction n with
  | zero => simp [alt01]
  | succ n ih => simp only [Nat.succ_add,alt01,ih]

def tail : Side := false ::: true ::: false ::: true ::: z

def sec (n : Nat) : Config := c 0 z false (alt10 n tail)

def stride (v : Bool) : Nat := if v then 8 else 6

def turn (v : Bool) : Nat := if v then 33 else 29

theorem rightPair (v : Bool) (l r : Side) :
    run v (stride v) (c 0 (false ::: l) false (alt10 1 r)) = some (c 0 (false ::: alt01 1 l) false r) := by
  cases v <;> rfl

theorem rightSweep (v : Bool) (n : Nat) (l r : Side) :
    run v (stride v*n) (c 0 (false ::: l) false (alt10 n r)) = some (c 0 (false ::: alt01 n l) false r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show stride v*(n+1) = stride v+stride v*n by rw [Nat.mul_succ, Nat.add_comm],run_add]
    change (run v (stride v) (c 0 (false ::: l) false (alt10 1 (alt10 n r)))).bind (run v (stride v*n)) = _
    rw [rightPair]
    simp only [Option.bind_some]
    rw [ih,← alt01_add]

theorem turning (v : Bool) (l : Side) :
    run v (turn v) (c 0 (false ::: false ::: true ::: l) false tail) = some (c 0 l true (alt10 2 tail)) := by
  cases v <;> rfl

theorem leftPair (v : Bool) (l r : Side) :
    run v 4 (c 0 (alt01 1 l) true (true ::: r)) = some (c 0 l true (alt10 1 (true ::: r))) := by
  cases v <;> rfl

theorem leftSweep (v : Bool) (n : Nat) (l r : Side) :
    run v (4*n) (c 0 (alt01 n l) true (true ::: r)) = some (c 0 l true (alt10 n (true ::: r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 4*(n+1) = 4+4*n by omega,run_add]
    change (run v 4 (c 0 (alt01 1 (alt01 n l)) true (true ::: r))).bind (run v (4*n)) = _
    rw [leftPair]
    simp only [Option.bind_some]
    change run v (4*n) (c 0 (alt01 n l) true (true ::: false ::: true ::: r)) = _
    rw [ih]
    change some (c 0 l true (alt10 n (alt10 1 (true ::: r)))) = _
    rw [← Root56.alt_add]

theorem finish (v : Bool) (r : Side) :
    run v 4 (c 0 z true (true ::: r)) = some (c 0 z false (alt10 1 (true ::: r))) := by
  cases v <;> rfl

theorem advance (v : Bool) (n : Nat) :
    run v (stride v*(n+1)+turn v+4*n+4) (sec (n+1)) = some (sec (n+3)) := by
  unfold sec
  rw [show stride v*(n+1)+turn v+4*n+4 = stride v*(n+1)+(turn v+(4*n+4)) by omega,run_add]
  conv => lhs; arg 1; arg 3; rw [← Root56.zero_push]
  rw [rightSweep]
  simp only [Option.bind_some]
  rw [run_add]
  change (run v (turn v) (c 0 (false ::: false ::: true ::: alt01 n z) false tail)).bind (run v (4*n+4)) = _
  rw [turning]
  simp only [Option.bind_some]
  rw [run_add]
  change (run v (4*n) (c 0 (alt01 n z) true (true ::: false ::: alt10 1 tail))).bind (run v 4) = _
  rw [leftSweep]
  simp only [Option.bind_some]
  change run v 4 (c 0 z true (alt10 n (alt10 2 tail))) = _
  rw [← Root56.alt_add,show n+2=1+(n+1) by omega,Root56.alt_add]
  change run v 4 (c 0 z true (true ::: false ::: alt10 (n+1) tail)) = _
  rw [finish]
  change some (c 0 z false (alt10 2 (alt10 (n+1) tail))) = _
  rw [← Root56.alt_add,show 2+(n+1)=n+3 by omega]

#print axioms advance
end Raw11ExtraSweep
