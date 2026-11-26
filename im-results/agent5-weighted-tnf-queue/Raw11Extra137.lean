import Root56
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
namespace Raw11Extra137
open Root56

def step : Config → Option Config
  | (0,l,false,r) => some (right 1 l true r)
  | (0,l,true,r) => some (right 3 l true r)
  | (1,l,false,r) => some (right 2 l true r)
  | (1,l,true,r) => some (right 2 l false r)
  | (2,l,false,r) => some (left 0 l false r)
  | (2,l,true,r) => some (right 4 l false r)
  | (3,l,false,r) => some (left 0 l true r)
  | (3,l,true,r) => some (left 3 l true r)
  | (4,l,false,r) => some (right 3 l false r)
  | (4,l,true,r) => some (right 5 l false r)
  | (5,l,true,r) => some (left 2 l true r)
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
  | zero => simp only [Nat.zero_add,ones]
  | succ n ih => simp only [Nat.succ_add,ones,ih]

def sec (n : Nat) : Config := c 0 z false (ones (2*n+4) z)

theorem enter (n : Nat) : run 8 (sec n) = some (c 2 (ones 2 (false ::: true ::: z)) true (ones (2*n) z)) := by
  unfold sec
  rw [show 2*n+4=4+2*n by omega,ones_add]
  rfl

theorem rightPair (l r : Side) : run 6 (c 2 l true (ones 2 r)) = some (c 2 (ones 2 l) true r) := by rfl

theorem rightSweep (n : Nat) (l r : Side) : run (6*n) (c 2 l true (ones (2*n) r)) = some (c 2 (ones (2*n) l) true r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 6*(n+1)=6+6*n by omega,run_add,show 2*(n+1)=2+2*n by omega,ones_add,rightPair]
    simp only [Option.bind_some]
    rw [ih,← ones_add,show 2*n+2=2+2*n by omega]

theorem turn (l : Side) : run 18 (c 2 (true ::: l) true z) = some (c 3 (true ::: l) true (ones 4 z)) := by rfl

theorem leftOne (l r : Side) : run 1 (c 3 (true ::: l) true r) = some (c 3 l true (true ::: r)) := by rfl

theorem leftSweep (n : Nat) (l r : Side) : run n (c 3 (ones n l) true r) = some (c 3 l true (ones n r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    conv => lhs; arg 1; rw [show n+1=1+n by omega]
    rw [run_add]
    change (run 1 (c 3 (true ::: ones n l) true r)).bind (run n) = _
    rw [leftOne,Option.bind_some,ih]
    change some (c 3 l true (ones n (ones 1 r))) = _
    rw [← ones_add]

theorem finish (r : Side) : run 6 (c 3 (false ::: true ::: z) true r) = some (c 0 z false (ones 4 r)) := by rfl

theorem advance (n : Nat) : run (8*n+34) (sec n) = some (sec (n+3)) := by
  rw [show 8*n+34=8+(6*n+(18+((2*n+2)+6))) by omega,run_add,enter]
  simp only [Option.bind_some]
  rw [run_add,rightSweep,Option.bind_some,← ones_add]
  rw [run_add]
  have h : run 18 (c 2 (ones (2*n+2) (false ::: true ::: z)) true z) = some (c 3 (ones (2*n+2) (false ::: true ::: z)) true (ones 4 z)) := by
    rw [show 2*n+2=1+(2*n+1) by omega,ones_add]
    exact turn _
  rw [h,Option.bind_some,run_add,leftSweep,Option.bind_some,finish]
  unfold sec
  rw [← ones_add,← ones_add,show 4+(2*n+2)+4=2*(n+3)+4 by omega]

theorem seed : run 10 blank = some (sec 0) := by rfl

def clock : Nat → Nat
  | 0 => 10
  | n+1 => clock n + (8*(3*n)+34)

theorem section_at (n : Nat) : run (clock n) blank = some (sec (3*n)) := by
  induction n with
  | zero => exact seed
  | succ n ih =>
    rw [clock,run_add,ih,Option.bind_some,advance,show 3*n+3=3*(n+1) by omega]

theorem clock_ge (n : Nat) : n ≤ clock n := by
  induction n with
  | zero => decide
  | succ n ih => change n+1 ≤ clock n + (8*(3*n)+34); omega

theorem never (n : Nat) : run n blank ≠ none := by
  intro h
  have hx := run_add n (clock n - n) blank
  rw [Nat.add_sub_of_le (clock_ge n),section_at,h] at hx
  contradiction

#print axioms advance
#print axioms never
end Raw11Extra137
