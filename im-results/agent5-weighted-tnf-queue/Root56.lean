import Std
set_option maxHeartbeats 200000
set_option maxRecDepth 1000

namespace Root56
abbrev Side := Nat → Bool
def z : Side := fun _ => false
def push (b : Bool) (s : Side) : Side
  | 0 => b
  | n+1 => s n
infixr:67 " ::: " => push
def hd (s : Side) := s 0
def tl (s : Side) := fun n => s (n+1)
@[simp] theorem hd_push (b : Bool) (s : Side) : hd (b ::: s) = b := rfl
@[simp] theorem tl_push (b : Bool) (s : Side) : tl (b ::: s) = s := rfl
@[simp] theorem hd_z : hd z = false := rfl
@[simp] theorem tl_z : tl z = z := rfl
@[simp] theorem zero_push : false ::: z = z := by funext n; cases n <;> rfl
abbrev Config := Nat × Side × Bool × Side
def c (q : Nat) (l : Side) (b : Bool) (r : Side) : Config := (q,l,b,r)
def right (q : Nat) (l : Side) (w : Bool) (r : Side) : Config := c q (w ::: l) (hd r) (tl r)
def left (q : Nat) (l : Side) (w : Bool) (r : Side) : Config := c q (tl l) (hd l) (w ::: r)
def step : Config → Option Config
  | (0,l,false,r) => some (right 1 l true r)
  | (0,l,true,r) => some (right 3 l true r)
  | (1,l,false,r) => some (right 2 l true r)
  | (1,l,true,r) => some (left 2 l false r)
  | (2,l,false,r) => some (left 0 l false r)
  | (2,l,true,r) => some (left 1 l true r)
  | (3,l,false,r) => some (left 0 l true r)
  | (3,l,true,r) => some (right 4 l false r)
  | (4,l,false,r) => some (left 1 l true r)
  | (4,l,true,r) => some (right 5 l true r)
  | (5,l,false,r) => some (right 0 l false r)
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

def alt10 : Nat → Side → Side
  | 0,s => s
  | n+1,s => true ::: false ::: alt10 n s
@[simp] theorem alt_add (n m : Nat) (s : Side) : alt10 (n+m) s = alt10 n (alt10 m s) := by
  induction n with
  | zero => simp only [Nat.zero_add,alt10]
  | succ n ih => simp only [Nat.succ_add,alt10,ih]

def A (n : Nat) : Config := c 0 z false (false ::: false ::: alt10 (2*n+1) (true ::: z))
def blank : Config := c 0 z false z

theorem enterF (n : Nat) : run 8 (A n) = some (c 5 (alt10 1 (true ::: true ::: z)) false (alt10 (2*n) (true ::: z))) := by
  rfl

theorem fpair (l r : Side) : run 6 (c 5 l false (alt10 2 r)) = some (c 5 (alt10 2 l) false r) := by rfl

theorem fSweep (n : Nat) (l r : Side) : run (6*n) (c 5 l false (alt10 (2*n) r)) = some (c 5 (alt10 (2*n) l) false r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 6*(n+1) = 6+6*n by omega,run_add]
    rw [show 2*(n+1) = 2+2*n by omega,alt_add,fpair]
    simp only [Option.bind_some]
    rw [ih,← alt_add]
    congr 3 <;> omega

theorem fTail (l : Side) : run 6 (c 5 l false (true ::: z)) = some (c 1 (alt10 1 l) false (true ::: z)) := by
  rfl

theorem bPair (l r : Side) : run 4 (c 1 (alt10 1 l) false (true ::: r)) = some (c 1 l false (alt10 1 (true ::: r))) := by rfl

theorem bSweep (n : Nat) (l r : Side) : run (4*n) (c 1 (alt10 n l) false (true ::: r)) = some (c 1 l false (alt10 n (true ::: r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 4*(n+1)=4+4*n by omega,run_add]
    change (run 4 (c 1 (alt10 1 (alt10 n l)) false (true ::: r))).bind (run (4*n)) = _
    rw [bPair]
    simp only [Option.bind_some]
    change run (4*n) (c 1 (alt10 n l) false (true ::: false ::: true ::: r)) = _
    rw [ih]
    change some (c 1 l false (alt10 n (alt10 1 (true ::: r)))) = _
    rw [← alt_add]

theorem bTail (r : Side) : run 6 (c 1 (true ::: true ::: z) false (true ::: r)) = some (c 0 z false (false ::: false ::: alt10 1 (true ::: r))) := by
  rfl

theorem advance (n : Nat) : run (14*n+28) (A n) = some (A (n+1)) := by
  rw [show 14*n+28=8+(6*n+(6+(4*(2*n+2)+6))) by omega,run_add,enterF]
  simp only [Option.bind_some]
  rw [run_add,fSweep]
  simp only [Option.bind_some]
  rw [run_add,fTail]
  simp only [Option.bind_some]
  rw [← alt_add,← alt_add]
  rw [show 1+(2*n)+1=2*n+2 by omega]
  rw [run_add,bSweep]
  simp only [Option.bind_some]
  change run 6 (c 1 (true ::: true ::: z) false (true ::: false ::: alt10 (2*n+1) (true ::: z))) = _
  rw [bTail]
  unfold A
  change some (c 0 z false (false ::: false ::: alt10 2 (alt10 (2*n+1) (true ::: z)))) = _
  rw [← alt_add,show 2+(2*n+1)=2*(n+1)+1 by omega]

theorem seed : run 14 blank = some (A 0) := by rfl

def clock : Nat → Nat
  | 0 => 14
  | n+1 => clock n + (14*n+28)

theorem section_at (n : Nat) : run (clock n) blank = some (A n) := by
  induction n with
  | zero => simpa only [clock] using seed
  | succ n ih =>
    simp only [clock]
    rw [run_add (clock n) (14*n+28) blank, ih, Option.bind_some]
    exact advance n

theorem clock_ge (n : Nat) : n ≤ clock n := by
  induction n with
  | zero => decide
  | succ n ih => change n+1 ≤ clock n + (14*n+28); omega

theorem never (n : Nat) : run n blank ≠ none := by
  intro h
  have hs := section_at n
  have hsum : n + (clock n - n) = clock n := Nat.add_sub_of_le (clock_ge n)
  have hx := run_add n (clock n - n) blank
  rw [hsum,hs,h] at hx
  contradiction
#print axioms advance
#print axioms never
end Root56
