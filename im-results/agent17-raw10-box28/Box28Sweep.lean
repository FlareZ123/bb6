import Box33BinaryCounter

namespace BB6.Agent17.Box28Sweep
open C9Pair
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def step (c : Config) : Option Config :=
  match c.q, c.a with
  | .A, false => some (right .B true c)
  | .A, true => some (right .D false c)
  | .B, false => some (left .C true c)
  | .B, true => some (right .F true c)
  | .C, false => some (left .C true c)
  | .C, true => some (left .D false c)
  | .D, false => some (right .D false c)
  | .D, true => some (left .E false c)
  | .E, false => some (left .A true c)
  | .E, true => some (left .D true c)
  | .F, false => some (right .A true c)
  | .F, true => none

def run : Nat → Config → Option Config
  | 0, c => some c
  | n+1, c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    simp only [Nat.succ_add, run]
    cases step c <;> simp [ih]

def bits : List Bool → Stream → Stream
  | [], s => s
  | b::bs, s => push b (bits bs s)

def p01 : Nat → Stream → Stream
  | 0,s => s
  | n+1,s => bits [false,true] (p01 n s)
def p10 : Nat → Stream → Stream
  | 0,s => s
  | n+1,s => bits [true,false] (p10 n s)

def sectionAt (q : Q) (l r : Stream) : Config := ⟨q,l,r 0,pop r⟩
def gap : Stream := push false (ones 3)
def root (k : Nat) : Config := sectionAt .A (rep true (6*k+3) gap) zeros
def leftPhase (n : Nat) (r : Stream) : Config :=
  ⟨.E,rep true (2*n+1) gap,true,r⟩

-- E,D traverse a pair of adjacent ones, leaving the pattern 01.
theorem left_pair (n : Nat) (r : Stream) :
    run 2 (leftPhase (n+1) r) = some (leftPhase n (bits [false,true] r)) := by
  have h : 2*(n+1) = 2*n+2 := by omega
  simp [leftPhase, h, run, step, left, bits, rep, pop_push, push_zero]

theorem left_pair_iter (n : Nat) (r : Stream) :
    run (2*n) (leftPhase n r) = some (leftPhase 0 (p01 n r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    -- perform the innermost n iterations first, so the output nesting is definitional
    have h : 2*(n+1) = 2+2*n := by omega
    rw [h, run_add, left_pair, Option.bind_some, ih]
    congr 1
    have hc : ∀ m (s : Stream), p01 m (bits [false,true] s) = bits [false,true] (p01 m s) := by
      intro m
      induction m with
      | zero => intro s; rfl
      | succ m hm => intro s; simp only [p01, hm]
    rw [hc, p01]

theorem enter (k : Nat) :
    run 4 (root k) =
      some (leftPhase (3*k) (bits [false,false,true] zeros)) := by
  have h : 6*k+3 = (2*(3*k)+1)+2 := by omega
  simp [root, sectionAt, gap, leftPhase, h, run, step, left, right, bits, rep, zeros,
    pop_push, push_zero, ones] 

-- Two final left moves reach the separator, then E0 crosses it.
theorem finish_left (r : Stream) :
    run 3 (leftPhase 0 r) = some (sectionAt .A (ones 2) (bits [true,true,false,true] r)) := by
  simp [leftPhase, gap, sectionAt, run, step, left, bits, rep, ones, pop_push, push_zero]

-- The remaining three ones on the left are cleared with three A,D,E cycles.
theorem clear_tail (s : Stream) :
    run 9 (sectionAt .A (ones 2) (push true (push true s))) =
      some (sectionAt .A zeros (bits [false,true,false,false,false] s)) := by
  simp [sectionAt, run, step, left, right, bits, ones, rep, zeros, pop_push, push_zero]

-- The right sweep starts with a fixed local turn, irrespective of the long suffix.
theorem turn (s : Stream) :
    run 18 (sectionAt .A zeros (bits [false,true,false,false,false,false,true] s)) =
      some (sectionAt .A gap (bits [false,true,false,false,true] s)) := by
  simp [sectionAt, gap, run, step, left, right, bits, ones, rep, zeros, pop_push, push_zero]

theorem shift_pairs (n : Nat) :
    push true (p01 n (bits [false,false,true] zeros)) =
      p10 (n+1) (bits [false,true] zeros) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change push true (push false (push true (p01 n (bits [false,false,true] zeros)))) =
      push true (push false (p10 (n+1) (bits [false,true] zeros)))
    rw [ih]

def rightPhase (l : Stream) (k : Nat) : Config :=
  sectionAt .A l (bits [false,true,false,false] (p10 (3*k+1) (bits [false,true] zeros)))

theorem right_cycle (l : Stream) (k : Nat) :
    run 10 (rightPhase l (k+1)) = some (rightPhase (rep true 6 l) k) := by
  have h : 3*(k+1)+1 = (3*k+1)+3 := by omega
  simp [rightPhase, h, p10, bits, sectionAt, run, step, left, right, rep, pop_push, push_zero]

theorem right_finish (l : Stream) :
    run 9 (rightPhase l 0) = some (sectionAt .A (rep true 9 l) zeros) := by
  simp [rightPhase, p10, bits, sectionAt, run, step, right, rep, zeros, pop_push, push_zero]

theorem right_iter (k : Nat) (l : Stream) :
    run (10*k+9) (rightPhase l k) =
      some (sectionAt .A (rep true (6*k+9) l) zeros) := by
  induction k generalizing l with
  | zero => exact right_finish l
  | succ k ih =>
    rw [show 10*(k+1)+9 = 10+(10*k+9) by omega, run_add, right_cycle, Option.bind_some, ih, ← rep_add]
    congr 1
    congr 1
    omega

theorem recur (k : Nat) : run (43+16*k) (root k) = some (root (k+1)) := by
  rw [show 43+16*k = 4+2*(3*k)+3+9+18+(10*k+9) by omega]
  rw [run_add, run_add, run_add, run_add, run_add, enter, Option.bind_some,
    left_pair_iter, Option.bind_some, finish_left, Option.bind_some, clear_tail, Option.bind_some]
  -- unfold one pair sectionAt the turn and retain the rest as an arbitrary stream.
  sorry

end BB6.Agent17.Box28Sweep
