import Std

namespace CryptidA

structure Cfg where
  left : List Bool
  bit : Bool
  right : List Bool
  state : Nat
  deriving Repr, DecidableEq

def goL (c : Cfg) (v : Bool) (s : Nat) : Cfg :=
  match c.left with
  | [] => ⟨[], false, v :: c.right, s⟩
  | b :: bs => ⟨bs, b, v :: c.right, s⟩

def goR (c : Cfg) (v : Bool) (s : Nat) : Cfg :=
  match c.right with
  | [] => ⟨v :: c.left, false, [], s⟩
  | b :: bs => ⟨v :: c.left, b, bs, s⟩

def step (c : Cfg) : Cfg :=
  match c.state, c.bit with
  | 0, false => goR c true 1
  | 0, true => goR c false 4
  | 1, false => goL c true 2
  | 1, true => goR c false 0
  | 2, false => goL c true 0
  | 2, true => goL c true 3
  | 3, false => goL c true 2
  | 3, true => goL c true 5
  | 4, false => goL c false 2
  | 4, true => goL c false 1
  | 5, false => goL c true 4
  | 5, true => c
  | _, _ => c

def run : Nat → Cfg → Cfg
  | 0, c => c
  | n + 1, c => step (run n c)

theorem run_add (m n : Nat) (c : Cfg) : run (m+n) c = run n (run m c) := by
  induction n with
  | zero => simp [run]
  | succ n ih => simpa [run, Nat.add_succ] using congrArg step ih

def pat : Nat → List Bool
  | 0 => []
  | m + 1 => true :: false :: pat m

def start (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false :: (pat m ++ [true,true]), false, false :: ys, 0⟩

def cursor (m k : Nat) (ys : List Bool) : Cfg :=
  ⟨false :: (pat m ++ [true,true]), true, List.replicate k true ++ ys, 2⟩

def finish (n : Nat) (ys : List Bool) : Cfg :=
  ⟨[], false, List.replicate n true ++ ys, 5⟩

theorem start_two (m : Nat) (ys : List Bool) :
    run 2 (start m ys) = cursor m 1 ys := by
  simp [run, step, goR, goL, start, cursor]

theorem cursor_two (m k : Nat) (ys : List Bool) :
    run 2 (cursor (m+1) k ys) = cursor m (k+2) ys := by
  simp [run, step, goL, cursor, pat, List.replicate]

theorem cursor_base (k : Nat) (ys : List Bool) :
    run 4 (cursor 0 k ys) = finish (k+4) ys := by
  simp [run, step, goL, cursor, pat, finish, List.replicate]

theorem cursor_sweep (m k : Nat) (ys : List Bool) :
    run (2*m+4) (cursor m k ys) = finish (k+2*m+4) ys := by
  induction m generalizing k with
  | zero => simpa using cursor_base k ys
  | succ m ih =>
    have h := cursor_two m k ys
    calc
      run (2*(m+1)+4) (cursor (m+1) k ys)
          = run (2*m+4) (run 2 (cursor (m+1) k ys)) := by
              rw [← run_add]
              congr 1
              omega
      _ = run (2*m+4) (cursor m (k+2) ys) := by rw [h]
      _ = finish ((k+2)+2*m+4) ys := ih (k+2)
      _ = finish (k+2*(m+1)+4) ys := by congr 1; omega

theorem close_double_zero (m : Nat) (ys : List Bool) :
    run (2*m+6) (start m ys) = finish (2*m+5) ys := by
  calc
    run (2*m+6) (start m ys) = run (2*m+4) (run 2 (start m ys)) := by
      rw [← run_add]
      congr 1
      omega
    _ = run (2*m+4) (cursor m 1 ys) := by rw [start_two]
    _ = finish (1+2*m+4) ys := cursor_sweep m 1 ys
    _ = finish (2*m+5) ys := by congr 1; omega

#print axioms close_double_zero
end CryptidA
