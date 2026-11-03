import Std

set_option maxHeartbeats 3000000
namespace BB6.Row262

-- 1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---
-- States 0..5 are A..F. F/1 is frozen and is the only halting configuration.
structure Cfg where
  st : Nat
  left : List Bool
  head : Bool
  right : List Bool
  deriving Repr, DecidableEq

-- Bit arrays store the nearest tape cell first. Empty sides denote infinite zeroes.
def moveL (c : Cfg) (q : Nat) (w : Bool) : Cfg :=
  ⟨q, c.left.tail, c.left.headD false, w :: c.right⟩

def moveR (c : Cfg) (q : Nat) (w : Bool) : Cfg :=
  ⟨q, w :: c.left, c.right.headD false, c.right.tail⟩

def step (c : Cfg) : Cfg :=
  match c.st, c.head with
  | 0, false => moveR c 1 true
  | 0, true  => moveL c 2 true
  | 1, false => moveL c 0 true
  | 1, true  => moveR c 5 true
  | 2, false => moveR c 3 false
  | 2, true  => moveR c 3 true
  | 3, false => moveR c 0 false
  | 3, true  => moveL c 4 false
  | 4, false => moveL c 0 true
  | 4, true  => moveL c 4 false
  | 5, false => moveR c 2 false
  | _, _ => c

def run : Nat → Cfg → Cfg
  | 0, c => c
  | n + 1, c => run n (step c)

-- E erases a contiguous leftward run of ones, then flips the next zero.
theorem e_sweep (k : Nat) (x : Bool) (ls rs : List Bool) :
    run (k+2) ⟨4, List.replicate k true ++ false :: x :: ls, true, rs⟩ =
      ⟨0, ls, x, true :: List.replicate (k+1) false ++ rs⟩ := by
  induction k generalizing rs with
  | zero => rfl
  | succ k ih =>
      have zero_comm : ∀ n : Nat, (List.replicate n false ++ false :: rs) =
          false :: (List.replicate n false ++ rs) := by
        intro n
        induction n with
        | zero => rfl
        | succ n hn => simp [List.replicate, hn]
      calc
        run (k+3) ⟨4, List.replicate (k+1) true ++ false :: x :: ls, true, rs⟩
            = run (k+2) ⟨4, List.replicate k true ++ false :: x :: ls, true, false :: rs⟩ := by
              simp [run, step, moveL, List.replicate]
        _ = ⟨0, ls, x, true :: List.replicate (k+1) false ++ false :: rs⟩ := ih (false :: rs)
        _ = ⟨0, ls, x, true :: List.replicate (k+2) false ++ rs⟩ := by
              simp [List.replicate, zero_comm]

-- Five bounded branches of the exact A-to-A-or-halt return map.
theorem a_zero_b_zero (ls rs : List Bool) :
    run 2 ⟨0, ls, false, false :: rs⟩ =
      ⟨0, ls, true, true :: rs⟩ := by rfl

theorem a_zero_halt_gate (ls rs : List Bool) :
    run 2 ⟨0, ls, false, true :: true :: rs⟩ =
      ⟨5, true :: true :: ls, true, rs⟩ := by rfl

theorem a_zero_d_zero (ls rs : List Bool) (x : Bool) :
    run 5 ⟨0, ls, false, true :: false :: x :: false :: rs⟩ =
      ⟨0, false :: x :: false :: true :: true :: ls, rs.headD false, rs.tail⟩ := by
  cases x <;> simp [run, step, moveL, moveR]

theorem a_zero_d_one_c_zero (ls rs : List Bool) :
    run 6 ⟨0, ls, false, true :: false :: false :: true :: rs⟩ =
      ⟨0, true :: true :: ls, false, true :: false :: rs⟩ := by simp [run, step, moveL, moveR]

theorem a_zero_d_one_c_one (ls rs : List Bool) :
    run 7 ⟨0, ls, false, true :: false :: true :: true :: rs⟩ =
      ⟨0, true :: ls, true, true :: false :: false :: rs⟩ := by simp [run, step, moveL, moveR]

theorem run_add (m n : Nat) (c : Cfg) : run (m+n) c = run n (run m c) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
      simpa [run, Nat.succ_add] using (ih (step c))

theorem a_one_front (left right : List Bool) :
    run 3 ⟨0, left, true, right⟩ =
      ⟨4, left.tail, left.headD false, false :: right⟩ := by
  cases left with
  | nil => simp [run, step, moveL, moveR]
  | cons x xs => cases x <;> simp [run, step, moveL, moveR]

theorem e_scan_any (k : Nat) (x : Bool) (ls rs : List Bool) :
    run (k+1) ⟨4, (List.replicate k true ++ false :: x :: ls).tail,
                    (List.replicate k true ++ false :: x :: ls).headD false, false :: rs⟩ =
      ⟨0, ls, x, true :: List.replicate (k+1) false ++ rs⟩ := by
  cases k with
  | zero => rfl
  | succ k =>
      have zero_comm : ∀ n : Nat, (List.replicate n false ++ false :: rs) =
          false :: (List.replicate n false ++ rs) := by
        intro n
        induction n with
        | zero => rfl
        | succ n hn => simp [List.replicate, hn]
      simpa [List.replicate, zero_comm] using (e_sweep k x ls (false :: rs))

-- A at a 1 scans into C, D then E, and the full E sweep makes the next A.
theorem a_one_sweep (k : Nat) (x : Bool) (ls rs : List Bool) :
    run (k+4) ⟨0, List.replicate k true ++ false :: x :: ls, true, rs⟩ =
      ⟨0, ls, x, true :: List.replicate (k+1) false ++ rs⟩ := by
  have h := run_add 3 (k+1) ⟨0, List.replicate k true ++ false :: x :: ls, true, rs⟩
  have h' : 3+(k+1)=k+4 := by omega
  rw [h'] at h
  rw [h, a_one_front]
  exact e_scan_any k x ls rs

end BB6.Row262

#print axioms BB6.Row262.e_sweep
#print axioms BB6.Row262.a_one_sweep
#print axioms BB6.Row262.a_zero_halt_gate
#print axioms BB6.Row262.a_zero_d_zero
#print axioms BB6.Row262.a_zero_d_one_c_zero
#print axioms BB6.Row262.a_zero_d_one_c_one
#eval BB6.Row262.run 6 ⟨0, [], false, []⟩
#eval BB6.Row262.run 26 ⟨0, [], false, []⟩
