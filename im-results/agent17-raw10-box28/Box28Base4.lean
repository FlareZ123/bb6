import Box33BinaryCounter

namespace BB6.Agent17.Box28Base4
open C9Pair
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)

def step (alt : Bool) (c : Config) : Option Config :=
  match c.q, c.a with
  | .A, false => some (right .B true c)
  | .A, true => none
  | .B, false => some (left .C true c)
  | .B, true => some (right .F true c)
  | .C, false => some (left .C true c)
  | .C, true => some (left .D false c)
  | .D, false => some (right .D false c)
  | .D, true => some (left .E false c)
  | .E, false => some (right .F false c)
  | .E, true => some (left (if alt then .E else .C) false c)
  | .F, false => some (left .E true c)
  | .F, true => some (right .A true c)

def run (alt : Bool) : Nat → Config → Option Config
  | 0, c => some c
  | n+1, c => (step alt c).bind (run alt n)

theorem run_add (alt : Bool) (m n : Nat) (c : Config) :
    run alt (m+n) c = (run alt m c).bind (run alt n) := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih =>
    simp only [Nat.succ_add, run]
    cases step alt c <;> simp [ih]

inductive Digit where | zero | one | two | three

def block (b c : Bool) (s : Stream) : Stream := push false (push b (push c s))

def encode : List Digit → Stream
  | [] => zeros
  | .zero :: ds => block false false (encode ds)
  | .one :: ds => block true false (encode ds)
  | .two :: ds => block false true (encode ds)
  | .three :: ds => block true true (encode ds)

def root (ds : List Digit) : Config := ⟨.E, zeros, false, push false (encode ds)⟩
def atA (k : Nat) (r : Stream) : Config := ⟨.A, ones (3*k+1), r 0, pop r⟩
def atE (l r : Stream) : Config := ⟨.E, pop l, l 0, r⟩

theorem zeroes_encode (k : Nat) (ds : List Digit) :
    encode (List.replicate k .zero ++ ds) = rep false (3*k) (encode ds) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, encode, ih]
    have h : 3*(k+1) = 3*k+3 := by omega
    rw [h]
    rfl

theorem clear3 (alt : Bool) (n : Nat) (r : Stream) :
    run alt 3 (atE (ones (n+3)) r) = some (atE (ones n) (rep false 3 r)) := by
  cases alt <;> simp [atE, run, step, left, ones, rep, pop_push, push_zero]

theorem clear_all (alt : Bool) (k : Nat) (r : Stream) :
    run alt (3*k) (atE (ones (3*k)) r) =
      some (atE zeros (rep false (3*k) r)) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    have h : 3*(k+1) = 3+3*k := by omega
    rw [h, run_add]
    rw [show 3+3*k = 3*k+3 by omega, clear3, Option.bind_some, ih, ← rep_add]

theorem start (alt : Bool) (ds : List Digit) :
    run alt 4 (root ds) = some (atA 0 (encode ds)) := by
  simp [root, atA, run, step, left, right, ones, rep, pop_push, push_zero]

theorem carry (alt : Bool) (k : Nat) (s : Stream) :
    run alt 3 (atA k (block true true s)) = some (atA (k+1) s) := by
  have h : 3*(k+1)+1 = (3*k+1)+3 := by omega
  simp [atA, block, run, step, right, ones, rep, h, pop_push, push_zero]

theorem stop_even (alt : Bool) (k : Nat) (b : Bool) (s : Stream) :
    run alt 4 (atA k (block false b s)) =
      some (atE (ones (3*k)) (push false (block true b s))) := by
  simp [atA, atE, block, run, step, left, right, ones, rep, pop_push, push_zero]

theorem stop_one (alt : Bool) (k : Nat) (s : Stream) :
    run alt 3 (atA k (block true false s)) =
      some (atE (ones (3*(k+1))) (push true s)) := by
  have h : 3*(k+1) = (3*k+1)+2 := by omega
  simp [atA, atE, block, run, step, left, right, ones, rep, h, pop_push, push_zero]

theorem even_return (alt : Bool) (k : Nat) (b : Bool) (ds : List Digit) :
    run alt (4+3*k) (atA k (block false b (encode ds))) =
      some (root (List.replicate k .zero ++ (if b then .three else .one) :: ds)) := by
  rw [run_add, stop_even, Option.bind_some, clear_all]
  cases b <;>
    simp [root, atE, zeroes_encode, encode, block, ← rep_add, rep]

theorem one_return (alt : Bool) (k : Nat) (ds : List Digit) :
    run alt (3+3*(k+1)) (atA k (block true false (encode ds))) =
      some (root (List.replicate k .zero ++ .two :: ds)) := by
  rw [run_add, stop_one, Option.bind_some, clear_all]
  simp [root, atE, zeroes_encode, encode, block]
  congr 1
  change rep false (3*(k+1)) (push true (encode ds)) =
    rep false 1 (rep false (3*k) (rep false 2 (push true (encode ds))))
  rw [← rep_add, ← rep_add]
  congr 1 <;> omega

theorem walk (alt : Bool) (ds : List Digit) (k : Nat) :
    ∃ n ds', 0<n ∧ run alt n (atA k (encode ds)) = some (root ds') := by
  induction ds generalizing k with
  | nil =>
    refine ⟨4+3*k, List.replicate k .zero ++ [.one], by omega, ?_⟩
    simpa [encode, block] using even_return alt k false []
  | cons d ds ih =>
    cases d with
    | zero => exact ⟨4+3*k, _, by omega, even_return alt k false ds⟩
    | one => exact ⟨3+3*(k+1), _, by omega, one_return alt k ds⟩
    | two => exact ⟨4+3*k, _, by omega, even_return alt k true ds⟩
    | three =>
      obtain ⟨n, ds', hn, hr⟩ := ih (k+1)
      exact ⟨3+n, ds', by omega, by rw [encode, run_add, carry, Option.bind_some, hr]⟩

theorem progress (alt : Bool) (ds : List Digit) :
    ∃ n ds', 0<n ∧ run alt n (root ds) = some (root ds') := by
  obtain ⟨n, ds', hn, hr⟩ := walk alt ds 0
  exact ⟨4+n, ds', by omega, by rw [run_add, start, Option.bind_some, hr]⟩

theorem never_root (alt : Bool) (n : Nat) (ds : List Digit) :
    run alt n (root ds) ≠ none := by
  induction n using Nat.strongRecOn generalizing ds with
  | ind n ih =>
    obtain ⟨k, ds', hk, hr⟩ := progress alt ds
    intro h
    by_cases hnk : n ≤ k
    · have e : k = n+(k-n) := by omega
      rw [e, run_add, h] at hr
      contradiction
    · have e : n = k+(n-k) := by omega
      rw [e, run_add, hr] at h
      exact ih (n-k) (by omega) ds' h

def blank : Config := ⟨.A, zeros, false, zeros⟩

theorem init (alt : Bool) : run alt 6 blank = some (root []) := by
  simp [blank, root, encode, run, step, left, right, zeros, pop_push, push_zero]

theorem never_blank (alt : Bool) (n : Nat) : run alt n blank ≠ none := by
  intro h
  by_cases hn : n ≤ 6
  · have hi := init alt
    have e : 6 = n+(6-n) := by omega
    rw [e, run_add, h] at hi
    contradiction
  · have e : n = 6+(n-6) := by omega
    rw [e, run_add, init] at h
    exact never_root alt (n-6) [] h

end BB6.Agent17.Box28Base4
