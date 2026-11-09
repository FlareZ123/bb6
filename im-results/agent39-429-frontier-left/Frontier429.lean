import Std

namespace Frontier429

structure Z where
  state : Nat
  left : List Bool
  cur : Bool
  right : List Bool
  deriving DecidableEq, Repr

-- A=0, B=1, C=2, D=3, E=4, F=5.
def leftStep (state : Nat) (w : Bool) (z : Z) : Z :=
  { state, left := z.left.drop 1, cur := z.left.headD false, right := w :: z.right }

def rightStep (state : Nat) (w : Bool) (z : Z) : Z :=
  { state, left := w :: z.left, cur := z.right.headD false, right := z.right.drop 1 }

def step (z : Z) : Option Z :=
  match z.state, z.cur with
  | 0, false => some (rightStep 1 true z)
  | 0, true => some (leftStep 5 false z)
  | 1, false => some (rightStep 2 true z)
  | 1, true => some (rightStep 0 true z)
  | 2, false => some (rightStep 3 false z)
  | 2, true => some (rightStep 1 false z)
  | 3, false => some (leftStep 4 true z)
  | 3, true => none
  | 4, false => some (leftStep 0 false z)
  | 4, true => some (leftStep 4 true z)
  | 5, false => some (rightStep 3 true z)
  | 5, true => some (leftStep 0 true z)
  | _, _ => none

def run : Nat → Z → Option Z
  | 0, z => some z
  | n+1, z => (step z).bind (run n)

theorem run_add (n k : Nat) (z : Z) :
    run (n+k) z = (run n z).bind (run k) := by
  induction n generalizing z with
  | zero => simp [run]
  | succ n ih =>
    cases h : step z with
    | none => simp [run, h, Nat.succ_add]
    | some zz =>
      simp only [Nat.succ_add, run, h, Option.bind_some]
      exact ih zz

-- Short deterministic machine macros, independent of remote tape.
example (l r : List Bool) :
    run 2 ⟨0, true :: false :: l, true, r⟩ =
    some ⟨0, l, false, [true,false] ++ r⟩ := by
  simp [run, step, leftStep, rightStep]

example (l r : List Bool) :
    run 3 ⟨2, l, false, false :: r⟩ =
      some ⟨0, (l.drop 1), l.headD false, [false,true] ++ r⟩ := by
  simp [run, step, leftStep, rightStep]

end Frontier429

namespace Frontier429

def ones2 : Nat → List Bool
  | 0 => []
  | n+1 => true :: true :: ones2 n

def pairs : Nat → List Bool
  | 0 => []
  | n+1 => true :: false :: pairs n

theorem ones2_add (m n : Nat) : ones2 (m+n) = ones2 m ++ ones2 n := by
  induction m with
  | zero => simp [ones2]
  | succ m ih => simpa only [Nat.succ_add, ones2, ih, List.cons_append]

theorem ones2_rotate (m : Nat) (l : List Bool) :
    ones2 m ++ true :: true :: l = true :: true :: (ones2 m ++ l) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [ones2, List.cons_append]; simp only [ih]

theorem pairs_succ_tail (m : Nat) : pairs (m+1) = pairs m ++ [true,false] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc
      pairs ((m+1)+1) = true :: false :: pairs (m+1) := rfl
      _ = true :: false :: (pairs m ++ [true,false]) := by rw [ih]
      _ = pairs (m+1) ++ [true,false] := by simp [pairs]

theorem twoAF (l r : List Bool) (b : Bool) :
    run 2 ⟨0, true :: b :: l, true, r⟩ =
      some ⟨0, l, b, true :: false :: r⟩ := by
  simp [run, step, leftStep, rightStep]

theorem twoAB (l r : List Bool) :
    run 2 ⟨0, l, false, true :: false :: r⟩ =
      some ⟨0, true :: true :: l, false, r⟩ := by
  simp [run, step, leftStep, rightStep]

theorem finish4 (l : List Bool) :
    run 4 ⟨0, l, false, [false,true]⟩ =
      some ⟨2, [true,false,true,true] ++ l, false, []⟩ := by
  simp [run, step, leftStep, rightStep]

def ae (m : Nat) (l r : List Bool) : Z :=
  match m with
  | 0 => ⟨0, l, false, r⟩
  | n+1 => ⟨0, true :: ones2 n ++ false :: l, true, r⟩

theorem ae_pair (m : Nat) (l r : List Bool) :
    run 2 (ae (m+1) l r) = some (ae m l (true :: false :: r)) := by
  cases m with
  | zero => simp [ae, ones2, twoAF]
  | succ m => simp [ae, ones2, twoAF]

theorem ae_sweep (m : Nat) (l r : List Bool) :
    run (2*m) (ae m l r) = some (ae 0 l (pairs m ++ r)) := by
  induction m generalizing r with
  | zero => simp [run, ae, pairs]
  | succ m ih =>
    rw [show 2*(m+1) = 2 + 2*m by omega, run_add, ae_pair]
    simp only [Option.bind_some]
    rw [ih]
    simp [pairs_succ_tail, List.append_assoc]

theorem ab_sweep (m : Nat) (l r : List Bool) :
    run (2*m) ⟨0,l,false,pairs m ++ r⟩ =
      some ⟨0,ones2 m ++ l,false,r⟩ := by
  induction m generalizing l with
  | zero => simp [run, pairs, ones2]
  | succ m ih =>
    rw [show 2*(m+1) = 2+2*m by omega, run_add]
    simp only [pairs, List.cons_append, twoAB, Option.bind_some]
    rw [ih]
    rw [ones2_rotate]
    rfl

theorem cde3 (l r : List Bool) :
    run 3 ⟨2, false :: l, false, false :: r⟩ =
      some ⟨0, l, false, [false,true] ++ r⟩ := by
  simp [run, step, leftStep, rightStep]

theorem cdeBlank (b : Bool) (l : List Bool) :
    run 3 ⟨2, b :: l, false, []⟩ = some ⟨0,l,b,[false,true]⟩ := by
  simp [run, step, leftStep, rightStep]

theorem cdeEven (m : Nat) (l : List Bool) :
    run 3 ⟨2, ones2 m ++ false :: l, false, []⟩ =
    some (ae m l [false,true]) := by
  cases m with
  | zero => simpa [ones2, ae] using cdeBlank false l
  | succ m => simpa [ones2, ae] using cdeBlank true (true :: ones2 m ++ false :: l)

theorem even_root (m : Nat) (l : List Bool) :
    run (4*m+7) ⟨2, ones2 m ++ false :: l, false, []⟩ =
    some ⟨2, [true,false,true,true] ++ ones2 m ++ l, false, []⟩ := by
  let z : Z := ⟨2, ones2 m ++ false :: l, false, []⟩
  calc
    run (4*m+7) z = run (3 + (2*m + (2*m+4))) z := by congr 1; omega
    _ = (run 3 z).bind (run (2*m+(2*m+4))) := run_add 3 _ z
    _ = run (2*m+(2*m+4)) (ae m l [false,true]) := by rw [cdeEven]; rfl
    _ = (run (2*m) (ae m l [false,true])).bind (run (2*m+4)) := run_add _ _ _
    _ = run (2*m+4) (ae 0 l (pairs m++[false,true])) := by rw [ae_sweep]; rfl
    _ = (run (2*m) (ae 0 l (pairs m++[false,true]))).bind (run 4) := run_add _ _ _
    _ = run 4 ⟨0,ones2 m++l,false,[false,true]⟩ := by
      change (run (2*m) ⟨0,l,false,pairs m++[false,true]⟩).bind (run 4) = _
      rw [ab_sweep]; rfl
    _ = some ⟨2, [true,false,true,true] ++ ones2 m ++ l, false, []⟩ := finish4 _

end Frontier429

namespace Frontier429

def ao (m : Nat) (l r : List Bool) : Z :=
  ⟨0, ones2 m ++ [false,false,false] ++ l, true, r⟩

theorem ao_pair (m : Nat) (l r : List Bool) :
    run 2 (ao (m+1) l r) = some (ao m l (true :: false :: r)) := by
  simp [ao, ones2, twoAF, List.append_assoc]

theorem ao_sweep (m : Nat) (l r : List Bool) :
    run (2*m) (ao m l r) = some (ao 0 l (pairs m ++ r)) := by
  induction m generalizing r with
  | zero => simp [run, ao, pairs]
  | succ m ih =>
    rw [show 2*(m+1) = 2 + 2*m by omega, run_add, ao_pair]
    simp only [Option.bind_some]
    rw [ih]
    simp [pairs_succ_tail, List.append_assoc]

theorem ao_finish5 (l r : List Bool) :
    run 5 (ao 0 l r) = some ⟨0,l,false,[false,true,true] ++ r⟩ := by
  simp [ao, ones2, run, step, leftStep, rightStep]

theorem odd_first8 (m : Nat) (l : List Bool) :
    run 8 ⟨0,l,false,[false,true,true] ++ pairs (m+1) ++ [false,true]⟩ =
    some ⟨0,ones2 2 ++ l,false,false :: pairs m ++ [false,true]⟩ := by
  simp [pairs, ones2, run, step, leftStep, rightStep]

def cp : Nat → List Bool → Z
  | 0, l => ⟨2,l,false,[true]⟩
  | m+1, l => ⟨2,l,true,false :: pairs m ++ [false,true]⟩

theorem odd_a2c (m : Nat) (l : List Bool) :
    run 2 ⟨0,l,false,false :: pairs m ++ [false,true]⟩ =
    some (cp m (true :: true :: l)) := by
  cases m with
  | zero => simp [cp, pairs, run, step, leftStep, rightStep]
  | succ m => simp [cp, pairs, run, step, leftStep, rightStep]

theorem cp_pair (m : Nat) (l : List Bool) :
    run 2 (cp (m+1) l) = some (cp m (true :: false :: l)) := by
  cases m with
  | zero => simp [cp, pairs, run, step, leftStep, rightStep]
  | succ m => simp [cp, pairs, run, step, leftStep, rightStep]

theorem cp_sweep (m : Nat) (l : List Bool) :
    run (2*m) (cp m l) = some (cp 0 (pairs m ++ l)) := by
  induction m generalizing l with
  | zero => simp [run, cp, pairs]
  | succ m ih =>
    rw [show 2*(m+1) = 2 + 2*m by omega, run_add, cp_pair]
    simp only [Option.bind_some]
    rw [ih]
    simp [pairs_succ_tail, List.append_assoc]

theorem cdeOdd (m : Nat) (l : List Bool) :
    run 3 ⟨2, true :: ones2 m ++ [false,false,false] ++ l, false, []⟩ =
    some (ao m l [false,true]) := by
  simpa [ao] using cdeBlank true (ones2 m ++ [false,false,false] ++ l)

theorem odd_root (j : Nat) (l : List Bool) :
    run (4*j+20) ⟨2, true :: ones2 (j+1) ++ [false,false,false] ++ l, false, []⟩ =
    some ⟨2, pairs j ++ ones2 3 ++ l, false, [true]⟩ := by
  let z : Z := ⟨2, true :: ones2 (j+1) ++ [false,false,false] ++ l, false, []⟩
  calc
    run (4*j+20) z = run (3+(2*(j+1)+(5+(8+(2+2*j))))) z := by congr 1; omega
    _ = (run 3 z).bind (run (2*(j+1)+(5+(8+(2+2*j))))) := run_add _ _ _
    _ = run (2*(j+1)+(5+(8+(2+2*j)))) (ao (j+1) l [false,true]) := by rw [cdeOdd]; rfl
    _ = (run (2*(j+1)) (ao (j+1) l [false,true])).bind (run (5+(8+(2+2*j)))) := run_add _ _ _
    _ = run (5+(8+(2+2*j))) (ao 0 l (pairs (j+1) ++ [false,true])) := by rw [ao_sweep]; rfl
    _ = (run 5 (ao 0 l (pairs (j+1) ++ [false,true]))).bind (run (8+(2+2*j))) := run_add _ _ _
    _ = run (8+(2+2*j)) ⟨0,l,false,[false,true,true] ++ pairs (j+1) ++ [false,true]⟩ := by rw [ao_finish5]; rfl
    _ = (run 8 ⟨0,l,false,[false,true,true] ++ pairs (j+1) ++ [false,true]⟩).bind (run (2+2*j)) := run_add _ _ _
    _ = run (2+2*j) ⟨0,ones2 2 ++ l,false,false :: pairs j ++ [false,true]⟩ := by rw [odd_first8]; rfl
    _ = (run 2 ⟨0,ones2 2 ++ l,false,false :: pairs j ++ [false,true]⟩).bind (run (2*j)) := run_add _ _ _
    _ = run (2*j) (cp j (ones2 3 ++ l)) := by rw [odd_a2c]; rfl
    _ = some (cp 0 (pairs j ++ ones2 3 ++ l)) := by simpa [List.append_assoc] using (cp_sweep j (ones2 3 ++ l))
    _ = some ⟨2,pairs j ++ ones2 3 ++ l,false,[true]⟩ := rfl

-- The marked neighbor triggers the unique halt row D/1 after one more move.
theorem odd_D1 (j : Nat) (l : List Bool) :
    run (4*j+21) ⟨2, true :: ones2 (j+1) ++ [false,false,false] ++ l, false, []⟩ =
    some ⟨3, false :: pairs j ++ ones2 3 ++ l, true, []⟩ := by
  rw [show 4*j+21 = (4*j+20)+1 by omega, run_add, odd_root]
  rfl

theorem odd_halts (j : Nat) (l : List Bool) :
    run (4*j+22) ⟨2, true :: ones2 (j+1) ++ [false,false,false] ++ l, false, []⟩ = none := by
  rw [show 4*j+22 = (4*j+21)+1 by omega, run_add, odd_D1]
  rfl

#print axioms even_root
#print axioms odd_root
#print axioms odd_D1
#print axioms odd_halts

end Frontier429
