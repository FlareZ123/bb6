import Root56
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
namespace Raw11Extra126
open Root56

def transition (v : Fin 14) (q : Nat) (b : Bool) : Option (Bool × Bool × Fin 6) :=
  match q,b with
  | 0, false => some (true, true, 1)
  | 0, true => some (true, true, 3)
  | 1, false => some (true, true, 2)
  | 1, true => some (true, false, 3)
  | 2, false => some (false, false, 0)
  | 2, true => some (true, true, 4)
  | 3, false => some (true, false, 0)
  | 3, true => some (true, false, 1)
  | 4, false => match v.val with
    | 0 => none
    | 1 => none
    | 2 => none
    | 3 => none
    | 4 => none
    | 5 => none
    | 6 => some (false, true, 3)
    | 7 => none
    | 8 => some (false, false, 0)
    | 9 => some (false, true, 0)
    | 10 => some (true, false, 0)
    | 11 => some (true, false, 1)
    | 12 => some (false, true, 3)
    | 13 => some (true, false, 4)
    | _ => none
  | 4, true => match v.val with
    | 0 => some (false, true, 5)
    | 1 => some (false, true, 5)
    | 2 => some (false, true, 5)
    | 3 => some (false, true, 5)
    | 4 => some (false, true, 5)
    | 5 => some (false, true, 5)
    | 6 => some (true, true, 5)
    | 7 => some (true, true, 5)
    | 8 => some (true, true, 5)
    | 9 => some (true, true, 5)
    | 10 => some (true, true, 5)
    | 11 => some (true, true, 5)
    | 12 => some (true, true, 5)
    | 13 => some (true, true, 5)
    | _ => none
  | 5, false => match v.val with
    | 0 => some (true, false, 0)
    | 1 => some (false, true, 1)
    | 2 => some (false, false, 2)
    | 3 => some (true, false, 2)
    | 4 => some (false, false, 3)
    | 5 => some (true, false, 3)
    | 6 => none
    | 7 => some (false, true, 1)
    | 8 => none
    | 9 => none
    | 10 => none
    | 11 => none
    | 12 => none
    | 13 => none
    | _ => none
  | 5, true => match v.val with
    | 0 => some (false, false, 0)
    | 1 => some (false, false, 0)
    | 2 => some (false, false, 0)
    | 3 => some (false, false, 0)
    | 4 => some (false, false, 0)
    | 5 => some (false, false, 0)
    | 6 => some (false, false, 2)
    | 7 => some (true, true, 2)
    | 8 => some (false, true, 3)
    | 9 => some (false, true, 3)
    | 10 => some (false, true, 3)
    | 11 => some (false, true, 3)
    | 12 => some (false, true, 3)
    | 13 => some (false, true, 3)
    | _ => none
  | _,_ => none

def step (v : Fin 14) : Config → Option Config
  | (q,l,b,r) => (transition v q b).map fun (w,d,q') => if d then right q'.val l w r else left q'.val l w r

def run (v : Fin 14) : Nat → Config → Option Config
  | 0,s => some s
  | n+1,s => (step v s).bind (run v n)

theorem run_add (v : Fin 14) (n m : Nat) (s : Config) : run v (n+m) s = (run v n s).bind (run v m) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    rw [Nat.succ_add]; simp only [run]
    cases h : step v s with
    | none => rfl
    | some t => exact ih t

def ones : Nat → Side → Side
  | 0,s => s
  | n+1,s => true ::: ones n s

theorem ones_add (n m : Nat) (s : Side) : ones (n+m) s = ones n (ones m s) := by
  induction n with
  | zero => simp only [Nat.zero_add,ones]
  | succ n ih => simp only [Nat.succ_add,ones,ih]

def sec (n : Nat) : Config := c 4 (ones 2 z) true (ones n z)

theorem rightSweep (v : Fin 14) (a : Nat)
    (triple : ∀ l r, run v a (c 4 l true (ones 3 r)) = some (c 4 (ones 3 l) true r))
    (n : Nat) (l r : Side) : run v (a*n) (c 4 l true (ones (3*n) r)) = some (c 4 (ones (3*n) l) true r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm (a*n) a,run_add,show 3*(n+1)=3+3*n by omega,ones_add,triple]
    simp only [Option.bind_some]
    rw [ih,← ones_add,show 3*n+3=3+3*n by omega]

theorem leftPair (v : Fin 14) (q : Nat) (hq : q=1 ∨ q=3) (l r : Side) :
    run v 2 (c q (ones 2 l) true r) = some (c q l true (ones 2 r)) := by
  rcases hq with h|h <;> subst q <;> rfl

theorem leftSweep (v : Fin 14) (q : Nat) (hq : q=1 ∨ q=3) (n : Nat) (l r : Side) :
    run v (2*n) (c q (ones (2*n) l) true r) = some (c q l true (ones (2*n) r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,run_add,ones_add,leftPair v q hq]
    simp only [Option.bind_some]
    rw [ih,← ones_add,show 2*n+2=2+2*n by omega]

def cost (a T F n : Nat) := a*(2*n)+(T+(2*(3*n)+F))

theorem returnRule (v : Fin 14) (n a r T q L R F s : Nat)
    (triple : ∀ l r, run v a (c 4 l true (ones 3 r)) = some (c 4 (ones 3 l) true r))
    (turn : ∀ l, run v T (c 4 (ones 2 l) true (ones r z)) = some (c q (ones L l) true (ones R z)))
    (finish : ∀ u, run v F (c q (ones L z) true (ones R u)) = some (c 4 (ones 2 z) true (ones s u)))
    (hq : q=1 ∨ q=3) :
    run v (cost a T F n) (sec (6*n+r)) = some (sec (6*n+s)) := by
  have h1 := rightSweep v a triple (2*n) (ones 2 z) (ones r z)
  have h2 := turn (ones (6*n) z)
  have h3 := leftSweep v q hq (3*n) (ones L z) (ones R z)
  have h4 := finish (ones (6*n) z)
  unfold cost sec
  rw [run_add]
  rw [show 6*n+r=3*(2*n)+r by omega,ones_add,h1,Option.bind_some]
  have e1 : ones (3*(2*n)) (ones 2 z) = ones 2 (ones (6*n) z) := by
    rw [← ones_add,← ones_add]; congr 1 <;> omega
  rw [e1,run_add,h2,Option.bind_some]
  have e2 : ones L (ones (6*n) z) = ones (2*(3*n)) (ones L z) := by
    rw [← ones_add,← ones_add]; congr 1 <;> omega
  rw [e2,run_add,h3,Option.bind_some]
  have e3 : ones (2*(3*n)) (ones R z) = ones R (ones (6*n) z) := by
    rw [← ones_add,← ones_add]; congr 1 <;> omega
  rw [e3,h4,← ones_add,show s+6*n=6*n+s by omega]

theorem return_0_1 (n : Nat) : run 0 (cost 5 8 7 n) (sec (6*n+1)) = some (sec (6*n+3)) := by
  apply returnRule 0 n 5 1 8 3 4 0 7 3
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_0_3 (n : Nat) : run 0 (cost 5 8 13 n) (sec (6*n+3)) = some (sec (6*n+7)) := by
  apply returnRule 0 n 5 3 8 1 6 0 13 7
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_1_1 (n : Nat) : run 1 (cost 5 8 7 n) (sec (6*n+1)) = some (sec (6*n+3)) := by
  apply returnRule 1 n 5 1 8 3 4 0 7 3
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_1_3 (n : Nat) : run 1 (cost 5 16 13 n) (sec (6*n+3)) = some (sec (6*n+9)) := by
  apply returnRule 1 n 5 3 16 1 6 2 13 9
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_2_1 (n : Nat) : run 2 (cost 5 8 7 n) (sec (6*n+1)) = some (sec (6*n+3)) := by
  apply returnRule 2 n 5 1 8 3 4 0 7 3
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_2_3 (n : Nat) : run 2 (cost 5 11 12 n) (sec (6*n+3)) = some (sec (6*n+6)) := by
  apply returnRule 2 n 5 3 11 3 5 0 12 6
  · intro l u; rfl
  · intro l; simpa only [zero_push, ones] using (show run 2 11 (c 4 (ones 2 l) true (ones 3 z)) = some (c 3 (ones 5 l) true (false ::: z)) from rfl)
  · intro u; rfl
  · decide

theorem return_2_6 (n : Nat) : run 2 (cost 5 16 11 n) (sec (6*n+6)) = some (sec (6*n+7)) := by
  apply returnRule 2 n 5 6 16 3 8 0 11 7
  · intro l u; rfl
  · intro l; simpa only [zero_push, ones] using (show run 2 16 (c 4 (ones 2 l) true (ones 6 z)) = some (c 3 (ones 8 l) true (false ::: z)) from rfl)
  · intro u; rfl
  · decide

theorem return_3_1 (n : Nat) : run 3 (cost 5 8 7 n) (sec (6*n+1)) = some (sec (6*n+3)) := by
  apply returnRule 3 n 5 1 8 3 4 0 7 3
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_3_3 (n : Nat) : run 3 (cost 5 11 12 n) (sec (6*n+3)) = some (sec (6*n+7)) := by
  apply returnRule 3 n 5 3 11 3 5 1 12 7
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_4_1 (n : Nat) : run 4 (cost 5 8 7 n) (sec (6*n+1)) = some (sec (6*n+3)) := by
  apply returnRule 4 n 5 1 8 3 4 0 7 3
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_4_3 (n : Nat) : run 4 (cost 5 9 12 n) (sec (6*n+3)) = some (sec (6*n+6)) := by
  apply returnRule 4 n 5 3 9 3 5 0 12 6
  · intro l u; rfl
  · intro l; simpa only [zero_push, ones] using (show run 4 9 (c 4 (ones 2 l) true (ones 3 z)) = some (c 3 (ones 5 l) true (false ::: z)) from rfl)
  · intro u; rfl
  · decide

theorem return_4_6 (n : Nat) : run 4 (cost 5 14 11 n) (sec (6*n+6)) = some (sec (6*n+7)) := by
  apply returnRule 4 n 5 6 14 3 8 0 11 7
  · intro l u; rfl
  · intro l; simpa only [zero_push, ones] using (show run 4 14 (c 4 (ones 2 l) true (ones 6 z)) = some (c 3 (ones 8 l) true (false ::: z)) from rfl)
  · intro u; rfl
  · decide

theorem return_5_1 (n : Nat) : run 5 (cost 5 8 7 n) (sec (6*n+1)) = some (sec (6*n+3)) := by
  apply returnRule 5 n 5 1 8 3 4 0 7 3
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_5_3 (n : Nat) : run 5 (cost 5 9 12 n) (sec (6*n+3)) = some (sec (6*n+7)) := by
  apply returnRule 5 n 5 3 9 3 5 1 12 7
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_6_1 (n : Nat) : run 6 (cost 7 6 11 n) (sec (6*n+1)) = some (sec (6*n+5)) := by
  apply returnRule 6 n 7 1 6 1 4 0 11 5
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_6_5 (n : Nat) : run 6 (cost 7 17 12 n) (sec (6*n+5)) = some (sec (6*n+8)) := by
  apply returnRule 6 n 7 5 17 1 9 0 12 8
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_6_8 (n : Nat) : run 6 (cost 7 24 19 n) (sec (6*n+8)) = some (sec (6*n+13)) := by
  apply returnRule 6 n 7 8 24 1 12 0 19 13
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_7_1 (n : Nat) : run 7 (cost 3 6 7 n) (sec (6*n+1)) = some (sec (6*n+3)) := by
  apply returnRule 7 n 3 1 6 3 4 0 7 3
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_7_3 (n : Nat) : run 7 (cost 3 14 9 n) (sec (6*n+3)) = some (sec (6*n+7)) := by
  apply returnRule 7 n 3 3 14 3 6 2 9 7
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_8_1 (n : Nat) : run 8 (cost 5 4 11 n) (sec (6*n+1)) = some (sec (6*n+5)) := by
  apply returnRule 8 n 5 1 4 1 4 0 11 5
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_8_5 (n : Nat) : run 8 (cost 5 14 11 n) (sec (6*n+5)) = some (sec (6*n+7)) := by
  apply returnRule 8 n 5 5 14 3 8 0 11 7
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_9_1 (n : Nat) : run 9 (cost 5 4 11 n) (sec (6*n+1)) = some (sec (6*n+5)) := by
  apply returnRule 9 n 5 1 4 1 4 0 11 5
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_9_5 (n : Nat) : run 9 (cost 5 26 19 n) (sec (6*n+5)) = some (sec (6*n+13)) := by
  apply returnRule 9 n 5 5 26 1 12 0 19 13
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_10_1 (n : Nat) : run 10 (cost 5 4 11 n) (sec (6*n+1)) = some (sec (6*n+5)) := by
  apply returnRule 10 n 5 1 4 1 4 0 11 5
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_10_5 (n : Nat) : run 10 (cost 5 12 11 n) (sec (6*n+5)) = some (sec (6*n+7)) := by
  apply returnRule 10 n 5 5 12 3 8 0 11 7
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_11_1 (n : Nat) : run 11 (cost 5 4 11 n) (sec (6*n+1)) = some (sec (6*n+5)) := by
  apply returnRule 11 n 5 1 4 1 4 0 11 5
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_11_5 (n : Nat) : run 11 (cost 5 11 10 n) (sec (6*n+5)) = some (sec (6*n+7)) := by
  apply returnRule 11 n 5 5 11 1 7 1 10 7
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_12_1 (n : Nat) : run 12 (cost 5 4 11 n) (sec (6*n+1)) = some (sec (6*n+5)) := by
  apply returnRule 12 n 5 1 4 1 4 0 11 5
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_12_5 (n : Nat) : run 12 (cost 5 13 12 n) (sec (6*n+5)) = some (sec (6*n+8)) := by
  apply returnRule 12 n 5 5 13 1 9 0 12 8
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_12_8 (n : Nat) : run 12 (cost 5 18 19 n) (sec (6*n+8)) = some (sec (6*n+13)) := by
  apply returnRule 12 n 5 8 18 1 12 0 19 13
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_13_1 (n : Nat) : run 13 (cost 5 4 11 n) (sec (6*n+1)) = some (sec (6*n+5)) := by
  apply returnRule 13 n 5 1 4 1 4 0 11 5
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_13_5 (n : Nat) : run 13 (cost 5 15 12 n) (sec (6*n+5)) = some (sec (6*n+8)) := by
  apply returnRule 13 n 5 5 15 1 9 0 12 8
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide

theorem return_13_8 (n : Nat) : run 13 (cost 5 20 19 n) (sec (6*n+8)) = some (sec (6*n+13)) := by
  apply returnRule 13 n 5 8 20 1 12 0 19 13
  · intro l u; rfl
  · intro l; rfl
  · intro u; rfl
  · decide


theorem never_of_cycle (v : Fin 14) (r g seedTime : Nat)
    (seed : run v seedTime blank = some (sec r))
    (grow : ∀ n, ∃ d, 0<d ∧ run v d (sec (6*n+r)) = some (sec (6*(n+g)+r))) :
    ∀ n, run v n blank ≠ none := by
  have long : ∀ k, ∃ t n, k ≤ t ∧ run v t blank = some (sec (6*n+r)) := by
    intro k
    induction k with
    | zero => exact ⟨seedTime,0,by omega,by simpa using seed⟩
    | succ k ih =>
      obtain ⟨t,n,ht,hr⟩ := ih
      obtain ⟨d,hd,hs⟩ := grow n
      exact ⟨t+d,n+g,by omega,by rw [run_add,hr,Option.bind_some,hs]⟩
  intro n h
  obtain ⟨t,k,ht,hr⟩ := long n
  have hx := run_add v n (t-n) blank
  rw [Nat.add_sub_of_le ht,hr,h] at hx
  contradiction

theorem never_0 : ∀ n, run 0 n blank ≠ none := by
  apply never_of_cycle 0 1 1 11 (by rfl)
  intro n
  refine ⟨cost 5 8 7 n + (cost 5 8 13 n), by unfold cost; omega, ?_⟩
  rw [run_add, return_0_1, Option.bind_some]
  rw [return_0_3, show 6*n+7=6*(n+1)+1 by omega]
theorem never_1 : ∀ n, run 1 n blank ≠ none := by
  apply never_of_cycle 1 3 1 26 (by rfl)
  intro n
  refine ⟨cost 5 16 13 n, by unfold cost; omega, ?_⟩
  rw [return_1_3, show 6*n+9=6*(n+1)+3 by omega]
theorem never_2 : ∀ n, run 2 n blank ≠ none := by
  apply never_of_cycle 2 1 1 11 (by rfl)
  intro n
  refine ⟨cost 5 8 7 n + (cost 5 11 12 n + (cost 5 16 11 n)), by unfold cost; omega, ?_⟩
  rw [run_add, return_2_1, Option.bind_some]
  rw [run_add, return_2_3, Option.bind_some]
  rw [return_2_6, show 6*n+7=6*(n+1)+1 by omega]
theorem never_3 : ∀ n, run 3 n blank ≠ none := by
  apply never_of_cycle 3 1 1 11 (by rfl)
  intro n
  refine ⟨cost 5 8 7 n + (cost 5 11 12 n), by unfold cost; omega, ?_⟩
  rw [run_add, return_3_1, Option.bind_some]
  rw [return_3_3, show 6*n+7=6*(n+1)+1 by omega]
theorem never_4 : ∀ n, run 4 n blank ≠ none := by
  apply never_of_cycle 4 1 1 11 (by rfl)
  intro n
  refine ⟨cost 5 8 7 n + (cost 5 9 12 n + (cost 5 14 11 n)), by unfold cost; omega, ?_⟩
  rw [run_add, return_4_1, Option.bind_some]
  rw [run_add, return_4_3, Option.bind_some]
  rw [return_4_6, show 6*n+7=6*(n+1)+1 by omega]
theorem never_5 : ∀ n, run 5 n blank ≠ none := by
  apply never_of_cycle 5 1 1 11 (by rfl)
  intro n
  refine ⟨cost 5 8 7 n + (cost 5 9 12 n), by unfold cost; omega, ?_⟩
  rw [run_add, return_5_1, Option.bind_some]
  rw [return_5_3, show 6*n+7=6*(n+1)+1 by omega]
theorem never_6 : ∀ n, run 6 n blank ≠ none := by
  apply never_of_cycle 6 1 2 11 (by rfl)
  intro n
  refine ⟨cost 7 6 11 n + (cost 7 17 12 n + (cost 7 24 19 n)), by unfold cost; omega, ?_⟩
  rw [run_add, return_6_1, Option.bind_some]
  rw [run_add, return_6_5, Option.bind_some]
  rw [return_6_8, show 6*n+13=6*(n+2)+1 by omega]
theorem never_7 : ∀ n, run 7 n blank ≠ none := by
  apply never_of_cycle 7 1 1 11 (by rfl)
  intro n
  refine ⟨cost 3 6 7 n + (cost 3 14 9 n), by unfold cost; omega, ?_⟩
  rw [run_add, return_7_1, Option.bind_some]
  rw [return_7_3, show 6*n+7=6*(n+1)+1 by omega]
theorem never_8 : ∀ n, run 8 n blank ≠ none := by
  apply never_of_cycle 8 1 1 11 (by rfl)
  intro n
  refine ⟨cost 5 4 11 n + (cost 5 14 11 n), by unfold cost; omega, ?_⟩
  rw [run_add, return_8_1, Option.bind_some]
  rw [return_8_5, show 6*n+7=6*(n+1)+1 by omega]
theorem never_9 : ∀ n, run 9 n blank ≠ none := by
  apply never_of_cycle 9 1 2 11 (by rfl)
  intro n
  refine ⟨cost 5 4 11 n + (cost 5 26 19 n), by unfold cost; omega, ?_⟩
  rw [run_add, return_9_1, Option.bind_some]
  rw [return_9_5, show 6*n+13=6*(n+2)+1 by omega]
theorem never_10 : ∀ n, run 10 n blank ≠ none := by
  apply never_of_cycle 10 1 1 11 (by rfl)
  intro n
  refine ⟨cost 5 4 11 n + (cost 5 12 11 n), by unfold cost; omega, ?_⟩
  rw [run_add, return_10_1, Option.bind_some]
  rw [return_10_5, show 6*n+7=6*(n+1)+1 by omega]
theorem never_11 : ∀ n, run 11 n blank ≠ none := by
  apply never_of_cycle 11 1 1 11 (by rfl)
  intro n
  refine ⟨cost 5 4 11 n + (cost 5 11 10 n), by unfold cost; omega, ?_⟩
  rw [run_add, return_11_1, Option.bind_some]
  rw [return_11_5, show 6*n+7=6*(n+1)+1 by omega]
theorem never_12 : ∀ n, run 12 n blank ≠ none := by
  apply never_of_cycle 12 1 2 11 (by rfl)
  intro n
  refine ⟨cost 5 4 11 n + (cost 5 13 12 n + (cost 5 18 19 n)), by unfold cost; omega, ?_⟩
  rw [run_add, return_12_1, Option.bind_some]
  rw [run_add, return_12_5, Option.bind_some]
  rw [return_12_8, show 6*n+13=6*(n+2)+1 by omega]
theorem never_13 : ∀ n, run 13 n blank ≠ none := by
  apply never_of_cycle 13 1 2 11 (by rfl)
  intro n
  refine ⟨cost 5 4 11 n + (cost 5 15 12 n + (cost 5 20 19 n)), by unfold cost; omega, ?_⟩
  rw [run_add, return_13_1, Option.bind_some]
  rw [run_add, return_13_5, Option.bind_some]
  rw [return_13_8, show 6*n+13=6*(n+2)+1 by omega]

theorem never (v : Fin 14) (n : Nat) : run v n blank ≠ none := by
  have hv : v.val=0 ∨ v.val=1 ∨ v.val=2 ∨ v.val=3 ∨ v.val=4 ∨ v.val=5 ∨ v.val=6 ∨ v.val=7 ∨ v.val=8 ∨ v.val=9 ∨ v.val=10 ∨ v.val=11 ∨ v.val=12 ∨ v.val=13 := by omega
  rcases hv with h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · have hv : v = 0 := Fin.ext h
    subst v
    exact never_0 n
  · have hv : v = 1 := Fin.ext h
    subst v
    exact never_1 n
  · have hv : v = 2 := Fin.ext h
    subst v
    exact never_2 n
  · have hv : v = 3 := Fin.ext h
    subst v
    exact never_3 n
  · have hv : v = 4 := Fin.ext h
    subst v
    exact never_4 n
  · have hv : v = 5 := Fin.ext h
    subst v
    exact never_5 n
  · have hv : v = 6 := Fin.ext h
    subst v
    exact never_6 n
  · have hv : v = 7 := Fin.ext h
    subst v
    exact never_7 n
  · have hv : v = 8 := Fin.ext h
    subst v
    exact never_8 n
  · have hv : v = 9 := Fin.ext h
    subst v
    exact never_9 n
  · have hv : v = 10 := Fin.ext h
    subst v
    exact never_10 n
  · have hv : v = 11 := Fin.ext h
    subst v
    exact never_11 n
  · have hv : v = 12 := Fin.ext h
    subst v
    exact never_12 n
  · have hv : v = 13 := Fin.ext h
    subst v
    exact never_13 n
#print axioms returnRule
#print axioms never
end Raw11Extra126