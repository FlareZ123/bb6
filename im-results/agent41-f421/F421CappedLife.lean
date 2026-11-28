import F421SecondaryLifetimes

set_option linter.unusedSimpArgs false

namespace F421CappedLife
open F421SecondaryLifetimes

/-- At a horizon of h cycles, only lifetimes at most h can expire. -/
def small (h : Nat) (xs : List Nat) : List Nat := xs.filter (· ≤ h)

theorem small_cons (h x : Nat) (xs : List Nat) :
    small h (x::xs) = if x≤h then x::small h xs else small h xs := by
  simp [small,List.filter_cons]

theorem small_append (h : Nat) (xs ys : List Nat) :
    small h (xs++ys)=small h xs++small h ys := by simp [small]

/-- Erasing lifetimes > h+1 changes neither this step's deletion count nor
    the projection to lifetimes at most h after the step. No positivity
    assumption is needed; the source recurrence also defines zero entries. -/
theorem advanceAux_small (h d : Nat) (xs : List Nat) :
    (advanceAux d (small (h+1) xs)).2 = (advanceAux d xs).2 ∧
    small h (advanceAux d (small (h+1) xs)).1 = small h (advanceAux d xs).1 := by
  induction xs generalizing d with
  | nil => simp [advanceAux,small]
  | cons x xs ih =>
    by_cases hx : x≤h+1
    · rw [small_cons,ite_eq_left hx]
      by_cases h1 : x=1
      · simpa [advanceAux,h1] using ih (d+1)
      · have H := ih d
        rcases ha : advanceAux d (small (h+1) xs) with ⟨us,e⟩
        rcases hb : advanceAux d xs with ⟨vs,f⟩
        rw [ha,hb] at H
        simp only [Prod.fst,Prod.snd] at H
        simp only [advanceAux,ite_eq_right h1,ha,hb,Prod.fst,Prod.snd,small_cons,H.1,H.2, true_and]
    · have h1 : x≠1 := by omega
      have hp : 0<2^d := Nat.pow_pos (by decide)
      have hmul : x-1≤(x-1)*2^d := Nat.le_mul_of_pos_right _ hp
      have hv : ¬ (x-1)*2^d≤h := by omega
      rw [small_cons,ite_eq_right hx]
      have H := ih d
      rcases hb : advanceAux d xs with ⟨vs,f⟩
      rw [hb] at H
      simpa only [advanceAux,ite_eq_right h1,hb,Prod.fst,Prod.snd,small_cons,ite_eq_right hv] using H

theorem aux_length (d : Nat) (xs : List Nat) :
    (advanceAux d xs).1.length+(advanceAux d xs).2=xs.length+d := by
  induction xs generalizing d with
  | nil => simp [advanceAux]
  | cons x xs ih =>
    by_cases hx : x=1
    · simp only [advanceAux,ite_eq_left hx,List.length_cons]
      have H:=ih (d+1)
      omega
    · rcases he : advanceAux d xs with ⟨ys,D⟩
      have H:=ih d
      rw [he] at H
      simp only [Prod.fst,Prod.snd] at H
      simp only [advanceAux,ite_eq_right hx,he,List.length_cons]
      omega

theorem advance_length (xs : List Nat) :
    (advance xs).length=xs.length+1-(advanceAux 0 xs).2 := by
  have H:=aux_length 0 xs
  rcases he : advanceAux 0 xs with ⟨ys,D⟩
  rw [he] at H
  simp only [Prod.fst,Prod.snd,Nat.add_zero] at H
  simp only [advance,he,List.length_append,List.length_singleton,Prod.snd]
  omega

/-- State stores total cell count and only the active finite-horizon subsequence. -/
abbrev State := Nat × List Nat

def encode (h : Nat) (xs : List Nat) : State := (xs.length,small h xs)

def next (h : Nat) (s : State) : State :=
  let (ys,D) := advanceAux 0 s.2
  (s.1+1-D,small h (ys++[2^(D+1)]))

theorem next_encode (h : Nat) (xs : List Nat) :
    next h (encode (h+1) xs)=encode h (advance xs) := by
  have H:=advanceAux_small h 0 xs
  have HL:=advance_length xs
  rcases ha : advanceAux 0 (small (h+1) xs) with ⟨us,e⟩
  rcases hb : advanceAux 0 xs with ⟨vs,f⟩
  rw [ha,hb] at H
  rw [hb] at HL
  simp only [Prod.fst,Prod.snd] at H HL
  have HL2 : (vs++[2^(f+1)]).length=xs.length+1-f := by simpa only [advance,hb] using HL
  simp only [next,encode,ha,advance,hb,Prod.fst,Prod.snd,HL2,H.1,small_append,H.2]

def iter : Nat → State → State
  | 0,s => s
  | k+1,s => iter k (next k s)

def slowIter : Nat → List Nat → List Nat
  | 0,xs => xs
  | k+1,xs => slowIter k (advance xs)

theorem iter_encode (k : Nat) (xs : List Nat) :
    iter k (encode k xs)=encode 0 (slowIter k xs) := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => simp only [iter,slowIter,next_encode,ih]

/-- Prefix n steps of a k+n horizon, so the horizon passed to every next
    operation is exact. This enables small independent kernel checkpoints. -/
def chunk : Nat → Nat → State → State
  | 0,_,s => s
  | n+1,k,s => chunk n k (next (k+n) s)

theorem iter_chunk (n k : Nat) (s : State) :
    iter (k+n) s=iter k (chunk n k s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change iter (k+n) (next (k+n) s)=iter k (chunk n k (next (k+n) s))
    exact ih _

def first : State := encode 32750 [327661,14,30,6,22,14,1,2]

#print axioms iter_encode
#print axioms iter_chunk
#eval (iter 32750 first).1

end F421CappedLife
