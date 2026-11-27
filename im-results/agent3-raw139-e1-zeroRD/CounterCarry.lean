import Std
import Lean.Elab.Tactic.Omega

namespace CounterCarry
abbrev Ray := Nat → Bool
abbrev z := false
abbrev o := true

def nilRay : Ray := fun _ => false
def cons (b : Bool) (r : Ray) : Ray
  | 0 => b
  | n+1 => r n

def tail (r : Ray) : Ray := fun n => r (n+1)
def pair (a b : Bool) (r : Ray) : Ray := cons a (cons b r)

@[simp] theorem cons_zero_blank : cons z nilRay = nilRay := by
  funext n; cases n <;> rfl

inductive Variant where
  | d0 | b1 | d1
  deriving DecidableEq, Repr

structure C where
  q : Fin 6
  l : Ray
  r : Ray

def A0 (l r : Ray) : C := ⟨0,l,pair z z r⟩
def A1 (l r : Ray) : C := ⟨0,l,pair o z r⟩
def C2 (l r : Ray) : C := ⟨2,l,r⟩

-- The only absent slot is F0. Three literal siblings differ at E0/F1.
def table (v : Variant) (q : Fin 6) (b : Bool) : Option (Bool × Bool × Fin 6) :=
  match q.val, b with
  | 0, false => some (true,true,1)
  | 0, true => some (false,false,3)
  | 1, false => some (true,true,2)
  | 1, true => some (true,false,3)
  | 2, false => some (true,false,3)
  | 2, true => some (false,true,1)
  | 3, false => some (false,false,0)
  | 3, true => some (false,false,4)
  | 4, false => some (v == .d1,false,5)
  | 4, true => some (false,true,3)
  | 5, false => none
  | 5, true => match v with
    | .d0 => some (false,true,3)
    | .b1 => some (true,true,1)
    | .d1 => some (true,true,3)
  | _, _ => none

def step (v : Variant) (c : C) : Option C :=
  (table v c.q (c.r 0)).map fun (w,d,q) =>
    if d then ⟨q, cons w c.l, tail c.r⟩
    else ⟨q, tail c.l, cons (c.l 0) (cons w (tail c.r))⟩

def run (v : Variant) : Nat → C → Option C
  | 0,c => some c
  | n+1,c => (step v c).bind (run v n)

theorem run_add (v : Variant) (n k : Nat) (c : C) :
    run v (n+k) c = (run v n c).bind (run v k) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [run]
    cases step v c with
    | none => rfl
    | some t => exact ih t

def Reach (v : Variant) (c d : C) : Prop := ∃ n, run v n c = some d
def Plus (v : Variant) (c d : C) : Prop := ∃ n, n > 0 ∧ run v n c = some d

theorem Reach.refl (v : Variant) (c : C) : Reach v c c := ⟨0,rfl⟩
theorem Reach.trans {v : Variant} {c d e : C} (h : Reach v c d) (g : Reach v d e) : Reach v c e := by
  obtain ⟨n,hn⟩ := h; obtain ⟨k,hk⟩ := g
  exact ⟨n+k, by rw [run_add,hn]; exact hk⟩
theorem Plus.reach {v : Variant} {c d : C} (h : Plus v c d) : Reach v c d := by
  obtain ⟨n,_,hn⟩ := h; exact ⟨n,hn⟩
theorem Plus.thenReach {v : Variant} {c d e : C} (h : Plus v c d) (g : Reach v d e) : Plus v c e := by
  obtain ⟨n,hn,h⟩ := h; obtain ⟨k,hk⟩ := g
  exact ⟨n+k, by omega, by rw [run_add,h]; exact hk⟩

-- Repeated pair 10, 00, or 01 respectively, outward from the head.
def ones : Nat → Ray → Ray
  | 0,r => r
  | n+1,r => pair o z (ones n r)
def zeros : Nat → Ray → Ray
  | 0,r => r
  | n+1,r => pair z z (zeros n r)
def stack : Nat → Ray → Ray
  | 0,l => l
  | n+1,l => pair z o (stack n l)

theorem ones_shift (n : Nat) (r : Ray) : ones n (pair o z r) = ones (n+1) r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ones]; rw [ih]; rfl
theorem zeros_shift (n : Nat) (r : Ray) : zeros n (pair z z r) = zeros (n+1) r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zeros]; rw [ih]; rfl
theorem stack_shift (n : Nat) (l : Ray) : stack n (pair z o l) = stack (n+1) l := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stack]; rw [ih]; rfl
theorem zeros_cons (n : Nat) (r : Ray) : cons z (zeros n r) = zeros n (cons z r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [zeros, pair]
    rw [← ih]

-- All displayed finite local rules leave both hidden rays unchanged.
theorem inc0 (v : Variant) (l r : Ray) : Plus v (A0 l (cons z r)) (A0 l (cons o r)) := by
  cases v <;> exact ⟨6,by decide,rfl⟩

theorem start_scan (v : Variant) (l r : Ray) : Plus v (A0 l r) (C2 (pair o o l) r) :=
  ⟨2,by decide,rfl⟩

theorem scan (v : Variant) (k : Nat) (l r : Ray) :
    Reach v (C2 (cons o l) (ones k r)) (C2 (cons o (stack k l)) r) := by
  induction k generalizing l with
  | zero => exact Reach.refl _ _
  | succ k ih =>
    have h : Reach v (C2 (cons o l) (ones (k+1) r))
      (C2 (cons o (pair z o l)) (ones k r)) := ⟨2,rfl⟩
    apply Reach.trans h
    rw [← stack_shift]
    exact ih (pair z o l)

theorem jump (v : Variant) (k : Nat) (l r : Ray) :
    Reach v (A0 l (ones k (pair o o r))) (A1 (stack k (cons o l)) (cons o r)) := by
  apply Reach.trans (start_scan v l _).reach
  apply Reach.trans (scan v k (cons o l) (pair o o r))
  exact ⟨3,rfl⟩

theorem pop (v : Variant) (k : Nat) (l r : Ray) :
    Reach v (A1 (stack k l) r) (A1 l (zeros k r)) := by
  induction k generalizing r with
  | zero => exact Reach.refl _ _
  | succ k ih =>
    have h : Reach v (A1 (stack (k+1) l) r) (A1 (stack k l) (pair z z r)) := ⟨2,rfl⟩
    apply Reach.trans h
    rw [← zeros_shift]
    exact ih (pair z z r)

theorem exit_one (v : Variant) (k : Nat) (l r : Ray) :
    Reach v (A0 (cons o l) (ones k (pair o o r))) (A0 l (zeros (k+1) (cons o r))) := by
  apply Reach.trans (jump v k (cons o l) r)
  apply Reach.trans (pop v k (pair o o l) (cons o r))
  cases v <;> exact ⟨4,rfl⟩

-- When the left context ends in 10 in physical tape order, the exit
-- shifts left twice. Its n+1 low digit positions are zero, except that
-- the b1 variant sets the first one; their terminal pair is 01.
def afterPair (v : Variant) (n : Nat) (r : Ray) : Ray :=
  match v with
  | .b1 => pair o z (zeros n (pair z o r))
  | _ => zeros (n+1) (pair z o r)
theorem exit_pair (v : Variant) (k : Nat) (l r : Ray) :
    Reach v (A0 (pair z o l) (ones k (pair o o r))) (A0 l (afterPair v k r)) := by
  apply Reach.trans (jump v k (pair z o l) r)
  apply Reach.trans (pop v k (cons o (pair z o l)) (cons o r))
  cases v with
  | d0 =>
    refine ⟨5,?_⟩
    change some (A0 l (pair z z (cons z (zeros k (cons o r))))) = _
    rw [zeros_cons]; rfl
  | b1 =>
    refine ⟨9,?_⟩
    change some (A0 l (pair o z (cons z (zeros k (cons o r))))) = _
    rw [zeros_cons]; rfl
  | d1 =>
    refine ⟨7,?_⟩
    change some (A0 l (pair z z (cons z (zeros k (cons o r))))) = _
    rw [zeros_cons]; rfl

-- Initial scan through k+1 ones, followed by the first right turn.
-- The scan stack has k pending 10 pairs plus a single 1.
theorem turn (v : Variant) (k : Nat) (l r : Ray) :
    Plus v (A0 l (ones (k+1) (cons z r)))
      (A0 (stack k (cons o l)) (pair o o r)) := by
  apply Plus.thenReach (start_scan v l _)
  apply Reach.trans (scan v (k+1) (cons o l) (cons z r))
  cases v with
  | d0 =>
    have h : Reach Variant.d0 (C2 (cons o (stack (k+1) (cons o l))) (cons z r))
        (A0 (stack k (cons o l)) (pair z o r)) := ⟨5,rfl⟩
    exact h.trans (inc0 _ _ _).reach
  | b1 => exact ⟨9,rfl⟩
  | d1 =>
    have h : Reach Variant.d1 (C2 (cons o (stack (k+1) (cons o l))) (cons z r))
        (A0 (stack k (cons o l)) (pair z o r)) := ⟨7,rfl⟩
    exact h.trans (inc0 _ _ _).reach

-- Main inductive carry specification, positive time and arbitrary hidden rays.
def Increment (v : Variant) (k : Nat) : Prop :=
  ∀ l r, Plus v (A0 l (ones k (cons z r))) (A0 l (zeros k (cons o r)))

-- Fill n low bits (currently zero) while preserving the tail; only smaller
-- increments are used. This is induction on the size of the low-bit block.
theorem fillLow (v : Variant) (n : Nat) (h : ∀ i < n, Increment v i) (l r : Ray) :
    Reach v (A0 l (zeros n r)) (A0 l (ones n r)) := by
  induction n generalizing r with
  | zero => exact Reach.refl _ _
  | succ n ih =>
    rw [← zeros_shift, ← ones_shift]
    have hsmall : ∀ i < n, Increment v i := fun i hi => h i (by omega)
    apply Reach.trans (ih hsmall (pair z z r))
    apply Reach.trans ((h n (by omega) l (cons z r)).reach)
    exact ih hsmall (pair o z r)

-- The b1 variant begins filling with the first low digit already one.
theorem fillLowOne (v : Variant) (n : Nat) (h : ∀ i < n+1, Increment v i) (l r : Ray) :
    Reach v (A0 l (pair o z (zeros n r))) (A0 l (ones (n+1) r)) := by
  induction n generalizing r with
  | zero => exact Reach.refl _ _
  | succ n ih =>
    rw [← zeros_shift, ← ones_shift]
    have hsmall : ∀ i < n+1, Increment v i := fun i hi => h i (by omega)
    apply Reach.trans (ih hsmall (pair z z r))
    apply Reach.trans ((h (n+1) (by omega) l (cons z r)).reach)
    exact fillLow v (n+1) hsmall l (pair o z r)

theorem fill_after (v : Variant) (n : Nat) (h : ∀ i ≤ n+1, Increment v i) (l r : Ray) :
    Reach v (A0 l (afterPair v n r)) (A0 l (ones (n+1) (pair o o r))) := by
  have hsmall : ∀ i < n+1, Increment v i := fun i hi => h i (by omega)
  have hfill : Reach v (A0 l (afterPair v n r)) (A0 l (ones (n+1) (pair z o r))) := by
    cases v with
    | d0 => exact fillLow _ _ hsmall _ _
    | d1 => exact fillLow _ _ hsmall _ _
    | b1 => exact fillLowOne _ _ hsmall _ _
  apply Reach.trans hfill
  apply Reach.trans ((h (n+1) (by omega) l (cons o r)).reach)
  exact fillLow _ _ hsmall _ _

-- Drain k pending left pairs. At each step fill one more low position
-- using carries of size at most n+k. The last exit consumes the single 1.
theorem returnLoop (v : Variant) (k n : Nat) (h : ∀ i ≤ n+k, Increment v i) (l r : Ray) :
    Reach v (A0 (stack k (cons o l)) (ones n (pair o o r)))
      (A0 l (zeros (n+k+1) (cons o r))) := by
  induction k generalizing n with
  | zero => simpa [stack] using exit_one v n l r
  | succ k ih =>
    apply Reach.trans (exit_pair v n (stack k (cons o l)) r)
    apply Reach.trans (fill_after v n (fun i hi => h i (by omega)) (stack k (cons o l)) r)
    have he : n+(k+1)+1=(n+1)+k+1 := by omega
    rw [he]
    exact ih (n+1) (fun i hi => h i (by omega))

theorem increments_through (v : Variant) (k : Nat) : ∀ i ≤ k, Increment v i := by
  induction k with
  | zero =>
    intro i hi
    have he : i = 0 := by omega
    subst i
    exact inc0 v
  | succ k ih =>
    intro i hi
    by_cases his : i ≤ k
    · exact ih i his
    · have he : i = k+1 := by omega
      subst i
      intro l r
      apply Plus.thenReach (turn v k l r)
      simpa only [ones, Nat.zero_add] using returnLoop v k 0 (fun i hi => ih i (by omega)) l r

theorem increment (v : Variant) (k : Nat) : Increment v k :=
  increments_through v k k (Nat.le_refl k)

-- Finite binary words in low-to-high order with zero ray extension.
def encode : List Bool → Ray
  | [] => nilRay
  | b::bs => pair b z (encode bs)
def incBits : List Bool → List Bool
  | [] => [o]
  | false::bs => o::bs
  | true::bs => z::incBits bs

theorem inc_prefix (bs : List Bool) :
    ∃ k r, encode bs = ones k (cons z r) ∧ encode (incBits bs) = zeros k (cons o r) := by
  induction bs with
  | nil =>
    refine ⟨0,cons z nilRay,?_,rfl⟩
    simp [encode,ones,cons_zero_blank]
  | cons b bs ih =>
    cases b with
    | false => exact ⟨0,cons z (encode bs),rfl,rfl⟩
    | true =>
      obtain ⟨k,r,h1,h2⟩ := ih
      refine ⟨k+1,r,?_,?_⟩
      · simp only [encode,ones,h1]
      · simp only [incBits,encode,zeros,h2]

theorem counter_step (v : Variant) (bs : List Bool) :
    Plus v (A0 nilRay (encode bs)) (A0 nilRay (encode (incBits bs))) := by
  obtain ⟨k,r,h1,h2⟩ := inc_prefix bs
  rw [h1,h2]
  exact increment v k _ _

def digits : Nat → List Bool
  | 0 => []
  | n+1 => incBits (digits n)
def cfg (n : Nat) : C := A0 nilRay (encode (digits n))
def blankC : C := ⟨0,nilRay,nilRay⟩

theorem cfg_zero : cfg 0 = blankC := by
  simp [cfg,digits,A0,encode,pair,blankC]

theorem long_prefix (v : Variant) (n : Nat) : ∃ k, n ≤ k ∧ run v k blankC = some (cfg n) := by
  induction n with
  | zero => exact ⟨0,by decide,by rw [cfg_zero]; rfl⟩
  | succ n ih =>
    obtain ⟨k,hk,hr⟩ := ih
    obtain ⟨j,hj,hs⟩ := counter_step v (digits n)
    exact ⟨k+j,by omega,by rw [run_add,hr]; exact hs⟩

theorem never (v : Variant) : ∀ n, ∃ c, run v n blankC = some c := by
  intro n
  obtain ⟨k,hk,hr⟩ := long_prefix v n
  cases h : run v n blankC with
  | some c => exact ⟨c,rfl⟩
  | none =>
    obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hk
    rw [hj,run_add,h] at hr
    contradiction

#print axioms increment
#print axioms never
end CounterCarry
