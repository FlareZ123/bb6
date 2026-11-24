import Std
import Lean.Elab.Tactic.Omega

namespace Cap

/-- Exact copy of the numerical part of the upstream `evalD0`, with `C` erased. -/
def eval (b c : Nat) : Option Nat :=
  let k := min (b / 2) c
  let a1 := 2 * k
  let b1 := b - 2 * k
  let c1 := c - k
  if c1 > 0 then
    if b1 = 0 then some (4 * a1 + 2 * c1 + 11)
    else if c1 = 1 then some (4 * a1 + 15)
    else some (4 * a1 + 2 * c1 + 13)
  else if b1 = 0 then some (4 * a1 + 11)
  else if b1 = 1 then some (4 * a1 + 13)
  else if b1 = 2 then some (4 * a1 + 17)
  else if b1 = 3 ∨ b1 = 4 then none
  else if b1 = 5 then some (2 * a1 + 15)
  else eval (b1 - 6) (a1 + 4)
termination_by b
decreasing_by omega

def drain (r c : Nat) : Option Nat :=
  if r ≤ c then some (3*r+c+7)
  else if r=c+1 then none
  else if r=c+2 then some (2*c+8)
  else drain (r-c-3) (2*c+4)
termination_by r
decreasing_by omega

def f (x : Nat) : Option Nat :=
  if x=0 then none else if x=1 then some 5 else drain (x-2) 1

def oddCounter (x : Nat) : Nat := 2*x-1

theorem eval_odd (r c : Nat) : eval (2*r+1) c = (drain r c).map oddCounter := by
  induction r using Nat.strongRecOn generalizing c with
  | ind r ih =>
    rw [eval,drain]
    have hd : (2*r+1)/2=r := by omega
    rw [hd]
    by_cases h : r ≤ c
    · simp only [h,ite_true,Nat.min_eq_left h,Option.map_some,oddCounter]
      have hb : 2*r+1-2*r=1 := by omega
      rw [hb]
      by_cases he : r=c
      · subst c
        simp
        omega
      · have hc : 0<c-r := by omega
        simp only [hc,ite_true,show (1:Nat)≠0 by decide,ite_false]
        by_cases hz : c-r=1 <;> simp [hz] <;> omega
    · have h' : c≤r := by omega
      simp only [h,ite_false,Nat.min_eq_right h',Nat.sub_self,Nat.lt_irrefl,ite_false]
      have h0 : 2*r+1-2*c≠0 := by omega
      have h1 : 2*r+1-2*c≠1 := by omega
      have h2 : 2*r+1-2*c≠2 := by omega
      have h4 : 2*r+1-2*c≠4 := by omega
      simp only [h0,h1,h2,h4,or_false,ite_false]
      by_cases ha : r=c+1
      · have h3 : 2*r+1-2*c=3 := by omega
        rw [h3]
        simp [ha]
      · have h3 : 2*r+1-2*c≠3 := by omega
        simp only [ha,h3,ite_false]
        by_cases hb : r=c+2
        · have h5 : 2*r+1-2*c=5 := by omega
          rw [h5]
          simp [hb,oddCounter]
          omega
        · have h5 : 2*r+1-2*c≠5 := by omega
          simp only [hb,h5,ite_false]
          have heq : 2*r+1-2*c-6=2*(r-c-3)+1 := by omega
          rw [heq]
          exact ih _ (by omega) _

def c (i : Nat) : Nat := 5*2^i-4

def lo : Nat → Nat
  | 0 => 2
  | i+1 => lo i+c i+3

def halt (i : Nat) : Nat := lo i+c i+1

def special (i : Nat) : Nat := lo i+c i+2

theorem pow_lower (i : Nat) : i+1≤2^i := by
  induction i with
  | zero => decide
  | succ i ih => rw [Nat.pow_succ]; omega

theorem c_add (i : Nat) : c i+4=5*2^i := by
  unfold c
  have := pow_lower i
  omega

theorem c_succ (i : Nat) : c (i+1)=2*c i+4 := by
  have h := c_add i
  have hs := c_add (i+1)
  rw [Nat.pow_succ] at hs
  omega

theorem lo_add (i : Nat) : lo i+i+3=5*2^i := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [lo,Nat.pow_succ]
    have := c_add i
    omega

theorem lo_c (i : Nat) : lo i+i=c i+1 := by
  have := lo_add i
  have := c_add i
  omega

theorem lo_step (i : Nat) : lo (i+1)=lo i+c i+3 := rfl

theorem lo_ge (i : Nat) : i+2≤lo i := by
  induction i with
  | zero => decide
  | succ i ih => rw [lo]; omega

theorem lo_strict : ∀ {i j : Nat}, i<j → lo i<lo j := by
  intro i j h
  induction j with
  | zero => omega
  | succ j ih =>
    rw [lo]
    by_cases e : i=j
    · subst i; omega
    · have := ih (by omega)
      omega

theorem band_exists (x : Nat) (hx : 2≤x) : ∃ i, lo i≤x ∧ x<lo (i+1) := by
  have h : ∃ i, x<lo (i+1) := ⟨x,by have := lo_ge (x+1); omega⟩
  induction x using Nat.strongRecOn with
  | ind x ih =>
    -- use minimal index from a finite bounded search via induction on upper bound
    have aux : ∀ n, x<lo (n+1) → ∃ i, lo i≤x ∧ x<lo (i+1) := by
      intro n
      induction n with
      | zero => intro h; exact ⟨0,by simpa [lo] using hx,h⟩
      | succ n ih =>
        intro h
        by_cases hh : x<lo (n+1)
        · exact ih hh
        · exact ⟨n+1,by omega,h⟩
    obtain ⟨i,hi⟩ := h
    exact aux i hi

theorem band_unique {x i j : Nat} (hi : lo i≤x ∧ x<lo (i+1))
    (hj : lo j≤x ∧ x<lo (j+1)) : i=j := by
  by_cases h : i=j
  · exact h
  exfalso
  rcases Nat.lt_or_gt_of_ne h with hlt|hlt
  · by_cases he : i+1=j
    · rw [he] at hi; omega
    · have := lo_strict (show i+1<j by omega)
      omega
  · by_cases he : j+1=i
    · rw [he] at hj; omega
    · have := lo_strict (show j+1<i by omega)
      omega

theorem drain_shift (i r : Nat) :
    drain (lo i-2+r) 1 = drain r (c i) := by
  -- generalize the starting band to permit induction across one recursive step
  have aux : ∀ (k j r : Nat), drain (lo (k+j)-lo k+r) (c k) = drain r (c (k+j)) := by
    intro k j
    induction j generalizing k with
    | zero => simp
    | succ j ih =>
      intro r
      have hle : lo (k+1)≤lo (k+(j+1)) := by
        by_cases e : j=0
        · simp [e]
        · exact Nat.le_of_lt (lo_strict (by omega))
      have hs : lo (k+(j+1))-lo k+r≥c k+3 := by rw [lo_step] at hle; omega
      rw [drain]
      simp only [show ¬ lo (k+(j+1))-lo k+r≤c k by omega,ite_false,
        show lo (k+(j+1))-lo k+r≠c k+1 by omega,
        show lo (k+(j+1))-lo k+r≠c k+2 by omega]
      have he : lo (k+(j+1))-lo k+r-c k-3=lo ((k+1)+j)-lo (k+1)+r := by
        rw [show k+(j+1)=(k+1)+j by omega] at *
        rw [lo_step] at hle
        rw [lo_step]
        omega
      rw [he,←c_succ,ih]
      congr 2 <;> omega
  have h := aux 0 i r
  simpa [lo,c] using h

theorem f_band (i r : Nat) : f (lo i+r) =
    if r≤c i then some (3*r+c i+7)
    else if r=c i+1 then none
    else if r=c i+2 then some (2*c i+8)
    else drain (r-c i-3) (2*c i+4) := by
  have h := lo_ge i
  unfold f
  simp only [show lo i+r≠0 by omega,show lo i+r≠1 by omega,ite_false]
  rw [show lo i+r-2=lo i-2+r by omega,drain_shift,drain]

end Cap
