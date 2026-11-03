import Std

namespace CascadeSource

inductive S where
  | C (a b : Nat)
  | P (k n p : Nat)
  deriving Repr, DecidableEq

/-- Identical source clauses to cryptids #746 accelerated State.next. -/
def next : S → Option S
  | .C a 0 => some (.C 2 (2*a+1))
  | .C _ 1 => none
  | .C a (d+2) => some (.P a 0 (d+2))
  | .P 0 n 0 => some (.C (n+1) 2)
  | .P 0 n 1 => some (.C (n+1) 0)
  | .P 0 n (p+2) => some (.C (n+2) p)
  | .P (k+1) n 0 => some (.P k (n+1) 2)
  | .P (k+1) n 1 => some (.P k (n+1) 0)
  | .P (k+1) n (p+2) => some (.P k (n+2) p)

inductive Reach : S → S → Prop where
  | refl (s : S) : Reach s s
  | step {s t u : S} : next s = some t → Reach t u → Reach s u

protected theorem Reach.one {s t : S} (h : next s = some t) : Reach s t :=
  Reach.step h (Reach.refl t)

protected theorem Reach.trans {a b c : S} (h : Reach a b) (g : Reach b c) : Reach a c := by
  induction h with
  | refl => exact g
  | step hstep h ih => exact Reach.step hstep (ih g)

/-- Underflow sweep weight of a source P(k,n,p), valid when p<=2k+2. -/
def weight (k n p : Nat) : Nat :=
  6*k+4*n+p+(if p%2=0 then 6 else 3)

theorem w0 (k n : Nat) : weight (k+1) n 0 = weight k (n+1) 2 := by
  simp [weight]
  omega

theorem w1 (k n : Nat) : weight (k+1) n 1 = weight k (n+1) 0 := by
  simp [weight]
  omega

theorem w2 (k n p : Nat) : weight (k+1) n (p+2) = weight k (n+2) p := by
  have hp : (p+2)%2=p%2 := by omega
  simp only [weight, hp]
  omega

/-- Complete exact source-P sweep for all underflow inputs. -/
theorem P_sweep (k n p : Nat) (hp : p ≤ 2*k+2) :
    Reach (.P k n p) (.C (weight k n p / 4) (weight k n p % 4)) := by
  induction k generalizing n p with
  | zero =>
    have hp3 : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases hp3 with rfl | rfl | rfl
    · have h : weight 0 n 0 / 4 = n+1 ∧ weight 0 n 0 % 4 = 2 := by
        simp [weight]; omega
      rcases h with ⟨h1,h2⟩
      rw [h1,h2]
      exact Reach.one rfl
    · have h : weight 0 n 1 / 4 = n+1 ∧ weight 0 n 1 % 4 = 0 := by
        simp [weight]; omega
      rcases h with ⟨h1,h2⟩
      rw [h1,h2]
      exact Reach.one rfl
    · have h : weight 0 n 2 / 4 = n+2 ∧ weight 0 n 2 % 4 = 0 := by
        simp [weight]; omega
      rcases h with ⟨h1,h2⟩
      rw [h1,h2]
      exact Reach.one rfl
  | succ k ih =>
    rcases p with _ | _ | p
    · rw [w0 k n]
      exact Reach.step rfl (ih (n+1) 2 (by omega))
    · rw [w1 k n]
      exact Reach.step rfl (ih (n+1) 0 (by omega))
    · rw [w2 k n p]
      exact Reach.step rfl (ih (n+2) p (by omega))

/-- Source-P sweep while the right counter is large; after k branches the sweep closes. -/
theorem P_large (k n p : Nat) (hp : 2*k+2 ≤ p) :
    Reach (.P k n p) (.C (n+2*k+2) (p-2*k-2)) := by
  induction k generalizing n p with
  | zero =>
    obtain ⟨r, rfl⟩ : ∃ r, p=r+2 := ⟨p-2, by omega⟩
    have hh : n + 2*0+2=n+2 := by omega
    have hs : r+2-2*0-2=r := by omega
    rw [hh, hs]
    exact Reach.one rfl
  | succ k ih =>
    obtain ⟨r, rfl⟩ : ∃ r, p=r+2 := ⟨p-2, by omega⟩
    have hp' : 2*k+2 ≤ r := by omega
    have h := ih (n+2) r hp'
    have hh : n+2*(k+1)+2=(n+2)+2*k+2 := by omega
    have hs : r+2-2*(k+1)-2=r-2*k-2 := by omega
    rw [hh, hs]
    exact Reach.step rfl h

/-- This source-indexed C episode is either a direct new C or passes through P. -/
def Cstep (a b : Nat) : Option (Nat × Nat) :=
  if b=0 then some (2, 2*a+1)
  else if b=1 then none
  else
    let d := b-2
    if 2*a ≤ d then some (2*a+2, d-2*a)
    else
      let t := 6*a+d+(if d%2=0 then 8 else 5)
      some (t/4,t%4)

/-- Universal exact accelerated source C-to-C episode, for all configurations. -/
theorem C_step_sound (a b : Nat) (u v : Nat)
  (he : Cstep a b = some (u,v)) : Reach (.C a b) (.C u v) := by
  rcases b with _ | _ | d
  · simp only [Cstep, if_pos rfl, Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    exact Reach.one rfl
  · simp [Cstep] at he
  · have hzero : d+2 ≠ 0 := by omega
    have hone : d+2 ≠ 1 := by omega
    by_cases hd : 2*a ≤ d
    · have he' : some (2*a+2,d-2*a) = some (u,v) := by
        simpa [Cstep,hzero,hone,hd] using he
      have hu : u=2*a+2 ∧ v=d-2*a := by
        simpa using he'.symm
      rcases hu with ⟨rfl,rfl⟩
      have hp : 2*a+2 ≤ d+2 := by omega
      have h := P_large a 0 (d+2) hp
      have hs : 0+2*a+2=2*a+2 ∧ d+2-2*a-2=d-2*a := by omega
      rw [hs.1,hs.2] at h
      exact Reach.step rfl h
    · have hp : d+2 ≤ 2*a+2 := by omega
      have ht : (d+2)%2=d%2 := by omega
      have he' : some ((6*a+d+(if d%2=0 then 8 else 5))/4,
          (6*a+d+(if d%2=0 then 8 else 5))%4) = some (u,v) := by
        simpa [Cstep,hzero,hone,hd] using he
      have hw : weight a 0 (d+2) = 6*a+d+(if d%2=0 then 8 else 5) := by
        simp only [weight, ht]
        by_cases hpar : d % 2 = 0
        · simp only [if_pos hpar]; omega
        · simp only [if_neg hpar]; omega
      have hu : u=(6*a+d+(if d%2=0 then 8 else 5))/4 ∧
          v=(6*a+d+(if d%2=0 then 8 else 5))%4 := by
        simpa using he'.symm
      rcases hu with ⟨rfl,rfl⟩
      have h := P_sweep a 0 (d+2) hp
      rw [hw] at h
      exact Reach.step rfl h

#print axioms P_sweep
#print axioms P_large
#print axioms C_step_sound

end CascadeSource
