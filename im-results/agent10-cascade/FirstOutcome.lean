import FullReturn

namespace CascadeResetInverse
open CascadeSource

/-- A deterministic source-C episode computation stopped at its *first*
    reset or its first undefined halting transition. -/
inductive Outcome : (Nat × Nat) → Option Nat → Prop where
  | halt {x : Nat × Nat} (hx : Cstep x.1 x.2=none) : Outcome x none
  | reset {x : Nat × Nat} {u : Nat}
      (hx : Cstep x.1 x.2=some (u,0)) : Outcome x (some u)
  | follow {x y : Nat × Nat} {out : Option Nat}
      (hx : Cstep x.1 x.2=some y) (hy : y.2≠0)
      (hr : Outcome y out) : Outcome x out

private def A (k : Nat) : Nat := 4*2^k-2
private def B (h k : Nat) : Nat := 2*h+2*k+9-8*2^k

private theorem sweep_lift (h k : Nat)
  (hg : ∀ j, j<k → 8*2^j≤h+j+5)
  {out : Option Nat} (hout : Outcome (A k,B h k) out) :
  Outcome (h,0) out := by
  induction k with
  | zero =>
    have he : Cstep h 0 = some (A 0,B h 0) := by simp [Cstep,A,B]
    have hpos : B h 0≠0 := by simp [B]
    exact Outcome.follow he hpos hout
  | succ k ih =>
    have hg' : ∀j, j<k → 8*2^j≤h+j+5 := by
      intro j hj; exact hg j (by omega)
    have hk : 8*2^k≤h+k+5 := hg k (by omega)
    have he : Cstep (A k) (B h k)=some (A (k+1),B h (k+1)) := by
      have he0:= CascadeExactGate.cascade_one h k hk
      change Cstep (4*2^k-2) (2*h+2*k+9-8*2^k) =
        some (4*2^(k+1)-2,2*h+2*(k+1)+9-8*2^(k+1)) at he0
      exact he0
    have hpos : B h (k+1)≠0 := by
      have hh : 2^(k+1)=2*2^k := by rw [Nat.pow_succ];omega
      dsimp [B]
      rw [hh]
      omega
    exact ih hg' (Outcome.follow he hpos hout)

/-- Every successful dyadic B=2 drain has a certified *first-reset* outcome. -/
theorem drain_first (t d : Nat) (hd : d%2=1) (hq : 4≤2^t*d) :
    Outcome (2^t*d-3,2) (some ((3^(t+1)*d-5)/2)) := by
  induction t generalizing d with
  | zero =>
    have hd4 : 4≤d := by simpa using hq
    have hd5 : 5≤d := by omega
    simpa using (Outcome.reset (drain_odd d hd5 hd))
  | succ t ih =>
    have heven : (2^(t+1)*d)%2=0 := by
      have hp : 2^(t+1)*d=2*(2^t*d) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
      rw [hp]
      omega
    have hnext := drain_even (2^(t+1)*d) hq heven
    have hstep : Cstep (2^(t+1)*d-3) 2 = some (2^t*(3*d)-3,2) := by
      have hpow : 2^(t+1)*d=2*(2^t*d) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
      have hx : 2^t*(3*d)=3*(2^t*d) := by
        simp only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
      have hdiv : 3*(2^(t+1)*d)/2 = 2^t*(3*d) := by
        rw [hpow, hx]
        omega
      simpa only [hdiv] using hnext
    have hd3 : (3*d)%2=1 := by omega
    have hq3 : 4≤2^t*(3*d) := by
      have hpow : 2^(t+1)*d=2*(2^t*d) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
      have hx : 2^t*(3*d)=3*(2^t*d) := by
        simp only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
      rw [hpow] at hq
      rw [hx]
      omega
    have hrec := ih (3*d) hd3 hq3
    have hprod : 3^(t+1)*(3*d)=3^((t+1)+1)*d := by
      simp only [Nat.pow_succ,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]
    rw [hprod] at hrec
    exact Outcome.follow hstep (by simp) hrec

/-- A deterministic source-C computation has at most one first reset/halt
    outcome; every apparent alternative shares exactly the same first edge. -/
theorem outcome_unique {x : Nat × Nat} {a b : Option Nat}
    (ha : Outcome x a) (hb : Outcome x b) : a=b := by
  induction ha generalizing b with
  | halt he =>
    cases hb with
    | halt he2 => rfl
    | reset he2 => simp [he] at he2
    | follow he2 hy hr => simp [he] at he2
  | @reset x u he =>
    cases hb with
    | halt he2 => simp [he2] at he
    | @reset _ v he2 =>
      have hh : (u,0)=(v,0) := Option.some.inj (he.symm.trans he2)
      have hu : u=v := congrArg Prod.fst hh
      simp [hu]
    | @follow _ y _ he2 hy hr =>
      have hh : (u,0)=y := Option.some.inj (he.symm.trans he2)
      have hz : y.2=0 := by rw [←hh]
      exact False.elim (hy hz)
  | @follow x y out he hy hr ih =>
    cases hb with
    | halt he2 => simp [he2] at he
    | @reset _ v he2 =>
      have hh : y=(v,0) := Option.some.inj (he.symm.trans he2)
      have hz : y.2=0 := by rw [hh]
      exact False.elim (hy hz)
    | @follow _ y' _ he2 hy2 hr2 =>
      have hh : y=y' := Option.some.inj (he.symm.trans he2)
      subst y'
      exact ih hr2

/-- For every reset input, a deterministic first reset or halt exists. -/
theorem first_outcome_exists (h : Nat) :
    ∃ out, Outcome (h,0) out := by
  obtain ⟨k,hg,hhigh⟩ := first_fail h
  have hlow := first_low h k hg
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
  by_cases hfat : h+k+4=4*2^k
  · have hbk : B h k=1 := by dsimp [B]; omega
    have hx : Cstep (A k) (B h k)=none := by
      rw [hbk]
      simp [Cstep]
    exact ⟨none,sweep_lift h k hg (Outcome.halt hx)⟩
  · have he := exit (2^k) h k hp hlow hhigh hfat
    by_cases hpar : (h+k)%2=0
    · have he' : Cstep (A k) (B h k)=some (4*2^k+(h+k)/2,0) := by
        simpa [A,B,hpar] using he
      exact ⟨some (4*2^k+(h+k)/2),
        sweep_lift h k hg (Outcome.reset he')⟩
    · have hodd : (h+k)%2=1 := by omega
      have hqpos : 0<4*2^k+(h+k)/2+3 := by omega
      obtain ⟨t,d,hfac,hd⟩ := factor_twos _ hqpos
      have hq : 4≤2^t*d := by omega
      have he' : Cstep (A k) (B h k)=some (2^t*d-3,2) := by
        have hs : 2^t*d-3=4*2^k+(h+k)/2 := by omega
        simpa [A,B,hodd,hs] using he
      exact ⟨some ((3^(t+1)*d-5)/2),
        sweep_lift h k hg (Outcome.follow he' (by simp) (drain_first t d hd hq))⟩

/-- Exact first successful reset in the even underflow case. -/
theorem even_outcome (h k : Nat)
  (hg : ∀ j, j<k → 8*2^j≤h+j+5)
  (hlow : 4*2^k≤h+k+4)
  (hhigh : h+k+5<8*2^k)
  (hnot : h+k+4≠4*2^k)
  (hpar : (h+k)%2=0) :
  Outcome (h,0) (some (4*2^k+(h+k)/2)) := by
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
  have he := exit (2^k) h k hp hlow hhigh hnot
  have he' : Cstep (A k) (B h k)=some (4*2^k+(h+k)/2,0) := by
    simpa [A,B,hpar] using he
  exact sweep_lift h k hg (Outcome.reset he')

/-- Exact first successful reset in the odd underflow case, for any
    valuation exponent. -/
theorem odd_outcome (h k t d : Nat)
  (hg : ∀ j, j<k → 8*2^j≤h+j+5)
  (hlow : 4*2^k≤h+k+4)
  (hhigh : h+k+5<8*2^k)
  (hnot : h+k+4≠4*2^k)
  (hpar : (h+k)%2=1)
  (hfactor : 4*2^k+(h+k)/2+3=2^t*d)
  (hd : d%2=1) :
  Outcome (h,0) (some ((3^(t+1)*d-5)/2)) := by
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
  have he := exit (2^k) h k hp hlow hhigh hnot
  have he' : Cstep (A k) (B h k)=some (2^t*d-3,2) := by
    have hs : 2^t*d-3=4*2^k+(h+k)/2 := by omega
    simpa [A,B,hpar,hs] using he
  have hq : 4≤2^t*d := by omega
  exact sweep_lift h k hg (Outcome.follow he' (by simp) (drain_first t d hd hq))

/-- The canonical halting or first-reset outcome determined by the finite
    first failed sweep guard and exact valuation drain. -/
theorem closed_outcome (h k : Nat)
  (hg : ∀ j, j<k → 8*2^j≤h+j+5)
  (hhigh : h+k+5<8*2^k) :
  (h+k+4=4*2^k ∧ Outcome (h,0) none) ∨
  (h+k+4≠4*2^k ∧ (h+k)%2=0 ∧
    Outcome (h,0) (some (4*2^k+(h+k)/2))) ∨
  ∃t d, h+k+4≠4*2^k ∧ (h+k)%2=1 ∧ d%2=1 ∧
    4*2^k+(h+k)/2+3=2^t*d ∧
    Outcome (h,0) (some ((3^(t+1)*d-5)/2)) := by
  have hlow := first_low h k hg
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
  by_cases hfat : h+k+4=4*2^k
  · have hbk : B h k=1 := by dsimp [B]; omega
    have hx : Cstep (A k) (B h k)=none := by
      rw [hbk]
      simp [Cstep]
    exact Or.inl ⟨hfat,sweep_lift h k hg (Outcome.halt hx)⟩
  · have he := exit (2^k) h k hp hlow hhigh hfat
    by_cases hpar : (h+k)%2=0
    · have he' : Cstep (A k) (B h k)=some (4*2^k+(h+k)/2,0) := by
        simpa [A,B,hpar] using he
      exact Or.inr (Or.inl ⟨hfat,hpar,
        sweep_lift h k hg (Outcome.reset he')⟩)
    · have hodd : (h+k)%2=1 := by omega
      have hqpos : 0<4*2^k+(h+k)/2+3 := by omega
      obtain ⟨t,d,hfac,hd⟩ := factor_twos _ hqpos
      have hq : 4≤2^t*d := by omega
      have he' : Cstep (A k) (B h k)=some (2^t*d-3,2) := by
        have hs : 2^t*d-3=4*2^k+(h+k)/2 := by omega
        simpa [A,B,hodd,hs] using he
      exact Or.inr (Or.inr ⟨t,d,hfat,hodd,hd,hfac,
        sweep_lift h k hg (Outcome.follow he' (by simp) (drain_first t d hd hq))⟩)

/-- Necessity: an actual first reset has exactly one of the two closed
    dyadic image forms; all intermediate sweep and drain states have been
    explicitly excluded by the FirstOutcome semantics. -/
theorem first_reset_classification (h u : Nat)
    (hr : Outcome (h,0) (some u)) :
  ∃ k, 4*2^k≤h+k+4 ∧ h+k+5<8*2^k ∧
    h+k+4≠4*2^k ∧ (((h+k)%2=0 ∧ u=4*2^k+(h+k)/2) ∨
     ∃t d, (h+k)%2=1 ∧ d%2=1 ∧
       4*2^k+(h+k)/2+3=2^t*d ∧
       u=(3^(t+1)*d-5)/2) := by
  obtain ⟨k,hg,hhigh⟩ := first_fail h
  have hlow := first_low h k hg
  obtain hcases := closed_outcome h k hg hhigh
  rcases hcases with ⟨hfat,hhalt⟩ | ⟨hnot,hpar,heven⟩ |
    ⟨t,d,hnot,hpar,hd,hfac,hodd⟩
  · have hh := outcome_unique hr hhalt
    contradiction
  · have hu : u=4*2^k+(h+k)/2 := Option.some.inj (outcome_unique hr heven)
    exact ⟨k,hlow,hhigh,hnot,Or.inl ⟨hpar,hu⟩⟩
  · have hu : u=(3^(t+1)*d-5)/2 := Option.some.inj (outcome_unique hr hodd)
    exact ⟨k,hlow,hhigh,hnot,Or.inr ⟨t,d,hpar,hd,hfac,hu⟩⟩

#print axioms even_outcome
#print axioms odd_outcome
#print axioms closed_outcome
#print axioms first_reset_classification
#print axioms outcome_unique
#print axioms drain_first
#print axioms first_outcome_exists
end CascadeResetInverse
