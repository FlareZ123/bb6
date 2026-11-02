import Lean.Elab.Tactic.Omega

namespace BB6.BReduction

abbrev S := Nat × Nat × Nat

/-- Exact independently transcribed published acceleration for Machine B. -/
def nextB : S → Option S
  | (0, 0, _) => none
  | (a + 1, 0, c) => some (a, c, 2)
  | (0, 1, c) => some (2 * c + 9, 0, 0)
  | (a + 1, 1, c) => some (a, c, 6)
  | (a, b + 2, c) => some (a, b, c + 3)

/-- Exact finite positive transition closure (halting calls excluded). -/
inductive Star : S → S → Prop where
  | refl (s : S) : Star s s
  | step {s t u : S} (h : nextB s = some t) (ht : Star t u) : Star s u

theorem Star.trans {s t u : S} (h : Star s t) (g : Star t u) : Star s u := by
  induction h with
  | refl => exact g
  | step e _ ih => exact Star.step e (ih g)

theorem Star.single {s t : S} (h : nextB s = some t) : Star s t :=
  Star.step h (Star.refl _)

theorem drain_even (a q c : Nat) : Star (a,2*q,c) (a,0,c+3*q) := by
  induction q generalizing c with
  | zero => simp; exact Star.refl _
  | succ q ih =>
    have h0 : nextB (a, 2*(q+1), c) = some (a,2*q,c+3) := by
      simp [nextB, show 2*(q+1) = 2*q+2 by omega]
    have h1 := Star.step h0 (ih (c+3))
    have heq : c + 3 + 3*q = c + 3*(q+1) := by omega
    simpa only [heq] using h1

theorem drain_odd (a q c : Nat) : Star (a,2*q+1,c) (a,1,c+3*q) := by
  induction q generalizing c with
  | zero => simp; exact Star.refl _
  | succ q ih =>
    have h0 : nextB (a, 2*(q+1)+1, c) = some (a,2*q+1,c+3) := by
      simp [nextB, show 2*(q+1)+1 = (2*q+1)+2 by omega]
    have h1 := Star.step h0 (ih (c+3))
    have heq : c + 3 + 3*q = c + 3*(q+1) := by omega
    simpa only [heq] using h1

/-- Parity transducer for each positive-a decrement and full drain. -/
def F : Nat × Nat → Nat × Nat
  | (p,d) => (d % 2,3*(d/2)+2+4*p)

theorem decrement_even0 (a q : Nat) :
    Star (a+1,0,2*q) (a,0,3*q+2) := by
  have h : Star (a+1,0,2*q) (a,2*q,2) := Star.single (by rfl)
  have hd : Star (a,2*q,2) (a,0,2+3*q) := drain_even a q 2
  have ht := h.trans hd
  simpa only [show 2 + 3*q = 3*q + 2 by omega] using ht

theorem decrement_odd0 (a q : Nat) :
    Star (a+1,0,2*q+1) (a,1,3*q+2) := by
  have h : Star (a+1,0,2*q+1) (a,2*q+1,2) := Star.single (by rfl)
  have hd : Star (a,2*q+1,2) (a,1,2+3*q) := drain_odd a q 2
  have ht := h.trans hd
  simpa only [show 2 + 3*q = 3*q + 2 by omega] using ht

theorem decrement_even1 (a q : Nat) :
    Star (a+1,1,2*q) (a,0,3*q+6) := by
  have h : Star (a+1,1,2*q) (a,2*q,6) := Star.single (by rfl)
  have hd : Star (a,2*q,6) (a,0,6+3*q) := drain_even a q 6
  have ht := h.trans hd
  simpa only [show 6 + 3*q = 3*q + 6 by omega] using ht

theorem decrement_odd1 (a q : Nat) :
    Star (a+1,1,2*q+1) (a,1,3*q+6) := by
  have h : Star (a+1,1,2*q+1) (a,2*q+1,6) := Star.single (by rfl)
  have hd : Star (a,2*q+1,6) (a,1,6+3*q) := drain_odd a q 6
  have ht := h.trans hd
  simpa only [show 6 + 3*q = 3*q + 6 by omega] using ht

theorem decrement (a p d : Nat) (hp : p ≤ 1) :
    Star (a+1,p,d) (a,(F (p,d)).1,(F (p,d)).2) := by
  have hpar : p = 0 ∨ p = 1 := by omega
  have hrem : d % 2 = 0 ∨ d % 2 = 1 := by omega
  rcases hpar with hp0 | hp1
  · subst p
    rcases hrem with h0 | h1
    · have hd : d = 2*(d/2) := by omega
      have hh : Star (a+1,0,d) (a,0,3*(d/2)+2) := by
        simpa only [←hd] using decrement_even0 a (d/2)
      simpa [F, h0] using hh
    · have hd : d = 2*(d/2)+1 := by omega
      have hh : Star (a+1,0,d) (a,1,3*(d/2)+2) := by
        simpa only [←hd] using decrement_odd0 a (d/2)
      simpa [F, h1] using hh
  · subst p
    rcases hrem with h0 | h1
    · have hd : d = 2*(d/2) := by omega
      have hh : Star (a+1,1,d) (a,0,3*(d/2)+6) := by
        simpa only [←hd] using decrement_even1 a (d/2)
      simpa [F, h0] using hh
    · have hd : d = 2*(d/2)+1 := by omega
      have hh : Star (a+1,1,d) (a,1,3*(d/2)+6) := by
        simpa only [←hd] using decrement_odd1 a (d/2)
      simpa [F, h1] using hh

/-- Defined composition of the section transducer. -/
def iterF : Nat → Nat × Nat → Nat × Nat
  | 0, s => s
  | n+1, s => iterF n (F s)

theorem bit_F (s : Nat × Nat) : (F s).1 ≤ 1 := by
  rcases s with ⟨p,d⟩
  simp [F]
  omega

theorem bit_iterF (n : Nat) (s : Nat × Nat) (hs : s.1 ≤ 1) :
    (iterF n s).1 ≤ 1 := by
  induction n generalizing s with
  | zero => simpa [iterF] using hs
  | succ n ih => exact ih (F s) (bit_F s)

theorem cycle (a p d : Nat) (hp : p ≤ 1) :
    Star (a,p,d) (0,(iterF a (p,d)).1,(iterF a (p,d)).2) := by
  induction a generalizing p d with
  | zero => simp [iterF]; exact Star.refl _
  | succ a ih =>
    rw [iterF]
    exact (decrement a p d hp).trans (ih _ _ (bit_F _))

/-- Finite halting in the published partial three-counter map. -/
inductive Halts : S → Prop where
  | stop {s : S} (h : nextB s = none) : Halts s
  | next {s t : S} (h : nextB s = some t) (ht : Halts t) : Halts s

theorem halts_step_iff {s t : S} (h : nextB s = some t) :
    Halts s ↔ Halts t := by
  constructor
  · intro hs
    cases hs with
    | stop hh => simp [hh] at h
    | next hh ht =>
      have heq : _ := congrArg id (hh.symm.trans h)
      cases Option.some.inj heq
      exact ht
  · exact Halts.next h

theorem halts_iff_star {s t : S} (h : Star s t) : Halts s ↔ Halts t := by
  induction h with
  | refl => exact Iff.rfl
  | step h _ ih => exact (halts_step_iff h).trans ih

theorem halt_zero (d : Nat) : Halts (0,0,d) := Halts.stop rfl

theorem halt_one_iff (d : Nat) :
    Halts (0,1,d) ↔ Halts (2*d+9,0,0) := halts_step_iff rfl

/-- Exact iff for a complete countdown cycle, including both terminal branches. -/
theorem cycle_halts_iff (a : Nat) :
    Halts (a,0,0) ↔
      (iterF a (0,0)).1 = 0 ∨
      ((iterF a (0,0)).1 = 1 ∧ Halts (2*(iterF a (0,0)).2+9,0,0)) := by
  have hc := halts_iff_star (cycle a 0 0 (by omega))
  rcases hpair : iterF a (0,0) with ⟨p,d⟩
  have hp : p ≤ 1 := by
    have hb := bit_iterF a (0,0) (by omega)
    rw [hpair] at hb
    exact hb
  have hor : p=0 ∨ p=1 := by omega
  rcases hor with rfl | rfl
  · simp only [hpair, Prod.fst] at *
    simp [halt_zero] at hc ⊢
    exact hc
  · simp only [hpair, Prod.fst, Prod.snd] at *
    simp [halt_one_iff] at hc ⊢
    exact hc

#print axioms cycle
#print axioms cycle_halts_iff
end BB6.BReduction
