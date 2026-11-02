module

public import Lean.Elab.Tactic.Omega

@[expose] public section

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

/-- The transducer's payload grows on every countdown substep. -/
theorem F_grows (p d : Nat) : d < (F (p,d)).2 := by
  simp only [F]
  omega

theorem iterF_growth (n p d : Nat) : d+n ≤ (iterF n (p,d)).2 := by
  induction n generalizing p d with
  | zero => simp [iterF]
  | succ n ih =>
    have h := ih (F (p,d)).1 (F (p,d)).2
    have hstep := F_grows p d
    have hpair : ((F (p,d)).1,(F (p,d)).2) = F (p,d) := by
      cases F (p,d) <;> rfl
    rw [hpair] at h
    change d+(n+1) ≤ (iterF n (F (p,d))).2
    omega

/-- Symbolic reset indices, even when a hypothetical earlier cycle would halt. -/
def resetA : Nat → Nat
  | 0 => 3
  | n+1 => 2 * (iterF (resetA n) (0,0)).2 + 9

theorem reset_growth (n : Nat) : 2*resetA n+9 ≤ resetA (n+1) := by
  simp only [resetA]
  have h := iterF_growth (resetA n) 0 0
  omega

theorem reset_exp_lower (n : Nat) : 12*2^n ≤ resetA n + 9 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := reset_growth n
    have hpow : 12*2^(n+1) = 2*(12*2^n) := by
      simp [Nat.pow_succ]
      omega
    omega

/-- Exact parity sampled at the recursively generated reset index. -/
def sample (n : Nat) : Nat × Nat := iterF (resetA n) (0,0)

theorem sample_bit (n : Nat) : (sample n).1 ≤ 1 :=
  bit_iterF (resetA n) (0,0) (by omega)

theorem reset_index_ge (n : Nat) : n ≤ resetA n := by
  induction n with
  | zero => simp [resetA]
  | succ n ih =>
    have h := reset_growth n
    omega

/-- If every sampled bit is one, all generated reset states are genuinely reachable. -/
theorem all_one_reaches (h : ∀ n, (sample n).1 = 1) (n : Nat) :
    Star (3,0,0) (resetA n,0,0) := by
  induction n with
  | zero => simpa only [resetA] using Star.refl (3,0,0)
  | succ n ih =>
    have hc := cycle (resetA n) 0 0 (by omega)
    have hstep : Star (resetA n,0,0) (0,1,(sample n).2) := by
      have heq : (iterF (resetA n) (0,0)).1 = 1 := h n
      rw [heq] at hc
      exact hc
    have hreset : Star (0,1,(sample n).2) (resetA (n+1),0,0) := by
      apply Star.single
      simp [nextB, resetA, sample]
    exact ih.trans (hstep.trans hreset)

/-- Finite halting proofs bound the first counter of all reachable states. -/
theorem halt_bounded {s : S} (h : Halts s) :
    ∃ B : Nat, ∀ t : S, Star s t → t.1 ≤ B := by
  induction h with
  | @stop s hs =>
    refine ⟨s.1, ?_⟩
    intro t ht
    cases ht with
    | refl => exact Nat.le_refl _
    | step hx _ => simp [hs] at hx
  | @next s t ht hh ih =>
    obtain ⟨B,hB⟩ := ih
    refine ⟨max s.1 B, ?_⟩
    intro u hu
    cases hu with
    | refl => exact Nat.le_max_left _ _
    | @step _ v _ hv htail =>
      have heq : v=t := Option.some.inj (hv.symm.trans ht)
      subst v
      have hBound := hB _ htail
      omega

/-- Any finite sampling horizon already has a halt or has reached the next reset. -/
theorem halt_or_reset (n : Nat) :
    Halts (3,0,0) ∨ Star (3,0,0) (resetA n,0,0) := by
  induction n with
  | zero => exact Or.inr (by simpa [resetA] using Star.refl (3,0,0))
  | succ n ih =>
    rcases ih with hhalt | hreach
    · exact Or.inl hhalt
    · have hc := cycle (resetA n) 0 0 (by omega)
      have hb := sample_bit n
      have hor : (sample n).1 = 0 ∨ (sample n).1 = 1 := by omega
      rcases hor with hz | ho
      · have hlast : Halts (resetA n,0,0) := by
          have heq : (iterF (resetA n) (0,0)).1 = 0 := hz
          rw [heq] at hc
          apply (halts_iff_star hc).2
          exact halt_zero (sample n).2
        exact Or.inl ((halts_iff_star hreach).2 hlast)
      · have hstep : Star (resetA n,0,0) (0,1,(sample n).2) := by
          have heq : (iterF (resetA n) (0,0)).1 = 1 := ho
          rw [heq] at hc
          exact hc
        have hreset : Star (0,1,(sample n).2) (resetA (n+1),0,0) := by
          apply Star.single
          simp [nextB,resetA,sample]
        exact Or.inr (hreach.trans (hstep.trans hreset))

/-- Complete, infinite-horizon reduction for the certified blank-entry triple (3,0,0).
    Machine B halts exactly if one of its recursively sampled parity bits is zero. -/
theorem blank_halts_iff_sample_zero :
    Halts (3,0,0) ↔ ∃ n : Nat, (sample n).1 = 0 := by
  constructor
  · intro hh
    by_cases hzero : ∃ n : Nat, (sample n).1 = 0
    · exact hzero
    · exfalso
      have hall : ∀ n, (sample n).1 = 1 := by
        intro n
        have hb := sample_bit n
        have hneq : (sample n).1 ≠ 0 := by
          intro hz
          exact hzero ⟨n,hz⟩
        omega
      obtain ⟨B,hB⟩ := halt_bounded hh
      have hr := all_one_reaches hall (B+1)
      have hbound := hB _ hr
      have hlarge := reset_index_ge (B+1)
      omega
  · rintro ⟨n,hzero⟩
    rcases halt_or_reset n with hh | hr
    · exact hh
    · have hc := cycle (resetA n) 0 0 (by omega)
      have hlast : Halts (resetA n,0,0) := by
        have heq : (iterF (resetA n) (0,0)).1 = 0 := hzero
        rw [heq] at hc
        apply (halts_iff_star hc).2
        exact halt_zero (sample n).2
      exact (halts_iff_star hr).2 hlast

#print axioms blank_halts_iff_sample_zero
#print axioms reset_exp_lower

#print axioms cycle
#print axioms cycle_halts_iff
end BB6.BReduction
