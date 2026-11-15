import BB429SourceBridge
import Lean.Elab.Tactic.Omega

/-!
# Exact last-reset equation for the authentic #429 root

This module keeps the state immediately before the final non-first transition,
the even seed produced by that transition, and the length of the final
first-branch burst.  It is a source-level reformulation of root halting, not a
claim that the required reset state or burst exists.
-/

namespace BB429LastResetEquation

open BB429SourceBridge
open BusyBeaver
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

def rootHalts : Prop :=
  ∃ n a b,
    sourceRun n (.J 0 0) = some (.J a b) ∧
    highLevelNext (.J a b) = none

theorem sourceRun_add (i k : Nat) (s : HighLevelState) :
    sourceRun (i+k) s = (sourceRun i s).bind (sourceRun k) := by
  induction k with
  | zero => simp [sourceRun]
  | succ k ih =>
    rw [Nat.add_succ]
    simp only [sourceRun, ih]
    cases h : sourceRun i s with
    | none => simp [h]
    | some t => simp [h, sourceRun]

/-- Every genuine source-root iterate is either the initial zero-length
    first burst, or a final non-first transition followed only by first steps.
    The predecessor and the exact even seed are retained. -/
theorem source_orbit_last_reset (n a b : Nat)
    (h : sourceRun n (.J 0 0) = some (.J a b)) :
    (∃ k, BB429Burst.firstRun k (0,0) = some (a,b)) ∨
    (∃ i x y u w k,
      i+1+k = n ∧
      sourceRun i (.J 0 0) = some (.J x y) ∧
      y < 2*x+3 ∧
      highLevelNext (.J x y) = some (.J u w) ∧
      w%2=0 ∧
      BB429Burst.firstRun k (u,w) = some (a,b)) := by
  induction n generalizing a b with
  | zero =>
    simp only [sourceRun, Option.some.injEq, HighLevelState.J.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    exact Or.inl ⟨0,rfl⟩
  | succ n ih =>
    change (sourceRun n (.J 0 0)).bind highLevelNext = some (.J a b) at h
    cases hp : sourceRun n (.J 0 0) with
    | none => simp [hp] at h
    | some p =>
      cases p with
      | J x y =>
        simp only [hp, Option.bind_some] at h
        by_cases hfirst : 2*x+3 ≤ y
        · have hs := source_first_step x y hfirst
          rw [hs] at h
          simp only [Option.some.injEq, HighLevelState.J.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          obtain hprev := ih x y hp
          rcases hprev with ⟨k,hk⟩ |
            ⟨i,x0,y0,u,w,k,hik,hr,hnot,hreset,heven,hprefix⟩
          · apply Or.inl
            refine ⟨k+1,?_⟩
            change (BB429Burst.firstRun k (0,0)).bind BB429Burst.firstStep =
              some (2*x+3,y-2*x-3)
            rw [hk]
            simp [BB429Burst.firstStep]
          · apply Or.inr
            refine ⟨i,x0,y0,u,w,k+1,?_ ,hr,hnot,hreset,heven,?_⟩
            · omega
            · change (BB429Burst.firstRun k (u,w)).bind BB429Burst.firstStep =
                some (2*x+3,y-2*x-3)
              rw [hprefix]
              simp [BB429Burst.firstStep]
        · have hnot : y < 2*x+3 := by omega
          have heven : b%2=0 := exit_even x y a b hnot h
          exact Or.inr ⟨n,x,y,a,b,0,by omega,hp,hnot,h,heven,rfl⟩

/-- The blank seed has no positive-length first-branch prefix. -/
private theorem blankFirstRun_pos_none (k : Nat) :
    BB429Burst.firstRun (k+1) (0,0) = none := by
  induction k with
  | zero => simp [BB429Burst.firstRun, BB429Burst.firstStep]
  | succ k ih =>
      change (BB429Burst.firstRun (k+1) (0,0)).bind BB429Burst.firstStep = none
      rw [ih]
      rfl

theorem initial_first_run_only_zero (k a b : Nat)
    (h : BB429Burst.firstRun k (0,0) = some (a,b)) :
    k=0 ∧ a=0 ∧ b=0 := by
  cases k with
  | zero =>
      simp only [BB429Burst.firstRun, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨rfl,rfl,rfl⟩
  | succ k =>
      have hnone := blankFirstRun_pos_none k
      simp [hnone] at h

/-- Exact root-level last-reset characterization.

A blank-root halt occurs iff some *genuinely root-reachable* state (x,y)
takes a non-first transition to an even seed (u,w), and the final first-branch
length k satisfies the exact exponential equation

    2*u + w + 3*k + 13 = 4*(u+3)*2^k.

Unlike a terminal-residue-only sieve, this equivalence retains the actual
pre-outer state, the post-reset seed, and the final outer-ladder length. -/
theorem root_halts_iff_last_reset_equation :
    rootHalts ↔
    ∃ i x y u w k,
      sourceRun i (.J 0 0) = some (.J x y) ∧
      y < 2*x+3 ∧
      highLevelNext (.J x y) = some (.J u w) ∧
      w%2=0 ∧
      2*u+w+3*k+13 = 4*((u+3)*2^k) := by
  constructor
  · rintro ⟨n,a,b,hr,hh⟩
    rcases source_orbit_last_reset n a b hr with
      ⟨k,hfirst⟩ |
      ⟨i,x,y,u,w,k,hik,hp,hnot,hreset,heven,hprefix⟩
    · obtain ⟨rfl,rfl,rfl⟩ := initial_first_run_only_zero k a b hfirst
      have hbad : 0+1=2*0 := (source_none_iff 0 0).mp hh
      omega
    · have hhalt : b+1=2*a := (source_none_iff a b).mp hh
      have heq :=
        (BB429Burst.gateway_iff_exponential u w k a b hprefix).mp hhalt
      exact ⟨i,x,y,u,w,k,hp,hnot,hreset,heven,heq⟩
  · rintro ⟨i,x,y,u,w,k,hp,hnot,hreset,heven,heq⟩
    obtain ⟨n,a,b,hprefix,hhalt⟩ :=
      (source_burst_gateway_iff u w).mpr ⟨k,heq⟩
    have hseed : sourceRun (i+1) (.J 0 0) = some (.J u w) := by
      change (sourceRun i (.J 0 0)).bind highLevelNext = some (.J u w)
      rw [hp]
      exact hreset
    have hroot : sourceRun ((i+1)+n) (.J 0 0) = some (.J a b) := by
      rw [sourceRun_add,hseed]
      exact firstRun_source u w n a b hprefix
    exact ⟨(i+1)+n,a,b,hroot,hhalt⟩

/-- A sourceRun path ending in a halting state is exactly a CollatzHalts
    witness for the upstream source accelerator. -/
theorem collatzHalts_of_sourceRun (n : Nat) (s t : HighLevelState)
    (h : sourceRun n s = some t)
    (ht : CollatzHalts highLevelNext t) :
    CollatzHalts highLevelNext s := by
  induction n generalizing s t with
  | zero =>
    simp only [sourceRun, Option.some.injEq] at h
    subst t
    exact ht
  | succ n ih =>
    change (sourceRun n s).bind highLevelNext = some t at h
    cases hp : sourceRun n s with
    | none => simp [hp] at h
    | some p =>
      simp only [hp, Option.bind_some] at h
      exact ih s p hp (CollatzHalts.of_next_eq_some h ht)

/-- Every CollatzHalts witness has a corresponding sourceRun endpoint whose
    next transition is none. -/
theorem sourceRun_of_collatzHalts (s : HighLevelState)
    (h : CollatzHalts highLevelNext s) :
    ∃ n t, sourceRun n s = some t ∧ highLevelNext t = none := by
  obtain ⟨N,hN⟩ := h
  induction N generalizing s with
  | zero => simp at hN
  | succ N ih =>
    rw [Function.iterate_succ_apply] at hN
    cases hs : highLevelNext s with
    | none => exact ⟨0,s,rfl,hs⟩
    | some s' =>
      have htailRaw :
          ((fun x => x.bind highLevelNext)^[N] (some s')).isNone = true := by
        simpa [hs] using hN
      obtain ⟨m,t,hr,ht⟩ := ih s' htailRaw
      refine ⟨m+1,t,?_ ,ht⟩
      have h1 : sourceRun 1 s = some s' := by simp [sourceRun,hs]
      calc
        sourceRun (m+1) s = sourceRun (1+m) s := by congr 1 <;> omega
        _ = (sourceRun 1 s).bind (sourceRun m) := sourceRun_add 1 m s
        _ = some t := by simp [h1,hr]

theorem rootHalts_iff_CollatzHalts :
    rootHalts ↔ CollatzHalts highLevelNext (.J 0 0) := by
  constructor
  · rintro ⟨n,a,b,hr,hh⟩
    exact collatzHalts_of_sourceRun n (.J 0 0) (.J a b) hr
      (CollatzHalts.of_next_eq_none hh)
  · intro h
    obtain ⟨n,t,hr,hh⟩ := sourceRun_of_collatzHalts (.J 0 0) h
    cases t with
    | J a b => exact ⟨n,a,b,hr,hh⟩

/-- The upstream, unchanged Cryptids acceleration therefore transports this
    last-reset criterion all the way to halting of the literal blank-root
    Turing machine. -/
theorem isHalt_iff_rootHalts :
    IsHalt target ↔ rootHalts :=
  isHalt_iff_highLevel_acceleration.trans rootHalts_iff_CollatzHalts.symm

/-- Exact raw-machine halting criterion with the authentic pre-reset state,
    even reset seed, and final outer-ladder length all retained. -/
theorem isHalt_iff_last_reset_equation :
    IsHalt target ↔
    ∃ i x y u w k,
      sourceRun i (.J 0 0) = some (.J x y) ∧
      y < 2*x+3 ∧
      highLevelNext (.J x y) = some (.J u w) ∧
      w%2=0 ∧
      2*u+w+3*k+13 = 4*((u+3)*2^k) := by
  exact isHalt_iff_rootHalts.trans root_halts_iff_last_reset_equation

/-- The exact root-level criterion also forces the known odd-burst and
    mod-six restrictions on the even reset seed. -/
theorem root_halt_has_odd_burst_and_mod6_seed (h : rootHalts) :
    ∃ i x y u w k,
      sourceRun i (.J 0 0) = some (.J x y) ∧
      y < 2*x+3 ∧
      highLevelNext (.J x y) = some (.J u w) ∧
      w%2=0 ∧ k%2=1 ∧ w%6=2 := by
  obtain ⟨i,x,y,u,w,k,hp,hnot,hreset,heven,heq⟩ :=
    root_halts_iff_last_reset_equation.mp h
  exact ⟨i,x,y,u,w,k,hp,hnot,hreset,heven,
    even_seed_odd_burst u w k heven heq,
    even_gateway_mod_six u w k heven heq⟩

#print axioms sourceRun_add
#print axioms source_orbit_last_reset
#print axioms initial_first_run_only_zero
#print axioms root_halts_iff_last_reset_equation
#print axioms collatzHalts_of_sourceRun
#print axioms sourceRun_of_collatzHalts
#print axioms rootHalts_iff_CollatzHalts
#print axioms isHalt_iff_rootHalts
#print axioms isHalt_iff_last_reset_equation
#print axioms root_halt_has_odd_burst_and_mod6_seed

end BB429LastResetEquation
