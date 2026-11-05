import S4TripleSharp
import Lean.Elab.Tactic.Omega

namespace S4TripleRoot
open S4Power S4Octet S4Toggle S4TripleHead S4TripleSharp
set_option maxHeartbeats 0

def root : List Nat := [301,650,645,322,163,160]

private theorem prun_none_after (T : List Nat) (k j : Nat)
    (hn : prun k T=none) : prun (k+j) T=none := by
  induction j with
  | zero => simpa using hn
  | succ j ih =>
      change (prun (k+j) T).bind P=none
      rw [ih]
      rfl

private theorem first_failure (k : Nat) (h : prun k root=none) :
    ∃ j U, prun j root=some U ∧ P U=none := by
  induction k with
  | zero => simp [prun] at h
  | succ k ih =>
      cases hk : prun k root with
      | none => exact ih hk
      | some U =>
          refine ⟨k,U,hk,?_⟩
          simpa [prun,hk] using h

private theorem failure_not_before_twentythree (j : Nat) (U : List Nat)
    (hprun : prun j root=some U) (hP : P U=none) : 23≤j := by
  by_cases hge : 23≤j
  · exact hge
  · exfalso
    have hsucc : prun (j+1) root=none := by
      change (prun j root).bind P=none
      simp [hprun,hP]
    have heq : j+1+(23-(j+1))=23 := by omega
    have h23none : prun 23 root=none := by
      rw [←heq]
      exact prun_none_after root (j+1) (23-(j+1)) hsucc
    have h23 := S4TripleHead.seed23
    simp [root,h23] at h23none

theorem halt_iff_reached_failure :
    (∃ k, prun k root=none) ↔
    ∃ n U, prun (23+n) root=some U ∧ P U=none := by
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨j,U,hj,hP⟩ := first_failure k hk
    have hjge := failure_not_before_twentythree j U hj hP
    refine ⟨j-23,U,?_,hP⟩
    simpa [show 23+(j-23)=j by omega] using hj
  · rintro ⟨n,U,hU,hP⟩
    refine ⟨23+n+1,?_⟩
    change (prun (23+n) root).bind P=none
    simp [hU,hP]

def DangerPhase (i : Nat) : Prop :=
    i=3 ∨ i=6 ∨ i=7 ∨ i=10 ∨ i=11 ∨ i=12 ∨
    i=15 ∨ i=23 ∨ i=25 ∨ i=26 ∨ i=28 ∨ i=31

private theorem danger_iff_not_safe (n : Nat) :
    DangerPhase (n%32) ↔ ¬S4TripleSharp.SafePhase (n%32) := by
  unfold DangerPhase S4TripleSharp.SafePhase
  have hlt : n%32<32 := Nat.mod_lt n (by omega)
  omega

theorem rooted_halt_iff_twelve_phases :
    (∃ k, prun k root=none) ↔
    ∃ n T,
       prun (23+n) root = some ((tripleRun n).1::(tripleRun n).2.1::(tripleRun n).2.2::T) ∧
       DangerPhase (n%32) ∧
       P ((tripleRun n).1::(tripleRun n).2.1::(tripleRun n).2.2::T)=none := by
  constructor
  · intro hh
    obtain ⟨n,U,hU,hP⟩ := halt_iff_reached_failure.mp hh
    obtain ⟨T,hPair⟩ := prun_triple_cycle n U hU
    subst U
    refine ⟨n,T,hU,?_,hP⟩
    apply (danger_iff_not_safe n).mpr
    intro hs
    have hall := (exact_triple_safety n).mpr hs
    exact (hall T) hP
  · rintro ⟨n,T,hU,_,hP⟩
    exact halt_iff_reached_failure.mpr ⟨n,_,hU,hP⟩

#print axioms halt_iff_reached_failure
#print axioms rooted_halt_iff_twelve_phases
end S4TripleRoot
