import Lean.Elab.Tactic.Omega
import FullFTapeConjugacy

namespace BB6.Agent2ESeamFRoot
open CryptidBoundary
open BB6.SourceSeamFrame
open BB6.SourceSeamComplete

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- Elementary well-ordering argument in core Lean, independent of
    mathlib or a bounded search. -/
private theorem least_witness (p : Nat → Prop) (hc : ∃ t, p t) :
    ∃ t, p t ∧ ∀ i, i < t → ¬p i := by
  obtain ⟨t,ht⟩ := hc
  suffices hmin : ∀ n : Nat,
      p n → ∃ u, p u ∧ ∀ i, i < u → ¬p i from hmin t ht
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hsmall : ∃ i, i < n ∧ p i
    · obtain ⟨i,hi,hp⟩ := hsmall
      exact ih i hi hp
    · refine ⟨n,hn,?_⟩
      intro i hi hp
      exact hsmall ⟨i,hi,hp⟩

/-- Any genuine positive return from one prepared F section forces its
    common E3 core to exhaust its protected left list at some raw time.
    This direction is exact for the original D source and requires no
    finite time search or assumption that k is small. -/
theorem core_contact_of_positive_F_return (k : Nat) (ys : List Bool)
    (hr : ∃ j : Nat, 0 < j ∧
      physicalReturn (run j (fStart k ys))) :
    ∃ t : Nat, (run t (eCore ys)).l = [] := by
  obtain ⟨j,hpos,hret⟩ := hr
  classical
  by_cases hcontact : ∃ t : Nat, (run t (eCore ys)).l = []
  · exact hcontact
  · exfalso
    have hnever (i : Nat) : (run i (eCore ys)).l ≠ [] := by
      intro hi
      exact hcontact ⟨i,hi⟩
    have hge : prefixTime k ≤ j := by
      by_cases hp : j < prefixTime k
      · exact False.elim ((prefix_strict_first k j ys hpos hp).1 hret)
      · omega
    have hsplit : j = prefixTime k + (j-prefixTime k) := by omega
    have hrun :
        run j (fStart k ys) =
          run (j-prefixTime k) (eSector (4*k) ys) := by
      calc
        run j (fStart k ys) =
            run (prefixTime k+(j-prefixTime k)) (fStart k ys) :=
              congrArg (fun n => run n (fStart k ys)) hsplit
        _ = run (j-prefixTime k) (eSector (4*k) ys) := by
              rw [run_add,prefix_is_certified_sector]
    rw [hrun] at hret
    exact (eSector_precontact_nonblank (4*k) (j-prefixTime k)
      ys (fun i _ => hnever i)) hret.2.2

/-- Exact converse: the first E3 marker contact, certified by the source
    invariant as C/1, sweeps back to a physically blank-left F/0 section
    for every unary parameter k. -/
theorem positive_F_return_of_core_contact (k : Nat) (ys : List Bool)
    (hc : ∃ t : Nat, (run t (eCore ys)).l = []) :
    ∃ j : Nat, 0 < j ∧
      physicalReturn (run j (fStart k ys)) := by
  obtain ⟨t,he,hb⟩ :=
    least_witness (fun i => (run i (eCore ys)).l = []) hc
  have hfull := (full_F_marker_sweep k t ys hb he).1
  refine ⟨prefixTime k+(t+8*k+2),by omega,?_⟩
  rw [hfull]
  simp [physicalReturn,blankLeft]

/-- Core marker contact is NECESSARY AND SUFFICIENT for positive-time
    physical F return, with arbitrary finite right tape and any E-index
    unary length. This reduces return classification of all k to one
    fixed E3 tape-orbit reachability predicate. -/
theorem core_contact_iff_positive_F_return (ys : List Bool) (k : Nat) :
    (∃ t : Nat, (run t (eCore ys)).l = []) ↔
    (∃ j : Nat, 0 < j ∧
      physicalReturn (run j (fStart k ys))) := by
  constructor
  · exact positive_F_return_of_core_contact k ys
  · exact core_contact_of_positive_F_return k ys

/-- A positive return witnessed at ANY parameter k0 forces a common
    strict first-return time and an exact full output tape for ALL k.
    This is a uniformly constructive mathematical consequence of
    source-level marker reachability; the witness need not be minimal. -/
theorem one_positive_return_certifies_all_outputs
    (ys : List Bool) (k0 : Nat)
    (h : ∃ j : Nat, 0 < j ∧
      physicalReturn (run j (fStart k0 ys))) :
    ∃ t : Nat, ∀ k : Nat,
      run (prefixTime k+(t+8*k+2)) (fStart k ys) =
        ⟨[],false,
          List.replicate (8*k+2) true ++ (run t (eCore ys)).r,5⟩ ∧
      (∀ j : Nat, 0 < j → j < prefixTime k+(t+8*k+2) →
        ¬ physicalReturn (run j (fStart k ys)) ∧
        ¬ haltGate (run j (fStart k ys))) := by
  have hc := core_contact_of_positive_F_return k0 ys h
  obtain ⟨t,he,hb⟩ :=
    least_witness (fun i => (run i (eCore ys)).l = []) hc
  exact ⟨t,fun k => full_F_marker_sweep k t ys hb he⟩

#print axioms core_contact_iff_positive_F_return
#print axioms one_positive_return_certifies_all_outputs
end BB6.Agent2ESeamFRoot
