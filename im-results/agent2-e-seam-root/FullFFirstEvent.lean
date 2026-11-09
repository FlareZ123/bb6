import Lean.Elab.Tactic.Omega
import SourceSeamComplete
import PrefixENoFSource

namespace BB6.Agent2ESeamFRoot
open CryptidBoundary
open BB6.SourceSeamFrame
open BB6.SourceSeamComplete

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- Physical F/0 section with unary length 3k+4 and an arbitrary
    right suffix beyond its first zero delimiter. -/
def fStart (k : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+2) true ++ false :: ys)

def prefixTime (k : Nat) : Nat := 12*k*k+41*k+33

/-- The original source's exact F-to-E delimiter prefix enters precisely
    the E-sector already covered by the unconditional seam certificate. -/
theorem prefix_is_certified_sector (k : Nat) (ys : List Bool) :
    run (prefixTime k) (fStart k ys) = eSector (4*k) ys := by
  simpa [prefixTime,fStart,eSector,Nat.add_comm,Nat.add_left_comm,
    Nat.add_assoc] using (prefix_E k ys)

/-- Neither physical F/0 return nor F/1 gate is possible while the
    original-source delimiter prefix is still being executed. -/
theorem no_gate_of_not_F (c : Cfg) (h : c.st ≠ 5) :
    ¬ physicalReturn c ∧ ¬ haltGate c := by
  simp [physicalReturn,haltGate,h]

theorem prefix_strict_first (k j : Nat) (ys : List Bool)
    (hj : 0 < j) (hbefore : j < prefixTime k) :
    ¬ physicalReturn (run j (fStart k ys)) ∧
    ¬ haltGate (run j (fStart k ys)) := by
  apply no_gate_of_not_F
  exact BB6.CryptidPrefixFirstReturn.prefixE_positive_noF
    k ys j hj hbefore

/-- Source-original unbounded first-event law from arbitrary prepared
    F/0 sections. The first alternative has one common core event time,
    strict first physical return for EVERY unary parameter k, and an
    exact primitive-step time quadratic in k. The second alternative
    excludes all further returns and identifies every halt gate with
    the same unbounded E3 core history after its exact source prefix.

    This is an all-prepared-section statement, not a blank-root theorem. -/
theorem all_prepared_F_first_events (ys : List Bool) :
    (∃ t : Nat,
      ∀ k : Nat,
        physicalReturn
          (run (prefixTime k+(t+8*k+2)) (fStart k ys)) ∧
        ∀ j : Nat, 0 < j → j < prefixTime k+(t+8*k+2) →
          ¬ physicalReturn (run j (fStart k ys)) ∧
          ¬ haltGate (run j (fStart k ys))) ∨
    (∀ k j : Nat, 0 < j →
      ¬ physicalReturn (run j (fStart k ys)) ∧
      (prefixTime k ≤ j →
        (haltGate (run j (fStart k ys)) ↔
          haltGate (run (j-prefixTime k) (eCore ys))))) := by
  rcases source_e_all_m_first_event ys with ⟨t, ht⟩ | hn
  · left
    refine ⟨t,?_⟩
    intro k
    have hprefix := prefix_is_certified_sector k ys
    have heq : t+8*k+2 = t+2*(4*k)+2 := by omega
    constructor
    · rw [heq,run_add,hprefix]
      exact (ht (4*k)).1
    · intro j hjpos hjlt
      by_cases hp : j < prefixTime k
      · exact prefix_strict_first k j ys hjpos hp
      · have hsplit : j = prefixTime k+(j-prefixTime k) := by omega
        have hinside : j-prefixTime k < t+2*(4*k)+2 := by omega
        rw [hsplit,run_add,hprefix]
        exact (ht (4*k)).2 (j-prefixTime k) hinside
  · right
    intro k j hjpos
    have hprefix := prefix_is_certified_sector k ys
    by_cases hp : j < prefixTime k
    · have hnone := prefix_strict_first k j ys hjpos hp
      refine ⟨hnone.1,?_⟩
      intro hge
      omega
    · have hsplit : j = prefixTime k+(j-prefixTime k) := by omega
      have hrun :
          run j (fStart k ys) =
            run (j-prefixTime k) (eSector (4*k) ys) := by
        calc
          run j (fStart k ys) =
              run (prefixTime k+(j-prefixTime k)) (fStart k ys) :=
                congrArg (fun n => run n (fStart k ys)) hsplit
          _ = run (j-prefixTime k) (eSector (4*k) ys) := by
              rw [run_add,hprefix]
      have hnone := hn (4*k) (j-prefixTime k)
      constructor
      · rw [hrun]
        exact hnone.1
      · intro _
        rw [hrun]
        exact hnone.2

#print axioms prefix_is_certified_sector
#print axioms prefix_strict_first
#print axioms all_prepared_F_first_events
end BB6.Agent2ESeamFRoot
