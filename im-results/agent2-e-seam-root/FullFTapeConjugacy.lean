import Lean.Elab.Tactic.Omega
import FullFFirstEvent

namespace BB6.Agent2ESeamFRoot
open CryptidBoundary
open BB6.SourceSeamFrame
open BB6.SourceSeamComplete

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- Original-source full physical output, starting from the actual F
    delimiter prefix, whenever the shared three-pair E core first reaches
    its protected left marker. Both the exact endpoint and strictness
    hold for every unary parameter k and every finite right suffix. -/
theorem full_F_marker_sweep (k t : Nat) (ys : List Bool)
    (hb : ∀ i : Nat, i < t → (run i (eCore ys)).l ≠ [])
    (he : (run t (eCore ys)).l = []) :
    run (prefixTime k+(t+8*k+2)) (fStart k ys) =
      ⟨[],false,
        List.replicate (8*k+2) true ++ (run t (eCore ys)).r,5⟩ ∧
    (∀ j : Nat, 0 < j → j < prefixTime k+(t+8*k+2) →
      ¬ physicalReturn (run j (fStart k ys)) ∧
      ¬ haltGate (run j (fStart k ys))) := by
  obtain ⟨hs,hh⟩ := source_marker_safe ys t hb he
  have hprefix := prefix_is_certified_sector k ys
  have hE := eSector_marker_sweep (4*k) t ys hb he hs hh
  have hfirst := eSector_first_event_return (4*k) t ys hb he hs hh
  have htime : t+8*k+2 = t+2*(4*k)+2 := by omega
  constructor
  · rw [htime,run_add,hprefix]
    exact hE
  · intro j hjpos hjlt
    by_cases hpre : j < prefixTime k
    · exact prefix_strict_first k j ys hjpos hpre
    · have hsplit : j = prefixTime k+(j-prefixTime k) := by omega
      have hinside : j-prefixTime k < t+2*(4*k)+2 := by omega
      have hrun :
          run j (fStart k ys) =
            run (j-prefixTime k) (eSector (4*k) ys) := by
        calc
          run j (fStart k ys) =
              run (prefixTime k+(j-prefixTime k)) (fStart k ys) :=
                congrArg (fun n => run n (fStart k ys)) hsplit
          _ = run (j-prefixTime k) (eSector (4*k) ys) := by
              rw [run_add,hprefix]
      rw [hrun]
      exact hfirst.2 (j-prefixTime k) hinside

/-- Complete physical right-tape conjugacy: increasing the original F
    unary parameter by k adds exactly 8k consecutive ones to the output
    of the shared k=0 first marker return, preserving the entire suffix
    of the physical tape. No bounded sampling and no truncation. -/
theorem full_F_output_shift (k t : Nat) (ys : List Bool)
    (hb : ∀ i : Nat, i < t → (run i (eCore ys)).l ≠ [])
    (he : (run t (eCore ys)).l = []) :
    (run (prefixTime k+(t+8*k+2)) (fStart k ys)).r =
      List.replicate (8*k) true ++
        (run (prefixTime 0+(t+2)) (fStart 0 ys)).r := by
  have hk := (full_F_marker_sweep k t ys hb he).1
  have hbase :
      run (prefixTime 0+(t+2)) (fStart 0 ys) =
        (⟨[],false,List.replicate 2 true ++ (run t (eCore ys)).r,5⟩ : Cfg) := by
    simpa using (full_F_marker_sweep 0 t ys hb he).1
  rw [hk,hbase]
  change List.replicate (8*k+2) true ++ (run t (eCore ys)).r =
    List.replicate (8*k) true ++
      (List.replicate 2 true ++ (run t (eCore ys)).r)
  rw [← List.append_assoc,List.replicate_append_replicate]

#print axioms full_F_marker_sweep
#print axioms full_F_output_shift
end BB6.Agent2ESeamFRoot
