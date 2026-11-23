import Lean.Elab.Tactic.Omega
import UnaryFirstReturnComplete
import BFirstReturn
import BRegularSource

/-!
# All original-source canonical B sections: prescribed first F return

The existing B endpoint contract is strengthened to exclude EVERY earlier
control-state F for all canonical a ≡ 2 mod 3 rows, regardless of the
arbitrary right (01)^q 1^b suffix. This proof handles physical right
blank when q=0 by observational tape padding.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent4BCanonicalAllFirst

open CryptidBoundary
open BB6.BoundaryPadding
open BB6.CryptidBFirstReturn
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidFirstReturn
open BB6.Agent4UnaryFirstReturnComplete

/-- Stronger version of BFirstReturn: this phase contains no state F
at all, until its exact positive-time endpoint, for EVERY right suffix. -/
theorem b_raw_noF (k : Nat) (ys : List Bool) (t : Nat)
    (hpos : 0<t) (ht : t<12*k*k+49*k+40) :
    (run t (bStart k ys)).st ≠ 5 := by
  by_cases hp : t<12*k*k+41*k+31
  · exact prefixB_positive_noF k ys t hpos hp
  · have hend : run (12*k*k+41*k+31) (bStart k ys) =
      sweepB (4*k+3) ys := by
      change run (12*k*k+41*k+31)
        (init (List.replicate (3*k) true ++ false::ys)) = _
      rw [prefix_B]
      rfl
    have htstep : t=(12*k*k+41*k+31)+(t-(12*k*k+41*k+31)) := by omega
    rw [htstep,run_add,hend]
    exact sweepB_firstF (4*k+3) ys
      (t-(12*k*k+41*k+31)) (by omega)

private theorem durationB (k q b : Nat) :
    DRegular.duration ⟨3*k+2,q,b⟩ = 12*k*k+49*k+40 := by
  have hm : (3*k+2)%3=2 := by omega
  have hd : (3*k+2)/3=k := by omega
  simp [DRegular.duration,hm,hd]

/-- Source first-F visit for every canonical B input. The b=0
constraint when q=0 follows from DRegular.Canon and is essential:
other redundant zero-pair encodings are not canonical. -/
theorem all_B_no_earlier_F (k q b : Nat)
    (hc : DRegular.Canon ⟨3*k+2,q,b⟩) :
    ∀ t, 0<t → t<DRegular.duration ⟨3*k+2,q,b⟩ →
      (run t (DRegularSource.sourceSection ⟨3*k+2,q,b⟩)).st ≠5 := by
  intro t hpos ht
  rw [durationB] at ht
  cases q with
  | zero =>
      rcases hc with ⟨ha, hcanon⟩
      have hb : b=0 := by
        rcases hcanon with hbad | hzero
        · exact False.elim (hbad rfl)
        · exact hzero
      subst b
      have hn : (3*k+2)-2=3*k := by omega
      have hstart : DRegularSource.sourceSection ⟨3*k+2,0,0⟩ =
          init (List.replicate (3*k) true) := by
        simp [DRegularSource.sourceSection, hn, oppairs]
      rw [hstart]
      exact b_unary_noF k t hpos ht
  | succ q =>
      have hn : (3*k+2)-2=3*k := by omega
      have heq :
          DRegularSource.sourceSection ⟨3*k+2,q+1,b⟩ =
            bStart k (true :: (oppairs q ++ List.replicate b true)) := by
        simp [DRegularSource.sourceSection,bStart,hn,oppairs,
          List.append_assoc]
      rw [heq]
      exact b_raw_noF k _ t hpos ht

/-- Combined B source endpoint and strict no-intermediate-control-F
for every B residue of the regular source grammar, with arbitrary
canonical (01)^q 1^b suffix. -/
theorem all_B_first (k q b : Nat)
    (hc : DRegular.Canon ⟨3*k+2,q,b⟩)
    (out : DRegular.L)
    (hn : DRegular.next ⟨3*k+2,q,b⟩ = some out) :
    ObsEq
      (run (DRegular.duration ⟨3*k+2,q,b⟩)
        (DRegularSource.sourceSection ⟨3*k+2,q,b⟩))
      (DRegularSource.sourceSection out) ∧
    ∀ t, 0<t → t<DRegular.duration ⟨3*k+2,q,b⟩ →
      (run t (DRegularSource.sourceSection ⟨3*k+2,q,b⟩)).st ≠ 5 := by
  constructor
  · have hmod : (DRegular.L.mk (3*k+2) q b).a % 3 = 2 := by
      change (3*k+2)%3=2
      omega
    exact BB6.BRegularSource.original_B_row
      (DRegular.L.mk (3*k+2) q b) out hc hmod hn
  · exact all_B_no_earlier_F k q b hc

#print axioms b_raw_noF
#print axioms all_B_no_earlier_F
#print axioms all_B_first

end BB6.Agent4BCanonicalAllFirst
