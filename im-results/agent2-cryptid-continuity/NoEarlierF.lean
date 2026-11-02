import Lean.Elab.Tactic.Omega
import CryptidSix

namespace BB6.CryptidFirstReturn
open CryptidBoundary

set_option maxHeartbeats 1000000

/-!
All statements below concern the original six-state D-start transition table
through the unmodified CryptidSix / Boundary source. In particular, this file
establishes a *strict* first-F bound for its B sweep, not just an endpoint.
-/

def dMid (m : Nat) (ys : List Bool) : Cfg :=
  ⟨pairs m ++ [true,true],false,ys,3⟩

private theorem dMid_two (m : Nat) (ys : List Bool) :
    run 2 (dMid (m+1) ys) = dMid m (true::true::ys) := by
  simp [dMid, pairs,run,step,goL]

private theorem dMid_noF (m : Nat) (ys : List Bool) (t : Nat)
    (ht : t < 2*m+3) : (run t (dMid m ys)).st ≠ 5 := by
  induction m generalizing ys t with
  | zero =>
    have hx : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hx with rfl | rfl | rfl
    all_goals simp [dMid,pairs,run,step,goL]
  | succ m ih =>
    by_cases hsmall : t<2
    · have hx : t=0 ∨ t=1 := by omega
      rcases hx with rfl | rfl
      all_goals simp [dMid,pairs,run,step,goL]
    · have ht' : 2 ≤ t := by omega
      obtain ⟨k, rfl⟩ : ∃ k, t=2+k := ⟨t-2,by omega⟩
      rw [run_add,dMid_two]
      exact ih (true::true::ys) k (by omega)

private theorem sweepB_two (m : Nat) (ys : List Bool) :
    run 2 (sweepB (m+1) ys) = dMid m (true::true::ys) := by
  simp [sweepB,dMid,pairs,run,step,goL]

/-- The exact first encounter with state F during a source B sweep occurs
    at time 2*m+3, independently of the arbitrary right suffix. -/
theorem sweepB_firstF (m : Nat) (ys : List Bool) (t : Nat)
    (ht : t < 2*m+3) : (run t (sweepB m ys)).st ≠ 5 := by
  cases m with
  | zero =>
    have hx : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hx with rfl | rfl | rfl
    all_goals simp [sweepB,pairs,run,step,goL]
  | succ m =>
    by_cases hsmall : t<2
    · have hx : t=0 ∨ t=1 := by omega
      rcases hx with rfl | rfl
      all_goals simp [sweepB,pairs,run,step,goL]
    · have ht' : 2 ≤ t := by omega
      obtain ⟨k, rfl⟩ : ∃ k, t=2+k := ⟨t-2,by omega⟩
      rw [run_add,sweepB_two]
      exact dMid_noF m (true::true::ys) k (by omega)

#print axioms sweepB_firstF
end BB6.CryptidFirstReturn
