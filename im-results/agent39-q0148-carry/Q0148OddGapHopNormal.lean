import Q0148EvenCarryOutput
import Lean.Elab.Tactic.Omega

/-!
# Exact U-carry recurrence through an arbitrary positive even A gap

In the Raw11 q0-148 marked E1 traversal, the left tape after one hop
contains a marker followed by an even alternating block. The following
unbounded source word identities give the exact next-hop carry and
marker displacement, including the zero-gap boundary case.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0

theorem aRun_add (m n : Nat) :
    aRun (m+n) = aRun m ++ aRun n := by
  induction m with
  | zero => simp [aRun]
  | succ m ih =>
      simpa [aRun, ih, Nat.succ_add]

/-- Carry U copies an arbitrary number of A tokens unchanged. -/
theorem u_run_copy (n : Nat) :
    carryFold .one (aRun n) = (aRun n, .one) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h := congrArg
        (fun z : List LeftChunk × Carry => (.alternating :: z.1, z.2)) ih
      simpa only [aRun,carryFold,carryStep,
        List.cons_append,List.nil_append] using h

/-- For any positive even A run, carry S emits exactly one M,
    copies all but the first two A tokens and leaves carry U. -/
theorem s_positive_even (n : Nat) :
    carryFold .eleven (aRun (2*n+2)) =
      (.separatedMarker :: aRun (2*n), .one) := by
  have hpow : 2*n+2 = 2+2*n := by omega
  rw [hpow,aRun_add,fold_append]
  simpa [aRun,carryFold,carryStep,u_run_copy]

/-- After seeing M and a positive even A run, the U carry emits
    exactly A A M A^(2n), and remains U. -/
theorem u_marker_even_open (n : Nat) :
    carryFold .one (.separatedMarker :: aRun (2*n+2)) =
      ([.alternating,.alternating,.separatedMarker] ++ aRun (2*n),
        .one) := by
  have h := fold_append .one [.separatedMarker] (aRun (2*n+2))
  simpa [carryFold,carryStep,s_positive_even,List.append_assoc] using h

/-- Completing the even gap with one more marker emits A A M
    A^(2n+2) and restores carry S. The same formula is independent of
    the size of the gap and is safe for all n>=0. -/
theorem u_marker_even_closed (n : Nat) :
    carryFold .one
      (.separatedMarker :: aRun (2*n+2) ++ [.separatedMarker]) =
      ([.alternating,.alternating,.separatedMarker] ++
         aRun (2*n+2), .eleven) := by
  have h := fold_append .one
      (.separatedMarker :: aRun (2*n+2)) [.separatedMarker]
  rw [u_marker_even_open] at h
  dsimp only at h
  have hlast : aRun (2*n) ++ [.alternating,.alternating] =
      aRun (2*n+2) := by
    simpa [aRun] using (aRun_add (2*n) 2).symm
  rw [hlast] at h
  simpa [carryFold,carryStep,List.append_assoc] using h

/-- The zero-length even gap is different: U M emits two A tokens
    and resets carry immediately, with no intermediate marker. -/
theorem u_marker_empty :
    carryFold .one [.separatedMarker] =
      ([.alternating,.alternating], .eleven) := by rfl

#print axioms aRun_add
#print axioms u_run_copy
#print axioms s_positive_even
#print axioms u_marker_even_open
#print axioms u_marker_even_closed
#print axioms u_marker_empty

end BB6.Agent39Q0148Carry
