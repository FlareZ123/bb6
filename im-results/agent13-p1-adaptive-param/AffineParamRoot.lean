import AdaptiveParam
import GenericCriticalReachParamK
set_option maxHeartbeats 10000000

namespace BB6.Agent13AdaptiveParam
open BB6.Agent9Adaptive (decode)
open BB6.Precision (ShadowReach)

/-- Check-accepted finite affine graph controls every genuine inverse path
    from the original two-feeder root, without a time or depth cutoff. -/
theorem check_all_reach (K B qbase side c P : Nat)
    (nodes : List (Nat×Nat×Nat×Nat))
    (hc : check K B (16*qbase+side) P nodes = true)
    (hroot : ∀ r, (0,c*(qbase+P*r)+4)∈decode r nodes)
    (r m z : Nat)
    (hp : ShadowReach (16*(qbase+P*r)+side)
        (c*(qbase+P*r)+4) m z) :
    m≤B ∧ ¬2^K∣z := by
  have hmem : (m,z)∈decode r nodes := by
    induction hp with
    | root => exact hroot r
    | @step m z hprev t v zp hd hn ih =>
        apply check_sound K B (16*qbase+side) P nodes hc r m z t v zp ih hd
        have he : 2*zp+1=16*P*r+(16*qbase+side)+m+t+v := by
          simpa [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hn
        exact he
  exact check_bounds K B (16*qbase+side) P nodes hc r m z hmem

/-- General original P1 blank-root exclusion from two finite, executable,
    exact affine inverse graphs, for ANY independently checked parameter
    period P and all precision K / inverse cost B. -/
theorem critical_unreachable_of_affine_check
    (K B qbase P : Nat)
    (hq : 29≤qbase) (hB : B+K+3≤15*qbase)
    (nodes0 nodes1 : List (Nat×Nat×Nat×Nat))
    (hc0 : check K B (16*qbase+8) P nodes0 = true)
    (hc1 : check K B (16*qbase+9) P nodes1 = true)
    (hroot0 : ∀ r, (0,12*(qbase+P*r)+4)∈decode r nodes0)
    (hroot1 : ∀ r, (0,10*(qbase+P*r)+4)∈decode r nodes1)
    (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(qbase+P*r)+2)-2*(16*(qbase+P*r)+2)-10) := by
  let q := qbase+P*r
  have hq' : 29≤q := by dsimp [q]; omega
  have hB' : B+K+3≤15*q := by dsimp [q]; omega
  have hs0 : ∀ m z, ShadowReach (16*q+8) (12*q+4) m z → m≤B := by
    intro m z hp
    exact (check_all_reach K B qbase 8 12 P nodes0 hc0 hroot0 r m z hp).1
  have hs1 : ∀ m z, ShadowReach (16*q+9) (10*q+4) m z → m≤B := by
    intro m z hp
    exact (check_all_reach K B qbase 9 10 P nodes1 hc1 hroot1 r m z hp).1
  have hn0 : ∀ m z, ShadowReach (16*q+8) (12*q+4) m z → ¬2^K∣z := by
    intro m z hp
    exact (check_all_reach K B qbase 8 12 P nodes0 hc0 hroot0 r m z hp).2
  have hn1 : ∀ m z, ShadowReach (16*q+9) (10*q+4) m z → ¬2^K∣z := by
    intro m z hp
    exact (check_all_reach K B qbase 9 10 P nodes1 hc1 hroot1 r m z hp).2
  exact BB6.Agent9GenericReachParamK.critical_unreachable_of_reach_param_K
    K B q hq' hB' hs0 hs1 hn0 hn1

#print axioms check_all_reach
#print axioms critical_unreachable_of_affine_check
end BB6.Agent13AdaptiveParam
