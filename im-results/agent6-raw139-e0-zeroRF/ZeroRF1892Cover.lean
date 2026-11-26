import ZeroRF1892Kernel
import Hybrid
set_option maxHeartbeats 0
namespace BB6.Agent6E0ZeroRF1892
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent6Hybrid

theorem nonhalt_cover (B : Nat) (p : PartialMachine)
    (hn : ∀ m, compatible p m → NeverHalts m) : Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm k d hh hd
  have h := hn m hm (k+1)
  rw [hh.2] at h
  contradiction

theorem weighted : Cover (WeightedBound 2043) p := nonhalt_cover 2043 p never
theorem tableCover : Cover (WeightedBound 2043)
    (BB6Coverage.FAR.fromCodes [7,24,11,17,14,8,3,16,21,11,12,13]) := by
  apply sound 2043 _ (.covered p weighted)
  · decide +kernel
  · exact fromCodes_nohalt _
  · decide +kernel
#print axioms weighted
#print axioms tableCover
end BB6.Agent6E0ZeroRF1892
