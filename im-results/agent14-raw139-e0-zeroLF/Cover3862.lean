import E0LFResidual3862
import ConditionalHybrid
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit BB6.Agent14ConditionalHybrid
namespace BB6.Agent14ZeroLF3862

def ctr : PartialMachine := fromCodes [7,10,11,19,14,17,24,16,20,11,3,0]
theorem exactTable : ctr = BB6Coverage.Agent3E0LFSweep.table false := tableOK_sound _ _ (by decide +kernel)
theorem never_exact (m : Machine) (hm : compatible ctr m) : NeverHalts m := by
  rw [exactTable] at hm
  exact never m hm

theorem weighted (B : Nat) : Cover (WeightedBound B) ctr := by
  apply Cover.leaf
  intro m hm k d hk hd
  have hn := never_exact m hm (k+1)
  unfold HaltsAfter at hk
  simp_all

#print axioms weighted
end BB6.Agent14ZeroLF3862
