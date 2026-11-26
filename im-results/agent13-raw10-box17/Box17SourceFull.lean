import Box17SourceCore
import CryptidsTapeAdapter
import BusyBeaver.Bridge
import BusyBeaver.BB6.NonHalt.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13.Box17
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent49BoxBridge BB6.ConjectureBridge BB6.Agent50RootFrontier

def upstreamR1 : ConjectureMachines.Machine 6 2 :=
  BusyBeaver.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.machine

theorem r1_source_eq : toAgent8 upstreamR1 = r1Machine := by
  funext s
  rcases s with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem r1_source_never : NeverHalts r1Machine := by
  rw [←r1_source_eq]
  apply not_halts_to_agent8 upstreamR1
  apply (ConjectureMachines.isNotHalt_toBB_iff_not_halts upstreamR1).mp
  simpa [upstreamR1] using BusyBeaver.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.is_not_halt

theorem sourceBound (m : Machine) (hm : Fits raw10Remainder[17]! m) :
    WeightedBound 7014 m := sourceBound_of_r1 r1_source_never m hm

theorem sourceExact (B : Nat) :
    (∀ m, Fits raw10Remainder[17]! m → WeightedBound B m) ↔ 7014 ≤ B :=
  sourceExact_of_r1 r1_source_never B

def raw10_cover_except17 (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOther : ∀ r ∈ raw10Remainder, r ≠ raw10Remainder[17]! →
      ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  raw10_cover B hB hHeld (fun r hr m hm => by
    by_cases he : r = raw10Remainder[17]!
    · subst r
      intro k d hk hd
      exact Nat.le_trans (sourceBound m hm k d hk hd) hB
    · exact hOther r hr he m hm)

#print axioms r1_source_eq
#print axioms r1_source_never
#print axioms sourceBound
#print axioms sourceExact
#print axioms raw10_cover_except17
end BB6.Agent13.Box17
