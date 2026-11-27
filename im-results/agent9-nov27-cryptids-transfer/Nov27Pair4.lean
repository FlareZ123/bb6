import Nov26SourceCore
import FirstHolePath
import BusyBeaver.BB6.NonHalt.M_1RB0RC_1LC0RB_1LD0LD_1RA1LE_HHH0LF_1LB1LF
import BusyBeaver.BB6.NonHalt.M_1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RCHHH

namespace BB6.Agent9Nov27
open BB6Coverage BB6.ConjectureBridge BB6.Agent10Nov26 BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Raw10; exact literal table, with halt row left unspecified in leaf. -/
def raw10_5 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,true,2⟩, some ⟨true,false,2⟩, some ⟨false,true,1⟩, some ⟨true,false,3⟩, some ⟨false,false,3⟩, some ⟨true,true,0⟩, some ⟨true,false,4⟩, none, some ⟨false,false,5⟩, some ⟨true,false,1⟩, some ⟨true,false,5⟩]
theorem raw10_5_eq : toAgent8 BusyBeaver.M_1RB0RC_1LC0RB_1LD0LD_1RA1LE_HHH0LF_1LB1LF.machine = raw10_5 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem raw10_5_never : NeverHalts raw10_5 := by
  rw [← raw10_5_eq]
  exact source_never BusyBeaver.M_1RB0RC_1LC0RB_1LD0LD_1RA1LE_HHH0LF_1LB1LF.machine BusyBeaver.M_1RB0RC_1LC0RB_1LD0LD_1RA1LE_HHH0LF_1LB1LF.is_not_halt
theorem raw10_5_cover : Cover NeverHalts (leaf raw10_5) :=
  Cover.leaf _ (all_completions_never _ raw10_5_never)
def raw10_5_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (3, false)), (5, (1, true)), (7, (2, false)), (8, (3, true)), (9, (4, true)), (10, (5, false)), (14, (0, true)), (23, (5, true))]
theorem raw10_5_reachable : FirstHolePath (leaf raw10_5) 6 := by
  change FirstHolePath (forgetHaltRows raw10_5) 6
  exact checked_from_root raw10_5 raw10_5_path (by decide +kernel)
def raw10_5_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf raw10_5) 6 := by
  change WeightedTNFCertificate B (forgetHaltRows raw10_5) 6
  exact forgetHaltRows_nonhaltCertificate B raw10_5 (by rfl) raw10_5_never
theorem raw10_5_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf raw10_5) :=
  (raw10_5_weighted_cert B).toCover
#print axioms raw10_5_eq
#print axioms raw10_5_never
#print axioms raw10_5_cover
#print axioms raw10_5_reachable
#print axioms raw10_5_weighted_cover

/-- Raw10; exact literal table, with halt row left unspecified in leaf. -/
def raw10_6 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,true,3⟩, some ⟨true,false,2⟩, some ⟨false,false,4⟩, some ⟨false,true,0⟩, some ⟨false,false,1⟩, some ⟨true,true,2⟩, some ⟨true,true,5⟩, some ⟨true,false,1⟩, some ⟨true,true,3⟩, some ⟨false,true,2⟩, none]
theorem raw10_6_eq : toAgent8 BusyBeaver.M_1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RCHHH.machine = raw10_6 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem raw10_6_never : NeverHalts raw10_6 := by
  rw [← raw10_6_eq]
  exact source_never BusyBeaver.M_1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RCHHH.machine BusyBeaver.M_1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RCHHH.is_not_halt
theorem raw10_6_cover : Cover NeverHalts (leaf raw10_6) :=
  Cover.leaf _ (all_completions_never _ raw10_6_never)
def raw10_6_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (4, (2, false)), (5, (0, true)), (6, (3, false)), (8, (1, true)), (9, (4, false)), (13, (3, true)), (14, (5, false)), (64, (4, true))]
theorem raw10_6_reachable : FirstHolePath (leaf raw10_6) 6 := by
  change FirstHolePath (forgetHaltRows raw10_6) 6
  exact checked_from_root raw10_6 raw10_6_path (by decide +kernel)
def raw10_6_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf raw10_6) 6 := by
  change WeightedTNFCertificate B (forgetHaltRows raw10_6) 6
  exact forgetHaltRows_nonhaltCertificate B raw10_6 (by rfl) raw10_6_never
theorem raw10_6_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf raw10_6) :=
  (raw10_6_weighted_cert B).toCover
#print axioms raw10_6_eq
#print axioms raw10_6_never
#print axioms raw10_6_cover
#print axioms raw10_6_reachable
#print axioms raw10_6_weighted_cover

end BB6.Agent9Nov27
