import Nov26SourceCore
import FirstHolePath
import BusyBeaver.BB6.NonHalt.M_1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RCHHH
import BusyBeaver.BB6.NonHalt.M_1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_HHH0LB

namespace BB6.Agent9Nov27
open BB6Coverage BB6.ConjectureBridge BB6.Agent10Nov26 BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Raw39; exact literal table, with halt row left unspecified in leaf. -/
def raw39_180 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,false,4⟩, some ⟨true,true,2⟩, some ⟨true,true,5⟩, some ⟨false,true,3⟩, some ⟨false,false,1⟩, some ⟨true,false,3⟩, some ⟨false,true,0⟩, some ⟨false,false,0⟩, some ⟨false,false,4⟩, some ⟨false,true,2⟩, none]
theorem raw39_180_eq : toAgent8 BusyBeaver.M_1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RCHHH.machine = raw39_180 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem raw39_180_never : NeverHalts raw39_180 := by
  rw [← raw39_180_eq]
  exact source_never BusyBeaver.M_1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RCHHH.machine BusyBeaver.M_1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RCHHH.is_not_halt
theorem raw39_180_cover : Cover NeverHalts (leaf raw39_180) :=
  Cover.leaf _ (all_completions_never _ raw39_180_never)
def raw39_180_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (3, (3, false)), (5, (3, true)), (6, (0, true)), (7, (4, false)), (12, (2, true)), (13, (1, true)), (14, (5, false)), (34, (4, true))]
theorem raw39_180_reachable : FirstHolePath (leaf raw39_180) 6 := by
  change FirstHolePath (forgetHaltRows raw39_180) 6
  exact checked_from_root raw39_180 raw39_180_path (by decide +kernel)
def raw39_180_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf raw39_180) 6 := by
  change WeightedTNFCertificate B (forgetHaltRows raw39_180) 6
  exact forgetHaltRows_nonhaltCertificate B raw39_180 (by rfl) raw39_180_never
theorem raw39_180_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf raw39_180) :=
  (raw39_180_weighted_cert B).toCover
#print axioms raw39_180_eq
#print axioms raw39_180_never
#print axioms raw39_180_cover
#print axioms raw39_180_reachable
#print axioms raw39_180_weighted_cover

/-- Raw13; exact literal table, with halt row left unspecified in leaf. -/
def raw13_new : Machine := literal [some ⟨true,true,1⟩, some ⟨true,false,3⟩, some ⟨true,true,2⟩, some ⟨false,false,0⟩, some ⟨true,false,0⟩, some ⟨false,true,4⟩, some ⟨true,false,1⟩, some ⟨true,false,0⟩, some ⟨true,true,5⟩, some ⟨false,true,1⟩, none, some ⟨false,false,1⟩]
theorem raw13_new_eq : toAgent8 BusyBeaver.M_1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_HHH0LB.machine = raw13_new := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem raw13_new_never : NeverHalts raw13_new := by
  rw [← raw13_new_eq]
  exact source_never BusyBeaver.M_1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_HHH0LB.machine BusyBeaver.M_1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_HHH0LB.is_not_halt
theorem raw13_new_cover : Cover NeverHalts (leaf raw13_new) :=
  Cover.leaf _ (all_completions_never _ raw13_new_never)
def raw13_new_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, false)), (3, (0, true)), (4, (3, true)), (6, (1, true)), (8, (3, false)), (10, (2, true)), (11, (4, true)), (41, (4, false)), (42, (5, true))]
theorem raw13_new_reachable : FirstHolePath (leaf raw13_new) 6 := by
  change FirstHolePath (forgetHaltRows raw13_new) 6
  exact checked_from_root raw13_new raw13_new_path (by decide +kernel)
def raw13_new_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf raw13_new) 6 := by
  change WeightedTNFCertificate B (forgetHaltRows raw13_new) 6
  exact forgetHaltRows_nonhaltCertificate B raw13_new (by rfl) raw13_new_never
theorem raw13_new_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf raw13_new) :=
  (raw13_new_weighted_cert B).toCover
#print axioms raw13_new_eq
#print axioms raw13_new_never
#print axioms raw13_new_cover
#print axioms raw13_new_reachable
#print axioms raw13_new_weighted_cover

end BB6.Agent9Nov27
