import Nov26SourceCore
import FirstHolePath
import BusyBeaver.BB6.NonHalt.M_1RB1RF_1LC0RF_1LE0LD_1RC0LB_HHH1RA_1LB1RA
import BusyBeaver.BB6.NonHalt.M_1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LFHHH_1LB1RF

namespace BB6.Agent9Nov27
open BB6Coverage BB6.ConjectureBridge BB6.Agent10Nov26 BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Raw10; exact literal table, with halt row left unspecified in leaf. -/
def raw10_7 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,true,5⟩, some ⟨true,false,2⟩, some ⟨false,true,5⟩, some ⟨true,false,4⟩, some ⟨false,false,3⟩, some ⟨true,true,2⟩, some ⟨false,false,1⟩, none, some ⟨true,true,0⟩, some ⟨true,false,1⟩, some ⟨true,true,0⟩]
theorem raw10_7_eq : toAgent8 BusyBeaver.M_1RB1RF_1LC0RF_1LE0LD_1RC0LB_HHH1RA_1LB1RA.machine = raw10_7 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem raw10_7_never : NeverHalts raw10_7 := by
  rw [← raw10_7_eq]
  exact source_never BusyBeaver.M_1RB1RF_1LC0RF_1LE0LD_1RC0LB_HHH1RA_1LB1RA.machine BusyBeaver.M_1RB1RF_1LC0RF_1LE0LD_1RC0LB_HHH1RA_1LB1RA.is_not_halt
theorem raw10_7_cover : Cover NeverHalts (leaf raw10_7) :=
  Cover.leaf _ (all_completions_never _ raw10_7_never)
def raw10_7_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (3, false)), (4, (2, false)), (5, (4, true)), (6, (0, true)), (7, (5, true)), (11, (3, true)), (12, (1, true)), (13, (5, false))]
theorem raw10_7_reachable : FirstHolePath (leaf raw10_7) 6 := by
  change FirstHolePath (forgetHaltRows raw10_7) 6
  exact checked_from_root raw10_7 raw10_7_path (by decide +kernel)
def raw10_7_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf raw10_7) 6 := by
  change WeightedTNFCertificate B (forgetHaltRows raw10_7) 6
  exact forgetHaltRows_nonhaltCertificate B raw10_7 (by rfl) raw10_7_never
theorem raw10_7_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf raw10_7) :=
  (raw10_7_weighted_cert B).toCover
#print axioms raw10_7_eq
#print axioms raw10_7_never
#print axioms raw10_7_cover
#print axioms raw10_7_reachable
#print axioms raw10_7_weighted_cover

/-- Raw0; exact literal table, with halt row left unspecified in leaf. -/
def raw0_new : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,2⟩, some ⟨false,false,0⟩, some ⟨true,true,3⟩, some ⟨true,false,0⟩, some ⟨false,true,4⟩, some ⟨true,true,4⟩, some ⟨false,true,5⟩, some ⟨true,false,5⟩, none, some ⟨true,false,1⟩, some ⟨true,true,5⟩]
theorem raw0_new_eq : toAgent8 BusyBeaver.M_1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LFHHH_1LB1RF.machine = raw0_new := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem raw0_new_never : NeverHalts raw0_new := by
  rw [← raw0_new_eq]
  exact source_never BusyBeaver.M_1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LFHHH_1LB1RF.machine BusyBeaver.M_1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LFHHH_1LB1RF.is_not_halt
theorem raw0_new_cover : Cover NeverHalts (leaf raw0_new) :=
  Cover.leaf _ (all_completions_never _ raw0_new_never)
def raw0_new_path : List (Nat × Slot) := [(1, (1, false)), (2, (0, true)), (3, (2, false)), (5, (1, true)), (6, (3, false)), (7, (4, false)), (8, (5, true)), (10, (5, false)), (12, (3, true)), (16, (2, true))]
theorem raw0_new_reachable : FirstHolePath (leaf raw0_new) 6 := by
  change FirstHolePath (forgetHaltRows raw0_new) 6
  exact checked_from_root raw0_new raw0_new_path (by decide +kernel)
def raw0_new_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf raw0_new) 6 := by
  change WeightedTNFCertificate B (forgetHaltRows raw0_new) 6
  exact forgetHaltRows_nonhaltCertificate B raw0_new (by rfl) raw0_new_never
theorem raw0_new_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf raw0_new) :=
  (raw0_new_weighted_cert B).toCover
#print axioms raw0_new_eq
#print axioms raw0_new_never
#print axioms raw0_new_cover
#print axioms raw0_new_reachable
#print axioms raw0_new_weighted_cover

end BB6.Agent9Nov27
