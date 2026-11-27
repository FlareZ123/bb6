import Nov26SourceCore
import FirstHolePath
import BusyBeaver.BB6.NonHalt.M_1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_HHH0RC
import BusyBeaver.BB6.NonHalt.M_1RB0LF_1LC0LA_HHH1RD_1RF1RE_1LF1RD_1LB0RE

namespace BB6.Agent9Nov27
open BB6Coverage BB6.ConjectureBridge BB6.Agent10Nov26 BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Raw10; exact literal table, with halt row left unspecified in leaf. -/
def raw10_3 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,4⟩, some ⟨true,false,2⟩, some ⟨true,true,3⟩, some ⟨true,false,0⟩, some ⟨false,true,1⟩, some ⟨true,true,2⟩, some ⟨true,true,1⟩, some ⟨true,false,5⟩, some ⟨false,false,2⟩, none, some ⟨false,true,2⟩]
theorem raw10_3_eq : toAgent8 BusyBeaver.M_1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_HHH0RC.machine = raw10_3 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem raw10_3_never : NeverHalts raw10_3 := by
  rw [← raw10_3_eq]
  exact source_never BusyBeaver.M_1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_HHH0RC.machine BusyBeaver.M_1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_HHH0RC.is_not_halt
theorem raw10_3_cover : Cover NeverHalts (leaf raw10_3) :=
  Cover.leaf _ (all_completions_never _ raw10_3_never)
def raw10_3_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (1, true)), (4, (3, false)), (5, (2, false)), (6, (0, true)), (7, (4, true)), (20, (3, true)), (34, (4, false)), (35, (5, true))]
theorem raw10_3_reachable : FirstHolePath (leaf raw10_3) 6 := by
  change FirstHolePath (forgetHaltRows raw10_3) 6
  exact checked_from_root raw10_3 raw10_3_path (by decide +kernel)
def raw10_3_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf raw10_3) 6 := by
  change WeightedTNFCertificate B (forgetHaltRows raw10_3) 6
  exact forgetHaltRows_nonhaltCertificate B raw10_3 (by rfl) raw10_3_never
theorem raw10_3_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf raw10_3) :=
  (raw10_3_weighted_cert B).toCover
#print axioms raw10_3_eq
#print axioms raw10_3_never
#print axioms raw10_3_cover
#print axioms raw10_3_reachable
#print axioms raw10_3_weighted_cover

/-- Raw10; exact literal table, with halt row left unspecified in leaf. -/
def raw10_4 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,5⟩, some ⟨true,false,2⟩, some ⟨false,false,0⟩, none, some ⟨true,true,3⟩, some ⟨true,true,5⟩, some ⟨true,true,4⟩, some ⟨true,false,5⟩, some ⟨true,true,3⟩, some ⟨true,false,1⟩, some ⟨false,true,4⟩]
theorem raw10_4_eq : toAgent8 BusyBeaver.M_1RB0LF_1LC0LA_HHH1RD_1RF1RE_1LF1RD_1LB0RE.machine = raw10_4 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem raw10_4_never : NeverHalts raw10_4 := by
  rw [← raw10_4_eq]
  exact source_never BusyBeaver.M_1RB0LF_1LC0LA_HHH1RD_1RF1RE_1LF1RD_1LB0RE.machine BusyBeaver.M_1RB0LF_1LC0LA_HHH1RD_1RF1RE_1LF1RD_1LB0RE.is_not_halt
theorem raw10_4_cover : Cover NeverHalts (leaf raw10_4) :=
  Cover.leaf _ (all_completions_never _ raw10_4_never)
def raw10_4_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (3, true)), (4, (4, false)), (5, (5, true)), (6, (4, true)), (7, (3, false)), (8, (5, false)), (9, (1, true)), (10, (0, true))]
theorem raw10_4_reachable : FirstHolePath (leaf raw10_4) 6 := by
  change FirstHolePath (forgetHaltRows raw10_4) 6
  exact checked_from_root raw10_4 raw10_4_path (by decide +kernel)
def raw10_4_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf raw10_4) 6 := by
  change WeightedTNFCertificate B (forgetHaltRows raw10_4) 6
  exact forgetHaltRows_nonhaltCertificate B raw10_4 (by rfl) raw10_4_never
theorem raw10_4_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf raw10_4) :=
  (raw10_4_weighted_cert B).toCover
#print axioms raw10_4_eq
#print axioms raw10_4_never
#print axioms raw10_4_cover
#print axioms raw10_4_reachable
#print axioms raw10_4_weighted_cover

end BB6.Agent9Nov27
