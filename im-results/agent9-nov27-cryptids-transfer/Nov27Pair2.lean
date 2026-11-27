import Nov26SourceCore
import FirstHolePath
import BusyBeaver.BB6.NonHalt.M_1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_HHH0LA
import BusyBeaver.BB6.NonHalt.M_1RB0LD_1LC0RE_HHH1LD_1LE1LA_1RA0LF_1LC1RE

namespace BB6.Agent9Nov27
open BB6Coverage BB6.ConjectureBridge BB6.Agent10Nov26 BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Raw10; exact literal table, with halt row left unspecified in leaf. -/
def raw10_1 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,2⟩, some ⟨true,false,2⟩, some ⟨false,true,4⟩, some ⟨true,true,0⟩, some ⟨true,false,3⟩, some ⟨true,false,0⟩, some ⟨true,false,2⟩, some ⟨true,true,5⟩, some ⟨false,true,0⟩, none, some ⟨false,false,0⟩]
theorem raw10_1_eq : toAgent8 BusyBeaver.M_1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_HHH0LA.machine = raw10_1 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem raw10_1_never : NeverHalts raw10_1 := by
  rw [← raw10_1_eq]
  exact source_never BusyBeaver.M_1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_HHH0LA.machine BusyBeaver.M_1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_HHH0LA.is_not_halt
theorem raw10_1_cover : Cover NeverHalts (leaf raw10_1) :=
  Cover.leaf _ (all_completions_never _ raw10_1_never)
def raw10_1_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (3, false)), (5, (1, true)), (6, (4, true)), (7, (0, true)), (8, (2, false)), (12, (3, true)), (26, (4, false)), (27, (5, true))]
theorem raw10_1_reachable : FirstHolePath (leaf raw10_1) 6 := by
  change FirstHolePath (forgetHaltRows raw10_1) 6
  exact checked_from_root raw10_1 raw10_1_path (by decide +kernel)
def raw10_1_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf raw10_1) 6 := by
  change WeightedTNFCertificate B (forgetHaltRows raw10_1) 6
  exact forgetHaltRows_nonhaltCertificate B raw10_1 (by rfl) raw10_1_never
theorem raw10_1_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf raw10_1) :=
  (raw10_1_weighted_cert B).toCover
#print axioms raw10_1_eq
#print axioms raw10_1_never
#print axioms raw10_1_cover
#print axioms raw10_1_reachable
#print axioms raw10_1_weighted_cover

/-- Raw10; exact literal table, with halt row left unspecified in leaf. -/
def raw10_2 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,3⟩, some ⟨true,false,2⟩, some ⟨false,true,4⟩, none, some ⟨true,false,3⟩, some ⟨true,false,4⟩, some ⟨true,false,0⟩, some ⟨true,true,0⟩, some ⟨false,false,5⟩, some ⟨true,false,2⟩, some ⟨true,true,4⟩]
theorem raw10_2_eq : toAgent8 BusyBeaver.M_1RB0LD_1LC0RE_HHH1LD_1LE1LA_1RA0LF_1LC1RE.machine = raw10_2 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem raw10_2_never : NeverHalts raw10_2 := by
  rw [← raw10_2_eq]
  exact source_never BusyBeaver.M_1RB0LD_1LC0RE_HHH1LD_1LE1LA_1RA0LF_1LC1RE.machine BusyBeaver.M_1RB0LD_1LC0RE_HHH1LD_1LE1LA_1RA0LF_1LC1RE.is_not_halt
theorem raw10_2_cover : Cover NeverHalts (leaf raw10_2) :=
  Cover.leaf _ (all_completions_never _ raw10_2_never)
def raw10_2_path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (3, false)), (4, (4, false)), (5, (0, true)), (6, (3, true)), (8, (1, true)), (26, (4, true)), (27, (5, false)), (66, (5, true))]
theorem raw10_2_reachable : FirstHolePath (leaf raw10_2) 6 := by
  change FirstHolePath (forgetHaltRows raw10_2) 6
  exact checked_from_root raw10_2 raw10_2_path (by decide +kernel)
def raw10_2_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf raw10_2) 6 := by
  change WeightedTNFCertificate B (forgetHaltRows raw10_2) 6
  exact forgetHaltRows_nonhaltCertificate B raw10_2 (by rfl) raw10_2_never
theorem raw10_2_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf raw10_2) :=
  (raw10_2_weighted_cert B).toCover
#print axioms raw10_2_eq
#print axioms raw10_2_never
#print axioms raw10_2_cover
#print axioms raw10_2_reachable
#print axioms raw10_2_weighted_cover

end BB6.Agent9Nov27
