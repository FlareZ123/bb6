import CapAnchorRoots
import CapSignedMacroSource

namespace CapSieve
open BusyBeaver

theorem anchor_h421 : IsHalt BusyBeaver.M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.target ↔
    ∃ k n q, 5≤k ∧ terminalAt k n=some q ∧ anchorOf k q=some (5,41) :=
  signed_h421.trans target_421

theorem anchor_h252 : IsHalt BusyBeaver.M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE.target ↔
    ∃ k n q, 5≤k ∧ terminalAt k n=some q ∧ anchorOf k q=some (5,35) :=
  signed_h252.trans target_252

theorem anchor_h754 : IsHalt BusyBeaver.M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE.target ↔
    ∃ k n q, 5≤k ∧ terminalAt k n=some q ∧ anchorOf k q=some (5,197) :=
  signed_h754.trans target_754

#print axioms anchor_h421
#print axioms anchor_h252
#print axioms anchor_h754
end CapSieve
