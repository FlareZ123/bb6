import CapSignedRoots
import CapForwardMacroSource

namespace CapSieve
open BusyBeaver

theorem signed_h421 : IsHalt BusyBeaver.M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.target ↔
    ∃ limit, signedHaltBy limit 0 6=true :=
  macro_h421.trans signed_root_two

theorem signed_h252 : IsHalt BusyBeaver.M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE.target ↔
    ∃ limit, signedHaltBy limit 0 12=true :=
  macro_h252.trans signed_root_one

theorem signed_h754 : IsHalt BusyBeaver.M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE.target ↔
    ∃ limit, signedHaltBy limit 0 8=true :=
  macro_h754.trans signed_root_three

#print axioms signed_h421
#print axioms signed_h252
#print axioms signed_h754
end CapSieve
