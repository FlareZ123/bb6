import CapForwardMacroReach
import CapBmoSource
import CapSource

namespace CapSieve
open BusyBeaver

theorem macro_h421 : IsHalt BusyBeaver.M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.target ↔
    ∃ limit, bandHaltBy limit 0 6=true :=
  CapSource.H421.root_criterion.trans ((Bmo.root_criterion Cap.root_two).symm.trans macro_root_two.symm)

theorem macro_h252 : IsHalt BusyBeaver.M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE.target ↔
    ∃ limit, bandHaltBy limit 0 12=true :=
  CapSource.H252.root_criterion.trans ((Bmo.root_criterion Cap.root_one).symm.trans macro_root_one.symm)

theorem macro_h754 : IsHalt BusyBeaver.M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE.target ↔
    ∃ limit, bandHaltBy limit 0 8=true :=
  CapSource.H754.root_criterion.trans ((Bmo.root_criterion Cap.root_three).symm.trans macro_root_three.symm)

#print axioms macro_h421
#print axioms macro_h252
#print axioms macro_h754
end CapSieve
