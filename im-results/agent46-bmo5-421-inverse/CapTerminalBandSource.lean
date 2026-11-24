import CapModNoGo
import CapAnchorSource
namespace CapSieve
open BusyBeaver

theorem band_anchor_iff {a : Nat} (ha : CanonQ 5 a) :
    (∃ k n q, 5 ≤ k ∧ terminalAt k n = some q ∧ anchorOf k q = some (5,a)) ↔
    ∃ i k q, terminalFromBand i = some (k,q) ∧ anchorOf k q = some (5,a) :=
  (anchor_terminal_iff ha).symm.trans (anchor_terminal_band_iff ha)

theorem terminal_band_h421 : IsHalt BusyBeaver.M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.target ↔
    ∃ i k q, terminalFromBand i = some (k,q) ∧ anchorOf k q = some (5,41) :=
  anchor_h421.trans (band_anchor_iff anchor_canon_421)

theorem terminal_band_h252 : IsHalt BusyBeaver.M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE.target ↔
    ∃ i k q, terminalFromBand i = some (k,q) ∧ anchorOf k q = some (5,35) :=
  anchor_h252.trans (band_anchor_iff anchor_canon_252)

theorem terminal_band_h754 : IsHalt BusyBeaver.M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE.target ↔
    ∃ i k q, terminalFromBand i = some (k,q) ∧ anchorOf k q = some (5,197) :=
  anchor_h754.trans (band_anchor_iff anchor_canon_754)

#print axioms terminal_band_h421
#print axioms terminal_band_h252
#print axioms terminal_band_h754
end CapSieve
