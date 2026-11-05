import NeedlePeriodCore
set_option maxHeartbeats 0
namespace NeedlePeriodTriple
open NeedlePeriodCore

def exponent (t : Nat) : Nat := 1756236+1855188*t

private theorem source_period (d r : Nat) (hrlt : r<d)
    (hbase : Nat.powMod 2 1756236 d=r)
    (hperiod : Nat.powMod 2 1855188 d=1) (t : Nat) :
    (2:Nat)^(exponent t)%d=r%d := by
  have ha : (2:Nat)^1756236%d=r%d := by
    rw [←Nat.powMod_def,hbase]
    exact (Nat.mod_eq_of_lt hrlt).symm
  have hp : (2:Nat)^1855188%d=1 := by
    rw [←Nat.powMod_def]
    exact hperiod
  exact periodic_mod d 1756236 1855188 r ha hp t

theorem all_bases (t : Nat) :
    (2:Nat)^(exponent t)%5=1 ∧
    (2:Nat)^(exponent t)%19=11 ∧
    (2:Nat)^(exponent t)%2097155=1048596 := by
  have h5 : Nat.powMod 2 1756236 5=1 := by decide
  have p5 : Nat.powMod 2 1855188 5=1 := by decide
  have h19 : Nat.powMod 2 1756236 19=11 := by decide
  have p19 : Nat.powMod 2 1855188 19=1 := by decide
  have hlarge : Nat.powMod 2 1756236 2097155=1048596 := by decide
  have plarge : Nat.powMod 2 1855188 2097155=1 := by decide
  have hfirst := source_period 5 1 (by decide) h5 p5 t
  have hsecond := source_period 19 11 (by decide) h19 p19 t
  have hthird := source_period 2097155 1048596 (by decide) hlarge plarge t
  exact ⟨hfirst,hsecond,hthird⟩

#print axioms all_bases
end NeedlePeriodTriple
