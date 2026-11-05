import BB429No181mod2048
import BB429Auto329
import BB429AutoGroup1
import BB429AutoGroup2
import BB429AutoGroup3
import BB429AutoGroup4
import Lean.Elab.Tactic.Omega

namespace BB429New34

/-- Explicit union of thirty-four genuinely root-excluded complete
    terminal residue cylinders. -/
def NewGate (a : Nat) : Prop :=
  a%2048=181 ∨
  a%2048=309 ∨
  a%2048=329 ∨
  a%2048=373 ∨
  a%2048=437 ∨
  a%2048=457 ∨
  a%2048=501 ∨
  a%2048=593 ∨
  a%2048=693 ∨
  a%2048=713 ∨
  a%2048=757 ∨
  a%2048=821 ∨
  a%2048=841 ∨
  a%2048=885 ∨
  a%2048=969 ∨
  a%2048=977 ∨
  a%2048=1013 ∨
  a%2048=1077 ∨
  a%2048=1105 ∨
  a%2048=1205 ∨
  a%2048=1333 ∨
  a%2048=1353 ∨
  a%2048=1397 ∨
  a%2048=1481 ∨
  a%2048=1525 ∨
  a%2048=1609 ∨
  a%2048=1617 ∨
  a%2048=1653 ∨
  a%2048=1745 ∨
  a%2048=1845 ∨
  a%2048=1865 ∨
  a%2048=1909 ∨
  a%2048=1993 ∨
  a%2048=2037

/-- Every real blank-root halting-line state avoids all 34 residues.
    Each conjunct is an unchanged-accelerator-source-certified theorem. -/
theorem blank_halt_not_thirtyfour (n a b : Nat)
    (hr : BB429.run n (0,0)=some(a,b)) (hg : b+1=2*a) :
    a%2048≠181 ∧
    a%2048≠309 ∧
    a%2048≠329 ∧
    a%2048≠373 ∧
    a%2048≠437 ∧
    a%2048≠457 ∧
    a%2048≠501 ∧
    a%2048≠593 ∧
    a%2048≠693 ∧
    a%2048≠713 ∧
    a%2048≠757 ∧
    a%2048≠821 ∧
    a%2048≠841 ∧
    a%2048≠885 ∧
    a%2048≠969 ∧
    a%2048≠977 ∧
    a%2048≠1013 ∧
    a%2048≠1077 ∧
    a%2048≠1105 ∧
    a%2048≠1205 ∧
    a%2048≠1333 ∧
    a%2048≠1353 ∧
    a%2048≠1397 ∧
    a%2048≠1481 ∧
    a%2048≠1525 ∧
    a%2048≠1609 ∧
    a%2048≠1617 ∧
    a%2048≠1653 ∧
    a%2048≠1745 ∧
    a%2048≠1845 ∧
    a%2048≠1865 ∧
    a%2048≠1909 ∧
    a%2048≠1993 ∧
    a%2048≠2037 := by
  exact ⟨BB429No181mod2048.blank_halt_not_181_mod2048 n a b hr hg,
      BB429AutoGroup1.blank_halt_not_309_mod2048 n a b hr hg,
      BB429Auto329.blank_halt_not_329_mod2048 n a b hr hg,
      BB429AutoGroup1.blank_halt_not_373_mod2048 n a b hr hg,
      BB429AutoGroup1.blank_halt_not_437_mod2048 n a b hr hg,
      BB429AutoGroup1.blank_halt_not_457_mod2048 n a b hr hg,
      BB429AutoGroup1.blank_halt_not_501_mod2048 n a b hr hg,
      BB429AutoGroup1.blank_halt_not_593_mod2048 n a b hr hg,
      BB429AutoGroup1.blank_halt_not_693_mod2048 n a b hr hg,
      BB429AutoGroup1.blank_halt_not_713_mod2048 n a b hr hg,
      BB429AutoGroup2.blank_halt_not_757_mod2048 n a b hr hg,
      BB429AutoGroup2.blank_halt_not_821_mod2048 n a b hr hg,
      BB429AutoGroup2.blank_halt_not_841_mod2048 n a b hr hg,
      BB429AutoGroup2.blank_halt_not_885_mod2048 n a b hr hg,
      BB429AutoGroup2.blank_halt_not_969_mod2048 n a b hr hg,
      BB429AutoGroup2.blank_halt_not_977_mod2048 n a b hr hg,
      BB429AutoGroup2.blank_halt_not_1013_mod2048 n a b hr hg,
      BB429AutoGroup2.blank_halt_not_1077_mod2048 n a b hr hg,
      BB429AutoGroup3.blank_halt_not_1105_mod2048 n a b hr hg,
      BB429AutoGroup3.blank_halt_not_1205_mod2048 n a b hr hg,
      BB429AutoGroup3.blank_halt_not_1333_mod2048 n a b hr hg,
      BB429AutoGroup3.blank_halt_not_1353_mod2048 n a b hr hg,
      BB429AutoGroup3.blank_halt_not_1397_mod2048 n a b hr hg,
      BB429AutoGroup3.blank_halt_not_1481_mod2048 n a b hr hg,
      BB429AutoGroup3.blank_halt_not_1525_mod2048 n a b hr hg,
      BB429AutoGroup3.blank_halt_not_1609_mod2048 n a b hr hg,
      BB429AutoGroup4.blank_halt_not_1617_mod2048 n a b hr hg,
      BB429AutoGroup4.blank_halt_not_1653_mod2048 n a b hr hg,
      BB429AutoGroup4.blank_halt_not_1745_mod2048 n a b hr hg,
      BB429AutoGroup4.blank_halt_not_1845_mod2048 n a b hr hg,
      BB429AutoGroup4.blank_halt_not_1865_mod2048 n a b hr hg,
      BB429AutoGroup4.blank_halt_not_1909_mod2048 n a b hr hg,
      BB429AutoGroup4.blank_halt_not_1993_mod2048 n a b hr hg,
      BB429AutoGroup4.blank_halt_not_2037_mod2048 n a b hr hg⟩

theorem blank_halt_not_newGate (n a b : Nat)
    (hr : BB429.run n (0,0)=some(a,b)) (hg : b+1=2*a) :
    ¬ NewGate a := by
  simpa only [NewGate, not_or] using
    blank_halt_not_thirtyfour n a b hr hg

#print axioms blank_halt_not_thirtyfour
#print axioms blank_halt_not_newGate
end BB429New34
