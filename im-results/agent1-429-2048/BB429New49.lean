import BB429New34
import BB429AutoGroup5
import BB429AutoGroup6
import BB429Shift53And721

namespace BB429New49

/-- Forty-nine entire terminal first-counter residue cylinders ruled out
    for actual BB429 blank-root runs. -/
def NewGate (a : Nat) : Prop :=
  BB429New34.NewGate a ∨
  a%2048=53 ∨
  a%2048=585 ∨
  a%2048=629 ∨
  a%2048=649 ∨
  a%2048=721 ∨
  a%2048=1225 ∨
  a%2048=1269 ∨
  a%2048=1461 ∨
  a%2048=1489 ∨
  a%2048=1589 ∨
  a%2048=1717 ∨
  a%2048=1737 ∨
  a%2048=1781 ∨
  a%2048=1873 ∨
  a%2048=2001

/-- A source-checked theorem over all macro-step counts and natural counters,
    not a finite simulation of a particular trajectory. -/
theorem blank_halt_not_newGate (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b)) (hg : b+1=2*a) :
    ¬ NewGate a := by
  intro h
  unfold NewGate at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact BB429New34.blank_halt_not_newGate n a b hr hg h
  · exact BB429Shift53And721.blank_halt_not_53_mod2048 n a b hr hg h
  · exact BB429AutoGroup5.blank_halt_not_585_mod2048 n a b hr hg h
  · exact BB429AutoGroup5.blank_halt_not_629_mod2048 n a b hr hg h
  · exact BB429AutoGroup5.blank_halt_not_649_mod2048 n a b hr hg h
  · exact BB429Shift53And721.blank_halt_not_721_mod2048 n a b hr hg h
  · exact BB429AutoGroup5.blank_halt_not_1225_mod2048 n a b hr hg h
  · exact BB429AutoGroup5.blank_halt_not_1269_mod2048 n a b hr hg h
  · exact BB429AutoGroup5.blank_halt_not_1461_mod2048 n a b hr hg h
  · exact BB429AutoGroup5.blank_halt_not_1489_mod2048 n a b hr hg h
  · exact BB429AutoGroup6.blank_halt_not_1589_mod2048 n a b hr hg h
  · exact BB429AutoGroup6.blank_halt_not_1717_mod2048 n a b hr hg h
  · exact BB429AutoGroup6.blank_halt_not_1737_mod2048 n a b hr hg h
  · exact BB429AutoGroup6.blank_halt_not_1781_mod2048 n a b hr hg h
  · exact BB429AutoGroup6.blank_halt_not_1873_mod2048 n a b hr hg h
  · exact BB429AutoGroup6.blank_halt_not_2001_mod2048 n a b hr hg h

#print axioms blank_halt_not_newGate
end BB429New49
