import SheepFaninOriginal
namespace SheepFaninParameters
open SheepBoostSourceModel

/-- A legal generic first-even source carries a canonical valuation and
odd-block length. Distinct (valuation, hidden-length) pairs always
represent distinct actual source states. -/
theorem index_determined_by_source {a b v w h g q r : Nat}
    (hvodd : v%2=1) (hwodd : w%2=1)
    (hqodd : q%2=1) (hrodd : r%2=1)
    (hsame : 2^a*v=2^b*w)
    (hfirst : GenericF a v=1+2^h*q)
    (hsecond : GenericF b w=1+2^g*r) :
    a=b ∧ h=g := by
  obtain ⟨hab,hvw⟩ :=
    SheepEven.factor_odd_unique a b v w hvodd hwodd hsame
  subst b
  subst w
  have hfactor : 2^h*q=2^g*r := by omega
  exact ⟨rfl,(SheepEven.factor_odd_unique h g q r hqodd hrodd hfactor).1⟩

/-- Uniqueness of the hidden odd-run exponent for the exact published
source section, independent of the target chosen. -/
theorem odd_hidden_length_unique {a v h g q r : Nat}
    (hqodd : q%2=1) (hrodd : r%2=1)
    (hfirst : GenericF a v=1+2^h*q)
    (hsecond : GenericF a v=1+2^g*r) : h=g := by
  have hf : 2^h*q=2^g*r := by omega
  exact (SheepEven.factor_odd_unique h g q r hqodd hrodd hf).1

#print axioms index_determined_by_source
#print axioms odd_hidden_length_unique
end SheepFaninParameters
