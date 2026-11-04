import BB429No393mod512
import BB429No265mod512
import BB429No137mod1024
import BB429No521mod1024
import Lean.Elab.Tactic.Omega
namespace BB429NineSector
/-- Of the eight 9(mod128) classes modulo1024, only 9 and 649 can
    occur at the source-accurate blank-root halting line. -/
theorem blank_terminal_nine_only_two (n a b : Nat)
    (hr : BB429.run n (0,0) = some (a,b))
    (hg : b+1=2*a) (h9 : a%128=9) :
    a%1024=9 ∨ a%1024=649 := by
  have h393 := BB429No393mod512.blank_halt_not_393_mod512 n a b hr hg
  have h265 := BB429No265mod512.blank_halt_not_265_mod512 n a b hr hg
  have h137 := BB429No137mod1024.blank_halt_not_137_mod1024 n a b hr hg
  have h521 := BB429No521mod1024.blank_halt_not_521_mod1024 n a b hr hg
  omega
#print axioms blank_terminal_nine_only_two
end BB429NineSector
