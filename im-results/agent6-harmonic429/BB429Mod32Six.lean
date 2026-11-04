import BB429Extra19
import BB429Depth4
import BB429OneGate
import BB429Thirteen
import Lean.Elab.Tactic.Omega

namespace BB429Mod32Six
/-- Every genuine BB429 accelerated blank-origin halting site has first
    counter in exactly one of these six necessary residues modulo 32.
    This is a necessary restriction only; each listed residue remains open. -/
theorem blank_halting_mod32_six (n u w : Nat)
    (h : BB429.run n (0,0) = some (u,w))
    (hn : BB429.next (u,w)=none) :
    u%32=3 ∨ u%32=9 ∨ u%32=17 ∨ u%32=21 ∨ u%32=25 ∨ u%32=29 := by
  have h9 := BB429Extra19.blank_halting_mod32 n u w h hn
  have h1 := BB429OneGate.blank_halt_u_not_1 n u w h hn
  have h5 := BB429Depth4.blank_halt_u_not_5 n u w h hn
  have h13 := BB429Thirteen.blank_halt_u_not_13 n u w h hn
  omega

#print axioms blank_halting_mod32_six
end BB429Mod32Six
