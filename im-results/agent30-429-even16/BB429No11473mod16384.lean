import BB429InverseKernel16
import Lean.Elab.Tactic.Omega

namespace BB429No11473
open BB429NewResidue BB429Kernel16
set_option maxHeartbeats 20000000
set_option maxRecDepth 32768

/-- Symbolic parameter-uniform inverse tree. This is not a finite orbit
search: its parameter q is universally quantified by cert_sound. -/
theorem all_parameter_certificate :
    cert 12 ⟨16384,11473,32768,22945⟩ = true := by
  decide

theorem no_reach_entire_cylinder (q : Nat) :
    ¬Reach (16384*q+11473) (32768*q+22945) := by
  exact cert_sound 12 ⟨16384,11473,32768,22945⟩ q
    all_parameter_certificate

/-- Any actual blank-root halting line avoids the entire cylinder,
strengthening an existing exclusion of only one of its four mod-65536 lifts. -/
theorem blank_halt_not_11473_mod16384 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%16384≠11473 := by
  intro hm
  let q := a/16384
  have ha : a=16384*q+11473 := by dsimp [q]; omega
  have hb : b=32768*q+22945 := by omega
  have hreach : Reach (16384*q+11473) (32768*q+22945) :=
    ⟨n, by simpa only [←ha,←hb] using hr⟩
  exact no_reach_entire_cylinder q hreach

#print axioms all_parameter_certificate
#print axioms no_reach_entire_cylinder
#print axioms blank_halt_not_11473_mod16384
end BB429No11473
