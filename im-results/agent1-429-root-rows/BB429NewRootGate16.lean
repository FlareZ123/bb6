import BB429InverseKernelExtended
import Lean.Elab.Tactic.Omega

namespace BB429NewRootGate16
open BB429NewResidue
open BB429KernelExtended
set_option maxHeartbeats 20000000
set_option maxRecDepth 32768

/-- Two distinct genuine blank-root terminal cylinders at modulus 65536. -/
def excluded2 : List Nat := [11473,57341]

/-- A finite computation of symbolic, all-parameter inverse trees. -/
theorem excluded2_certificate :
    excluded2.all (fun r => cert 14 ⟨65536,r,131072,2*r-1⟩) = true := by
  decide

theorem excluded2_positive (r : Nat) (hr : r∈excluded2) : 0<r := by
  simp [excluded2] at hr
  omega

theorem no_reach2 (r q : Nat) (hr : r∈excluded2) :
    ¬Reach (65536*q+r) (131072*q+(2*r-1)) := by
  have hc : cert 14 ⟨65536,r,131072,2*r-1⟩ = true :=
    (List.all_eq_true.mp excluded2_certificate) r hr
  exact cert_sound 14 ⟨65536,r,131072,2*r-1⟩ q hc

/-- Every parameter q is excluded, including q=0. -/
theorem blank_no_halt_two (n a b r : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) (hm : a%65536=r)
    (hre : r∈excluded2) : False := by
  let q := a/65536
  have hpos := excluded2_positive r hre
  have hsmall : r<65536 := by simp [excluded2] at hre; omega
  have ha : a=65536*q+r := by dsimp [q]; omega
  have hb : b=131072*q+(2*r-1) := by omega
  have hh : Reach (65536*q+r) (131072*q+(2*r-1)) :=
    ⟨n, by simpa only [←ha,←hb] using hr⟩
  exact (no_reach2 r q hre) hh

theorem blank_halt_not_11473 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%65536≠11473 := by
  intro hm
  exact blank_no_halt_two n a b 11473 hr hg hm (by decide)

theorem blank_halt_not_57341 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%65536≠57341 := by
  intro hm
  exact blank_no_halt_two n a b 57341 hr hg hm (by decide)

#print axioms excluded2_certificate
#print axioms blank_halt_not_11473
#print axioms blank_halt_not_57341
end BB429NewRootGate16
