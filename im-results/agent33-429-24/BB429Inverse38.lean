import BB429InverseKernel
import Lean.Elab.Tactic.Omega

namespace BB429Kernel

/-- Thirty-eight inverse-refutable whole affine terminal cylinders, modulo 8192.
    Other work has independently established eight of these exclusions. -/
def excluded38 : List Nat :=
  [73,117,949,1033,1361,1917,2045,2121,2293,2613,2813,2997,
   3721,3837,4093,4105,4433,4561,4861,5193,5237,5329,
   5769,5885,6069,6153,6261,6353,6481,6609,6781,6993,
   7177,7241,7285,7377,7505,8117]

set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

/-- Proof-producing calculation: uniform inverse depth 12 suffices for every
    q in every listed family, rather than sampling finitely many q. -/
theorem excluded38_certificate :
    excluded38.all (fun r => cert 12 ⟨8192,r,16384,2*r-1⟩) = true := by
  decide

theorem excluded38_nodup : excluded38.Nodup := by decide

theorem excluded38_count : excluded38.length = 38 := by decide

theorem excluded38_positive (r : Nat) (hr : r∈excluded38) : 0<r := by
  simp [excluded38] at hr
  omega

theorem no_reach38 (r q : Nat) (hr : r∈excluded38) :
    ¬BB429NewResidue.Reach (8192*q+r) (16384*q+(2*r-1)) := by
  have hc : cert 12 ⟨8192,r,16384,2*r-1⟩ = true :=
    (List.all_eq_true.mp excluded38_certificate) r hr
  exact cert_sound 12 ⟨8192,r,16384,2*r-1⟩ q hc

/-- On the authentic blank root, no halting terminal can have any listed
    modulo-8192 first counter. A quantified statement for all n and q. -/
theorem blank_no_halt_38 (n a b r : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a)
    (hm : a%8192=r)
    (hre : r∈excluded38) : False := by
  let q := a/8192
  have hpos := excluded38_positive r hre
  have ha : a=8192*q+r := by dsimp [q]; omega
  have hb : b=16384*q+(2*r-1) := by omega
  have hh : BB429NewResidue.Reach (8192*q+r) (16384*q+(2*r-1)) := by
    exact ⟨n, by simpa only [←ha,←hb] using hr⟩
  exact (no_reach38 r q hre) hh

#print axioms excluded38_certificate
#print axioms no_reach38
#print axioms blank_no_halt_38
end BB429Kernel
