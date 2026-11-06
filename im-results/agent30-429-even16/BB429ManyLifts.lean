import BB429No11473mod16384
import Lean.Elab.Tactic.Omega

namespace BB429ManyLifts
open BB429NewResidue BB429Kernel16

/-- Forty additional residue cylinders, all drawn from the current 52/8192
    necessary terminal set and disjoint from the already excluded 11473
    modulo 16384 cylinder. -/
def newLifts : List Nat :=
  [565,849,2249,2257,3409,3965,4021,4213,4297,4305,
   4945,5129,6013,6217,6909,8201,8529,8657,8957,9289,
   9333,9865,9981,10165,10249,10357,10577,10877,11273,11337,
   11381,12361,12853,13237,13649,14537,14581,15285,16125,16253]

theorem new_lifts_count : newLifts.length = 40 := by decide
theorem new_lifts_nodup : newLifts.Nodup := by decide

/-- Kernel evaluation of the symbolic inverse certificate for every listed
    residue. The parameter q remains universally quantified below. -/
theorem new_lifts_certificate :
    newLifts.all (fun r => cert 12 ⟨16384,r,32768,2*r-1⟩) = true := by
  decide

theorem certificate_for_mem (r : Nat) (hr : r ∈ newLifts) :
    cert 12 ⟨16384,r,32768,2*r-1⟩ = true :=
  (List.all_eq_true.mp new_lifts_certificate) r hr

/-- Each listed affine cylinder is disjoint from the genuine blank-root
    reachability relation, uniformly for every natural q. -/
theorem no_reach_cylinder (q r : Nat) (hr : r ∈ newLifts) :
    ¬ Reach (16384*q+r) (32768*q+2*r-1) := by
  have hrpos : 0<r := by simp [newLifts] at hr; omega
  have hcert := cert_sound 12 ⟨16384,r,32768,2*r-1⟩ q
    (certificate_for_mem r hr)
  convert hcert using 1 <;> simp [va, vb] <;> omega

/-- The exact BB429 blank-root orbit avoids all forty additional terminal
    residues. No finite-time cutoff is assumed. -/
theorem blank_halt_not_new_lifts (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) :
    a%16384 ∉ newLifts := by
  intro hm
  let r := a%16384
  let q := a/16384
  have hrmem : r ∈ newLifts := by simpa [r] using hm
  have hrpos : 0<r := by simp [newLifts] at hrmem; omega
  have ha : a=16384*q+r := by dsimp [q,r]; omega
  have hb : b=32768*q+2*r-1 := by omega
  have hrun : BB429.run n (0,0)=some (16384*q+r,32768*q+2*r-1) := by
    rw [ha,hb] at hr
    exact hr
  exact no_reach_cylinder q r hrmem ⟨n,hrun⟩

#print axioms new_lifts_certificate
#print axioms no_reach_cylinder
#print axioms blank_halt_not_new_lifts
end BB429ManyLifts
