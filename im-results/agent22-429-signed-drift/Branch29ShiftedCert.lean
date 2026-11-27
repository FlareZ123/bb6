import BB429InverseKernel
import Lean.Elab.Tactic.Omega

/-!
# Source-sound shifted affine residue lifting for the #429 branch-29 line

An inverse certificate at q=m*(t+1)+r excludes the *whole tail*
of the progression q=r (mod m), independent of upper bounds on q.

A separate proof that the initial representative q=r is unreachable
completes the full progression. The proof works for arbitrary positive
moduli m and is reusable at any depth d and any residue class r.

The shift by one modulus is useful when an unshifted affine certificate
contains small-constant leaves that prevent closure.
-/

namespace BB429ShiftedCert

/-- Parameter-index-1 affine cylinder for (32q+29,64q+55). -/
def shiftedAffine (m r : Nat) : BB429Kernel.Affine :=
  ⟨32*m,32*(m+r)+29,64*m,64*(m+r)+55⟩

theorem shifted_va (m r t : Nat) :
    BB429Kernel.va (shiftedAffine m r) t =
    32*(m*(t+1)+r)+29 := by
  simp [BB429Kernel.va,shiftedAffine,Nat.mul_add,Nat.add_mul,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  omega

theorem shifted_vb (m r t : Nat) :
    BB429Kernel.vb (shiftedAffine m r) t =
    64*(m*(t+1)+r)+55 := by
  simp [BB429Kernel.vb,shiftedAffine,Nat.mul_add,Nat.add_mul,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  omega

/-- A verified shifted affine inverse certificate excludes every
parameter q>=m satisfying q mod m = r. -/
theorem shifted_cert_sound (m r d q : Nat)
    (hm : 0<m) (hq : m≤q) (hmod : q%m=r)
    (hcert : BB429Kernel.cert d (shiftedAffine m r)=true) :
    ¬BB429NewResidue.Reach (32*q+29) (64*q+55) := by
  let t := q/m-1
  have hquot : 0<q/m := Nat.div_pos hq hm
  have hqt : q/m=t+1 := by dsimp [t]; omega
  have hdecomp : q=m*(t+1)+r := by
    calc
      q = q%m + m*(q/m) := (Nat.mod_add_div q m).symm
      _ = r + m*(t+1) := by rw [hmod,hqt]
      _ = m*(t+1)+r := Nat.add_comm _ _
  have hx : BB429Kernel.va (shiftedAffine m r) t = 32*q+29 := by
    rw [shifted_va m r t,hdecomp]
  have hy : BB429Kernel.vb (shiftedAffine m r) t = 64*q+55 := by
    rw [shifted_vb m r t,hdecomp]
  intro hroot
  have hs : BB429NewResidue.Reach
      (BB429Kernel.va (shiftedAffine m r) t)
      (BB429Kernel.vb (shiftedAffine m r) t) := by
    simpa only [hx,hy] using hroot
  exact (BB429Kernel.cert_sound d (shiftedAffine m r) t hcert) hs

/-- A sound exclusion for the initial representative, together with a
verified shifted affine certificate, excludes the complete residue
class for all q without a finite-horizon hypothesis. -/
theorem residue_excluded (m r d : Nat) (hm : 0<m)
    (hbase : ¬BB429NewResidue.Reach (32*r+29) (64*r+55))
    (hcert : BB429Kernel.cert d (shiftedAffine m r)=true)
    (q : Nat) (hmod : q%m=r) :
    ¬BB429NewResidue.Reach (32*q+29) (64*q+55) := by
  by_cases hsmall : q < m
  · have hqeq : q=r := by
      have hqmod : q%m=q := Nat.mod_eq_of_lt hsmall
      omega
    simpa only [hqeq] using hbase
  · exact shifted_cert_sound m r d q hm (by omega) hmod hcert

#print axioms shifted_cert_sound
#print axioms residue_excluded
end BB429ShiftedCert
