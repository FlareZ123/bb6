import ClosedCertFast
import UParentBand887
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
namespace CascadeUParentCone887
open CascadeResetInverse CascadeUParentBand887 CascadeQDepthHensel CascadeRayDepthHensel

def roots : List Nat := [z0_887 162,z0_887 324,z0_887 486,z0_887 648,z0_887 810]

def parentClosure : Nat→List Nat→List Nat
|0,xs=>xs
|n+1,xs=>xs ++ parentClosure n (xs.flatMap parentsFast)

def cone : List Nat := parentClosure 10 roots

theorem mem_parentClosure (n:Nat) (xs:List Nat) {u:Nat} (hu:u∈xs) :
    u∈parentClosure n xs := by
  induction n with
  | zero => exact hu
  | succ n ih =>
      simp [parentClosure,hu]

theorem cone_closed : closedCertFast cone=true := by decide
theorem two_not_mem_cone : 2∉cone := by decide
theorem cone_length : cone.length=31 := by decide

theorem cone_excludes_root (u:Nat) (hu:u∈cone) :
    ¬CascadeSweep.ReachC (2,0) (u,0) :=
  closedCertFast_excludes u cone cone_closed hu two_not_mem_cone

/-- Every exact parent of one of the five first-tier U children is in the
    closed 31-state inverse cone. -/
theorem first_parent_mem_cone (u q:Nat) (hu:u∈roots)
    (hq:q∈parentsFast u) : q∈cone := by
  change q∈roots ++ parentClosure 9 (roots.flatMap parentsFast)
  apply List.mem_append.mpr
  right
  exact mem_parentClosure 9 _ (List.mem_flatMap.mpr ⟨u,hu,hq⟩)

/-- Every immediate ResetParent predecessor of any of the five roots is
    excluded by the same finite closure certificate. -/
theorem first_parent_not_root (u q:Nat) (hu:u∈roots)
    (hp:ResetParent q u) : ¬CascadeSweep.ReachC (2,0) (q,0) := by
  have hmem : q∈parentsFast u := (parentsFast_iff q u).2 hp
  exact cone_excludes_root q (first_parent_mem_cone u q hu hmem)

/-- All odd U-parents of the n=887 first-tier spine are excluded from the
    blank-root component. This closes the entire t=2/t=4 U arm. -/
theorem U_odd_parent_not_root
    (j p U z q k t d : Nat)
    (hjlo:6≤j) (hjhi:j≤870) (hj6:j%6=0)
    (hp:p=2^885)
    (hform:U+2*887+2^(j+4)*1777=112*p+15)
    (hU:U=9*(2*z+5))
    (hzband:6*p-1≤z ∧ z≤8*p-3)
    (hdodd:d%2=1)
    (hband:6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1)
    (hout:2*z+5=3^(t+1)*d)
    (hscale:2*(2^t*d)=8*2^k+q+k+5) :
    ¬CascadeSweep.ReachC (2,0) (q,0) := by
  have hclass := u_odd_parent_exact_n887 j p U z q k t d
    hjlo hjhi hj6 hp hform hU hzband hdodd hband hout hscale
  have hjcases : j=162 ∨ j=324 ∨ j=486 ∨ j=648 ∨ j=810 := by
    rcases hclass with ⟨ht2,hk,hmod⟩ | ⟨ht4,hk,hmod⟩ <;> omega
  have hz0 : z=z0_887 j := z0_eq_of_U j p U z hp hform hU
  have hroot : z∈roots := by
    rw [hz0]
    rcases hjcases with h|h|h|h|h
    · subst j; simp [roots]
    · subst j; simp [roots]
    · subst j; simp [roots]
    · subst j; simp [roots]
    · subst j; simp [roots]
  have hparent : ResetParent q z := Or.inr ⟨k,t,d,hdodd,hband.1,hband.2,hout,hscale⟩
  have hmem : q∈parentsFast z := (parentsFast_iff q z).2 hparent
  exact cone_excludes_root q (first_parent_mem_cone z q hroot hmem)

end CascadeUParentCone887
