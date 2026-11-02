import OddDepthResidue
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11
open BB6.Agent15

/-- Eight concrete B8/M32 quotient cylinders, experimentally absent but
    requiring a full original-source finite quotient certificate.
    The theorem below has their nonreachability as an EXPLICIT hypothesis. -/
def m32Cylinder (x y : Nat) : Prop :=
    (x%32=27 ∧ y%32=28) ∨
    (x%32=19 ∧ y%32=16) ∨
    (x%32=3 ∧ y%32=20) ∨
    (x%32=11 ∧ y%32=0) ∨
    (x%32=3 ∧ y%32=16) ∨
    (x%32=11 ∧ y%32=12) ∨
    (x%32=19 ∧ y%32=4) ∨
    (x%32=27 ∧ y%32=0)

/-- The exact eight modulo-8 2-adic depth/odd-part parameter types
    that normalize into one of the experimental M32 forbidden cells. -/
def m32DepthClass (d q : Nat) : Prop :=
    (d%8=1 ∧ (q%8=7 ∨ q%8=4)) ∨
    (d%8=3 ∧ (q%8=5 ∨ q%8=0)) ∨
    (d%8=5 ∧ (q%8=4 ∨ q%8=3)) ∨
    (d%8=7 ∧ (q%8=1 ∨ q%8=0))

/-- A uniform all-depth conditional C nonreachability theorem:
    once the source-checked M32 cylinders are available, it instantly
    excludes the eight arithmetic inverse classes at arbitrary depths. -/
theorem m32_odd_depth_reach_barrier
    (hcyl : ∀ x y : Nat, m32Cylinder x y → ¬ CReach x y)
    (a d q : Nat)
    (ha : a%4=3) (hq : 1≤q)
    (hmass : (a+2*(2^(d+1)*(2*q+1)-2))%32=23)
    (hclass : m32DepthClass d q) :
    ¬ CReach a (2^(d+1)*(2*q+1)-2) := by
  intro hreach
  let k := 2^(d+1)*(2*q+1)-2
  let p := affineNormalize a k
  have hn := odd_term_normalized_residue a d q ha hq hmass
  change p.2 = 4*q ∧ (p.1+8*q+4*d)%32=23 at hn
  obtain ⟨hp2,hm⟩ := hn
  have hcell : m32Cylinder p.1 p.2 := by
    unfold m32Cylinder m32DepthClass at *
    rcases hclass with ⟨hd,hq⟩ | ⟨hd,hq⟩ | ⟨hd,hq⟩ | ⟨hd,hq⟩
    all_goals rcases hq with hq|hq <;> omega
  have hreachnorm := (reach_iff_normalize a k).mp hreach
  exact hcyl p.1 p.2 hcell hreachnorm

#print axioms m32_odd_depth_reach_barrier
end BB6.Agent11
