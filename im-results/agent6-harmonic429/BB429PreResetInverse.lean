import BB429InverseKernel16
import Lean.Elab.Tactic.Omega

namespace BB429PreResetInverse

open BB429Kernel16
open BB429NewResidue

/-- The branch-10 pre-reset first coordinate at burst length 35. -/
def branch10N35X (d : Nat) : Nat :=
  (2^37*(d+6)+2*d-126)/4

/-- The source-derived branch-10 pre-reset state, with n = 35. -/
def branch10N35PreReset (d : Nat) : Nat × Nat :=
  let x := branch10N35X d
  (x, 2*(x-d)+1)

/-- The affine inverse-kernel family for d = d0 + 64*q. -/
def branch10N35Family (d0 : Nat) : Affine :=
  let x := branch10N35X d0
  ⟨2199023255584, x, 4398046511040, 2*(x-d0)+1⟩

/-- Exact parametrization of the branch-10 pre-reset line. -/
theorem branch10N35_param (d0 q : Nat) (hd0 : 5≤d0) (hodd : d0%2=1) :
    branch10N35PreReset (d0+64*q) =
      (va (branch10N35Family d0) q, vb (branch10N35Family d0) q) := by
  simp [branch10N35PreReset, branch10N35Family, branch10N35X, va, vb]
  omega

/-- The inverse kernel certifies eight of the twelve mod-64 classes left by
    the branch-10 mod-16 sieve, at n = 35. -/
theorem branch10N35_cert (d0 : Nat)
    (hd0 : d0=65 ∨ d0=5 ∨ d0=9 ∨ d0=21 ∨
           d0=25 ∨ d0=37 ∨ d0=49 ∨ d0=53) :
    cert 60 (branch10N35Family d0) = true := by
  rcases hd0 with h|h|h|h|h|h|h|h <;> subst d0 <;> decide

/-- Every member of each certified affine family is outside the blank-root
    orbit. This is an all-q theorem, not a finite simulation. -/
theorem branch10N35_family_no_reach (d0 q : Nat)
    (hd0 : d0=65 ∨ d0=5 ∨ d0=9 ∨ d0=21 ∨
           d0=25 ∨ d0=37 ∨ d0=49 ∨ d0=53) :
    ¬ Reach (va (branch10N35Family d0) q)
            (vb (branch10N35Family d0) q) := by
  exact cert_sound 60 (branch10N35Family d0) q (branch10N35_cert d0 hd0)

/-- Reassemble an arithmetic-progression parameter from a mod-64 residue. -/
private theorem residue_rep (d d0 : Nat) (hd : d0≤d)
    (hm : d%64=d0%64) : ∃ q, d=d0+64*q := by
  refine ⟨(d-d0)/64, ?_⟩
  have hrem : (d-d0)%64=0 := by omega
  have hdiv := Nat.mod_add_div (d-d0) 64
  omega

/-- Eight infinite d-progressions in the n=35 branch-10 pre-reset family
    are formally excluded. The four surviving mod-64 residues are
    17, 33, 41, and 57. -/
theorem branch10N35_preReset_no_reach_of_residue (d : Nat)
    (hd : 3≤d)
    (hres : d%64=1 ∨ d%64=5 ∨ d%64=9 ∨ d%64=21 ∨
            d%64=25 ∨ d%64=37 ∨ d%64=49 ∨ d%64=53) :
    ¬ Reach (branch10N35PreReset d).1 (branch10N35PreReset d).2 := by
  rcases hres with h|h|h|h|h|h|h|h
  · have h65 : 65≤d := by omega
    obtain ⟨q,hq⟩ := residue_rep d 65 h65 (by omega)
    rw [hq, branch10N35_param 65 q (by omega) (by omega)]
    exact branch10N35_family_no_reach 65 q (by omega)
  · have h5 : 5≤d := by omega
    obtain ⟨q,hq⟩ := residue_rep d 5 h5 (by omega)
    rw [hq, branch10N35_param 5 q (by omega) (by omega)]
    exact branch10N35_family_no_reach 5 q (by omega)
  · have h9 : 9≤d := by omega
    obtain ⟨q,hq⟩ := residue_rep d 9 h9 (by omega)
    rw [hq, branch10N35_param 9 q (by omega) (by omega)]
    exact branch10N35_family_no_reach 9 q (by omega)
  · have h21 : 21≤d := by omega
    obtain ⟨q,hq⟩ := residue_rep d 21 h21 (by omega)
    rw [hq, branch10N35_param 21 q (by omega) (by omega)]
    exact branch10N35_family_no_reach 21 q (by omega)
  · have h25 : 25≤d := by omega
    obtain ⟨q,hq⟩ := residue_rep d 25 h25 (by omega)
    rw [hq, branch10N35_param 25 q (by omega) (by omega)]
    exact branch10N35_family_no_reach 25 q (by omega)
  · have h37 : 37≤d := by omega
    obtain ⟨q,hq⟩ := residue_rep d 37 h37 (by omega)
    rw [hq, branch10N35_param 37 q (by omega) (by omega)]
    exact branch10N35_family_no_reach 37 q (by omega)
  · have h49 : 49≤d := by omega
    obtain ⟨q,hq⟩ := residue_rep d 49 h49 (by omega)
    rw [hq, branch10N35_param 49 q (by omega) (by omega)]
    exact branch10N35_family_no_reach 49 q (by omega)
  · have h53 : 53≤d := by omega
    obtain ⟨q,hq⟩ := residue_rep d 53 h53 (by omega)
    rw [hq, branch10N35_param 53 q (by omega) (by omega)]
    exact branch10N35_family_no_reach 53 q (by omega)

#print axioms branch10N35_preReset_no_reach_of_residue

end BB429PreResetInverse
