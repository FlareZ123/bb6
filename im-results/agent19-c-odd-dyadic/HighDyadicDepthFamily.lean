import HighDyadicAllDepth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19AllDepth

/-- Explicit stopping-gate parameters, defined for every depth r>=2. -/
def depthM (r : Nat) : Nat := 2*r-1
def depthJ (r : Nat) : Nat := 3*2^(r+2)-(18*r+5)

private theorem scaled_linear_margin (n : Nat) :
    18*n+41≤48*2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have hp : 1≤(2:Nat)^n := Nat.pow_pos (by decide)
    omega

private theorem depth_linear_margin (r : Nat) (hr : 2≤r) :
    18*r+5≤3*2^(r+2) := by
  let n := r-2
  have he : r=n+2 := by dsimp [n]; omega
  rw [he]
  have hp : (2:Nat)^(n+2+2)=16*2^n := by
    have hf : n+2+2=n+4 := by omega
    rw [hf,Nat.pow_add]
    simp only [show (2:Nat)^4=16 by decide]
    omega
  rw [hp]
  have hm := scaled_linear_margin n
  omega

/-- Every depth >=2 supplies a closed-form high stopping residue
    satisfying all hypotheses of the source-certified dyadic cone. -/
theorem depth_family_parameters (r : Nat) (hr : 2≤r) :
    3≤depthM r ∧ r+4≤2*(depthM r)+2 ∧
    (depthM r)%4=(2*r+3)%4 ∧
    (depthJ r+9*(depthM r)+14)%2^(r+4)=3*2^(r+2) := by
  have hm : depthM r+1=2*r := by dsimp [depthM]; omega
  have hp := depth_linear_margin r hr
  have hj : depthJ r+18*r+5=3*2^(r+2) := by
    dsimp [depthJ]
    omega
  have hpow : (2:Nat)^(r+4)=4*2^(r+2) := by
    have he : r+4=(r+2)+2 := by omega
    rw [he,Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    omega
  have hpos : 0<(2:Nat)^(r+2) := Nat.pow_pos (by decide)
  have hlt : 3*2^(r+2)<2^(r+4) := by omega
  have hD : depthJ r+9*depthM r+14=3*2^(r+2) := by omega
  refine ⟨by omega,by omega,by omega,?_⟩
  rw [hD]
  exact Nat.mod_eq_of_lt hlt

/-- The defining parameters satisfy the exact source stopping
    dyadic residue equation before taking a modulus. -/
theorem depth_family_exact_sum (r : Nat) (hr : 2≤r) :
    depthJ r+9*depthM r+14=3*2^(r+2) := by
  have hm : depthM r+1=2*r := by dsimp [depthM]; omega
  have hp := depth_linear_margin r hr
  dsimp [depthJ]
  omega

/-- Different depths at least two necessarily give different m values. -/
theorem depthM_injective_on_two (r s : Nat)
    (hr : 2≤r) (hs : 2≤s)
    (he : depthM r=depthM s) : r=s := by
  dsimp [depthM] at he
  omega

/-- An explicit, genuinely infinite sequence of distinct high stopping
    target sectors is blank-unreachable in the authentic Machine C section. -/
theorem depth_family_no_blank (r : Nat) (hr : 2≤r) :
    ¬ BB6.Agent3.CReach (2*depthJ r+3)
      (2^(2*depthM r+2)*(depthJ r+3)-
        (depthJ r+3*depthM r+5)) := by
  obtain ⟨hm,hd,hm4,hpair⟩ := depth_family_parameters r hr
  exact high_depth_stopping_target_no_blank
    r (depthJ r) (depthM r) hr hm hd hm4 hpair

#print axioms depth_family_parameters
#print axioms depth_family_exact_sum
#print axioms depthM_injective_on_two
#print axioms depth_family_no_blank
end BB6.Agent19AllDepth
