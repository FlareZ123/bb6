import Lean
import Lean.Elab.Tactic.Omega
import HighDyadicGateDecision

namespace BB6.Agent11FastDepthGate

/-- The exponent of two in a positive natural. We define v2 0 = 0;
    the application below only evaluates it at j+9*m+14 > 0. -/
def v2 : Nat → Nat
  | 0 => 0
  | n+1 => if (n+1)%2 = 0 then v2 ((n+1)/2) + 1 else 0
termination_by n => n
decreasing_by omega

theorem v2_two_mul (n : Nat) (hn : 0<n) : v2 (2*n) = v2 n + 1 := by
  let q := 2*n-1
  have hq : q+1=2*n := by dsimp [q]; omega
  have hmod : (q+1)%2=0 := by rw [hq]; omega
  have hdiv : (q+1)/2=n := by rw [hq]; omega
  rw [← hq]
  simp [v2, hmod, hdiv]

theorem v2_odd (n : Nat) (h : n%2=1) : v2 n = 0 := by
  let q := n-1
  have hq : q+1=n := by dsimp [q]; omega
  have hmod : (q+1)%2=1 := by rw [hq]; exact h
  rw [← hq]
  simp [v2, hmod]

theorem v2_pow_mul_odd (k q : Nat) (hq : q%2=1) :
    v2 (2^k*q) = k := by
  have hqpos : 0<q := by omega
  induction k with
  | zero =>
      simpa [v2] using v2_odd q hq
  | succ k ih =>
      have hpow : 2^(k+1)*q = 2*(2^k*q) := by
        simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      have hpos : 0<2^k*q :=
        Nat.mul_pos (Nat.pow_pos (by decide)) hqpos
      rw [hpow, v2_two_mul (2^k*q) hpos, ih]

abbrev gate (r j m : Nat) : Prop :=
  BB6.Agent11GateDecision.gate r j m

/-- The residue equation determines the exact 2-adic valuation. -/
theorem v2_of_high_residue (j m r : Nat)
    (h : (j+9*m+14)%2^(r+4)=3*2^(r+2)) :
    v2 (j+9*m+14) = r+2 := by
  let D := j+9*m+14
  let q := D / 2^(r+4)
  have hp : 2^(r+4) = 2^(r+2)*4 := by
    rw [show r+4=(r+2)+2 by omega, Nat.pow_add]
  have hmod := Nat.mod_add_div D (2^(r+4))
  rw [h] at hmod
  have hD : D = 2^(r+2)*(4*q+3) := by
    calc
      D = 3*2^(r+2) + 2^(r+4)*q := hmod.symm
      _ = 3*2^(r+2) + (2^(r+2)*4)*q := by rw [hp]
      _ = 2^(r+2)*(4*q+3) := by
        rw [Nat.mul_add]
        ac_rfl
  change v2 D = r+2
  rw [hD]
  apply v2_pow_mul_odd
  omega

def candidateDepth (j m : Nat) : Nat := v2 (j+9*m+14)

/-- One-depth executable test. If v2 is too small or exceeds the
    gate's forced bound, no admissible depth exists. Otherwise the
    only possible depth is v2(j+9*m+14)-2. -/
def candidateAllowedBool (j m : Nat) : Bool :=
  if 4≤candidateDepth j m ∧ candidateDepth j m≤2*m then
    decide (¬gate (candidateDepth j m-2) j m)
  else true

theorem candidateAllowedBool_iff (j m : Nat) :
    candidateAllowedBool j m = true ↔ ∀ r, ¬gate r j m := by
  unfold candidateAllowedBool
  let v := candidateDepth j m
  change (if 4≤v ∧ v≤2*m then decide (¬gate (v-2) j m) else true) = true
      ↔ ∀ r, ¬gate r j m
  by_cases hv : 4≤v ∧ v≤2*m
  · simp only [if_pos hv, decide_eq_true_eq]
    constructor
    · intro h r hr
      rcases hr with ⟨hrmin, hm, hrbound, hmres, hres⟩
      have hv2 := v2_of_high_residue j m r hres
      change v = r+2 at hv2
      have hrEq : r=v-2 := by omega
      subst r
      exact h ⟨hrmin, hm, hrbound, hmres, hres⟩
    · intro h hcand
      exact (h (v-2)) hcand
  · simp only [if_neg hv, true_iff]
    intro r hr
    rcases hr with ⟨hrmin, hm, hrbound, hmres, hres⟩
    have hv2 := v2_of_high_residue j m r hres
    change v = r+2 at hv2
    apply hv
    constructor
    · omega
    · omega

/-- The optimized test is extensionally identical to the previous
    bounded scan, so downstream users can replace it without changing
    the exact criterion. -/
theorem candidate_matches_scan (j m : Nat) :
    candidateAllowedBool j m =
      BB6.Agent11GateDecision.allowedBool j m := by
  apply Bool.eq_iff_iff.mpr
  rw [candidateAllowedBool_iff,
    BB6.Agent11GateDecision.allowedBool_iff]
  try rfl

#print axioms v2_of_high_residue
#print axioms candidateAllowedBool_iff
#print axioms candidate_matches_scan
end BB6.Agent11FastDepthGate
