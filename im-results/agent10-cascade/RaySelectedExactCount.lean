import RayDepthResidue
import ParameterCountBridge

set_option maxHeartbeats 0

namespace CascadeSelectedGateRayCount

open CascadeRayPeriod CascadeRayDepthHensel CascadeRayDepthResidue CascadeAgent44

/-- Elementary dyadic domination for a linear input at depth j. -/
private theorem linear_big_pow (j : Nat) :
    8*j+51 ≤ 2^(3*j+24) := by
  induction j with
  | zero => decide
  | succ j ih =>
      have he : 3*(j+1)+24 = 3*j+24+3 := by omega
      rw [he, Nat.pow_add]
      have h8 : (2:Nat)^3=8 := by decide
      rw [h8]
      omega

/-- The linear source coefficient remains below the growing dyadic
    budget after arbitrary additional n-index increments. -/
private theorem linear_growth_budget (j r : Nat) :
    2*(4*j+24+r)+3 ≤ 2^(3*j+24+r) := by
  induction r with
  | zero =>
      have h := linear_big_pow j
      simpa only [Nat.add_zero] using
        (show 2*(4*j+24)+3 ≤ 2^(3*j+24) by omega)
  | succ r ih =>
      have he : 3*j+24+(r+1) = (3*j+24+r)+1 := by omega
      rw [he, Nat.pow_succ]
      omega

/-- Every n≥4j+24 has enough binary width for the exact ray deficit
    numerator coefficient at depth j. -/
private theorem physical_pow_budget (n j : Nat)
    (hn : 4*j+24 ≤ n) :
    2^j*(2*n+3) ≤ 2^n := by
  let r := n-(4*j+24)
  have hindex : n = 4*j+24+r := by dsimp [r]; omega
  have hlin : 2*n+3 ≤ 2^(3*j+24+r) := by
    rw [hindex]
    exact linear_growth_budget j r
  have hmul := Nat.mul_le_mul_left (2^j) hlin
  have hsum : j+(3*j+24+r)=n := by rw [hindex]; omega
  have hpow : 2^j*2^(3*j+24+r)=2^n := by
    rw [←Nat.pow_add, hsum]
  omega

/-- Universal all-index physical-power budget for the unique selected
    Hensel ray depth at every 3-adic precision. Unlike a brute-force
    finite-depth census this is a fully quantified n,k theorem. -/
theorem depth_selected_physical_pow_budget
    (n k : Nat)
    (hn : 100*3^(k+1) ≤ n) :
    2^(depthResidue n k)*(2*n+3) ≤ 2^n := by
  let j := depthResidue n k
  have hj : j < 2*3^k := by
    simpa only [j, depthPeriod] using depthResidue_lt n k
  have hpos : 1 ≤ 3^k := Nat.one_le_pow k 3 (by decide)
  have hpow : 3^(k+1)=3*3^k := by rw [Nat.pow_succ]; omega
  rw [hpow] at hn
  have hbudget : 4*j+24 ≤ n := by omega
  exact physical_pow_budget n j hbudget

/-- The selected all-precision Hensel ray residue has an exact
    source-valid odd-reset parameter count whenever its signed
    numerator is the genuine nonnegative source-C output numerator.
    No hypothesis on maximal odd valuation is needed, and the
    terminal d=1 correction is retained. -/
theorem selected_ray_exact_nonterminal_count
    (n k u : Nat)
    (hsector : n % 6 = 4 ∨ n % 6 = 5)
    (hphysical : signedZ n (depthResidue n k) = (2*u+5 : Int)) :
    ∃ d : Nat, d % 2 = 1 ∧
      2*u+5 = 3^(k+1)*d ∧
      oddParameterCount u k + Nat.log2 (3^k*d) +
        (if 0<k ∧ d=1 then 1 else 0) =
          2*k+Nat.log2 d := by
  have hsmall : depthResidue n k < depthPeriod k :=
    depthResidue_lt n k
  have hmod : depthResidue n k % depthPeriod k =
      depthResidue n k := Nat.mod_eq_of_lt hsmall
  have hdivI : (3 : Int)^(k+1) ∣ signedZ n (depthResidue n k) :=
    (depthResidue_iff n k (depthResidue n k) hsector).mpr hmod
  rw [hphysical] at hdivI
  have hdivN : 3^(k+1) ∣ 2*u+5 := by
    exact_mod_cast hdivI
  obtain ⟨d, hd⟩ := hdivN
  have hthree : ∀e : Nat, 3^e % 2 = 1 := by
    intro e
    induction e with
    | zero => decide
    | succ e ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]
  have hodd : (2*u+5)%2=1 := by omega
  have hdodd : d%2=1 := by
    rw [hd, Nat.mul_mod, hthree (k+1)] at hodd
    omega
  refine ⟨d, hdodd, hd, ?_⟩
  exact exact_nonterminal_odd_param_count u k d hdodd hd

#print axioms depth_selected_physical_pow_budget
#print axioms selected_ray_exact_nonterminal_count
end CascadeSelectedGateRayCount
