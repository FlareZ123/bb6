import RayDepthResidue
import ParameterCountBridge

set_option maxHeartbeats 0

namespace CascadeSelectedGateRayCount

open CascadeRayPeriod CascadeRayDepthHensel CascadeRayDepthResidue CascadeAgent44

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
      decide
  have hodd : (2*u+5)%2=1 := by omega
  have hdodd : d%2=1 := by
    rw [hd, Nat.mul_mod, hthree (k+1)] at hodd
    omega
  refine ⟨d, hdodd, hd, ?_⟩
  exact exact_nonterminal_odd_param_count u k d hdodd hd

#print axioms selected_ray_exact_nonterminal_count
end CascadeSelectedGateRayCount
