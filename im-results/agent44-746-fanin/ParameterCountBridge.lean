import OddGroup
import ExactCountLean
set_option maxHeartbeats 0
namespace CascadeAgent44

/-- In the nonterminal part of any exact 3-adic inverse, the original source
    odd reset parameter is exactly the dyadic geometric-band predicate. -/
theorem odd_param_band_iff (u n d t : Nat)
    (hd : d%2=1) (ht : t<n)
    (hz : 2*u+5 = 3^(n+1)*d) :
    OddParam u t ↔ BandOdd (geometricOddQ n d t) := by
  have hExp : n+1=(t+1)+(n-t) := by omega
  have hp : 3^(n+1)=3^(t+1)*3^(n-t) := by
    rw [hExp,Nat.pow_add]
  have hPow : 0 < 3^(t+1) := Nat.one_le_pow (t+1) 3 (by decide)
  have hodd : (3^(n-t)*d)%2=1 := by
    have hm : 3^(n-t)%2=1 := by
      induction n-t with
      | zero => decide
      | succ i ih => rw [Nat.pow_succ,Nat.mul_mod,ih]
    rw [Nat.mul_mod,hm,hd]
  have hq : 2*u+5=3^(t+1)*(3^(n-t)*d) := by
    rw [hz,hp]
    ac_rfl
  have hdiv : 3 ∣ geometricOddQ n d t := by
    have he:n-t=(n-t-1)+1 := by omega
    refine ⟨2^t*3^(n-t-1)*d,?_⟩
    dsimp [geometricOddQ]
    have hepow : 3^(n-t)=3^(n-t-1)*3 := by
      calc
        3^(n-t)=3^((n-t-1)+1) := congrArg (fun k:Nat => 3^k) he
        _ = 3^(n-t-1)*3 := Nat.pow_succ ..
    rw [hepow]
    ac_rfl
  constructor
  · rintro ⟨k,d',hd',hb,heq⟩
    have heq' : d'=3^(n-t)*d := by
      have hfactor : 3^(t+1)*d'=3^(t+1)*(3^(n-t)*d) := by
        rw [←heq,←hq]
      exact Nat.mul_left_cancel hPow hfactor
    have hq' : 2^t*d'=geometricOddQ n d t := by
      rw [heq']
      dsimp [geometricOddQ]
      ac_rfl
    have hgood : 1≤k := by
      by_cases hk : k=0
      · subst k
        simp at hb
        have hseven : geometricOddQ n d t=7 := by
          rw [←hq']
          omega
        have hm : geometricOddQ n d t %3=0 := Nat.mod_eq_zero_of_dvd hdiv
        rw [hseven] at hm
        omega
      · omega
    exact ⟨k,hgood,(by rw [←hq'];exact hb.1),(by rw [←hq'];exact hb.2)⟩
  · rintro ⟨k,hk,hlo,hhi⟩
    refine ⟨k,3^(n-t)*d,hodd,?_,hq⟩
    dsimp [geometricOddQ] at hlo hhi
    constructor
    · simpa only [Nat.mul_assoc] using hlo
    · simpa only [Nat.mul_assoc] using hhi

noncomputable def oddParameterCount (u n : Nat) : Nat :=
  (List.range n).countP (fun t => by
    classical
    exact decide (OddParam u t))

/-- Every nonterminal admissible source-C odd valuation is counted by the
    exact dyadic geometric band formula. No machine blank-root assumption. -/
theorem exact_nonterminal_odd_param_count (u n d : Nat) (hd : d%2=1)
    (hz : 2*u+5=3^(n+1)*d) :
    oddParameterCount u n + Nat.log2 (3^n*d) +
      (if 0<n ∧ d=1 then 1 else 0) = 2*n+Nat.log2 d := by
  classical
  have heq : oddParameterCount u n = geometricBandCount n d := by
    unfold oddParameterCount geometricBandCount
    apply List.countP_congr
    intro t ht
    have ht' : t<n := List.mem_range.mp ht
    have hiff := odd_param_band_iff u n d t hd ht' hz
    simpa [bandBool] using hiff
  rw [heq]
  exact geometric_band_count_identity n d hd

#print axioms odd_param_band_iff
#print axioms exact_nonterminal_odd_param_count
end CascadeAgent44
