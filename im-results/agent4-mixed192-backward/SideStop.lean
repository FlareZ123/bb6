import WideStop
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace A4Mixed192Side

private theorem halt_k_ge4 (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) : 4≤k := by
  have hpower : 3*m+9≤2^(2*m+2) := BB6.Agent46.pow_bound m (by omega)
  have hpositive : 1≤2^(2*m+2) := by omega
  have hjmul : j≤2^(2*m+2)*j := by
    simpa using Nat.mul_le_mul_right j hpositive
  have hprod : 2^(2*m+2)*(j+3) =
      2^(2*m+2)*j + 3*2^(2*m+2) := by
    simp [Nat.mul_add, Nat.mul_comm]
  rw [hprod] at heq
  omega

/-- 48 more residue pairs modulo 192 excluded by the high A invariant. -/
theorem side_A_j43_m11_excluded (j m k : Nat)
    (hj : j%48=43) (hm : m%16=11)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  intro hr
  have hm2 : 2≤m := by omega
  have hk := halt_k_ge4 j m k hm2 heq
  have hmod := A4Mixed192Stops.high_halt_mod192 j m k hm2 heq
  have hp := BB6.Agent46.reach_c0_two_parent (2*j+3) k hk hr
  have hg : A4Backward192.high (2*j+3) (k-3) 3 := by
    simp only [A4Backward192.high]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))))))
  have hn := A4Backward192.source_blank_never_bad192 (2*j+3,k-3,3) hp
  apply hn
  simpa [A4Backward192.bad] using hg


/-- 48 more residue pairs modulo 192 excluded by the high B invariant. -/
theorem side_B_j19_m3_excluded (j m k : Nat)
    (hj : j%48=19) (hm : m%16=3)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  intro hr
  have hm2 : 2≤m := by omega
  have hk := halt_k_ge4 j m k hm2 heq
  have hmod := A4Mixed192Stops.high_halt_mod192 j m k hm2 heq
  have hp := BB6.Agent46.reach_c0_two_parent (2*j+3) k hk hr
  have hg : A4Backward192B.high (2*j+3) (k-3) 3 := by
    simp only [A4Backward192B.high]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))
  have hn := A4Backward192B.source_blank_never_bad192B (2*j+3,k-3,3) hp
  apply hn
  simpa [A4Backward192B.bad] using hg


#print axioms side_A_j43_m11_excluded
#print axioms side_B_j19_m3_excluded

/-- Complete modular description of 504 parameter cells modulo192
whose second-family halting gateway is excluded by the two mixed192 cores. -/
theorem second_stop_504_mod192_excluded (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hres :
       (j%12=4 ∧ m%8=4) ∨
       (j%48=43 ∧ m%16=11) ∨
       (j%48=19 ∧ m%16=3) ∨
       ((j%192=16 ∧ m%64=58) ∨
        (j%192=112 ∧ m%64=26) ∨
        (j%192=64 ∧ m%64=10) ∨
        (j%192=160 ∧ m%64=42)) ∨
       ((j%192=40 ∧ m%64=2) ∨
        (j%192=136 ∧ m%64=34) ∨
        (j%192=88 ∧ m%64=18) ∨
        (j%192=184 ∧ m%64=50))) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  rcases hres with hwide | hsa | hsb | ha | hb
  · exact A4Mixed192Wide.second_stop_j4_mod12_m4_mod8_excluded
      j m k hwide.1 hwide.2 heq
  · exact side_A_j43_m11_excluded j m k hsa.1 hsa.2 heq
  · exact side_B_j19_m3_excluded j m k hsb.1 hsb.2 heq
  · exact A4Mixed192Stops.first_core_stops j m k hm heq ha
  · exact A4Mixed192Stops.second_core_stops j m k hm heq hb

#print axioms second_stop_504_mod192_excluded
end A4Mixed192Side
