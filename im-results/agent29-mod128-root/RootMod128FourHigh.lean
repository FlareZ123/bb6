import RootMod128High
import RootMod128FourSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29New

/-- All-natural arithmetic bridge from original high-stopping equation
into the new four-link authentic-root forbidden cylinder. -/
theorem high_four_cylinder (j m k : Nat)
    (hm : 4≤m) (hj : j%64=57)
    (hres : (j+31)%128=(3*m)%128)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%128=117 ∧ (2*j+3+k+1)%128=96 ∧ 106≤k := by
  have hpowdiv : 128 ∣ 2^(2*m+2) := by
    change 2^7 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨q,hq⟩ := hpowdiv
  have hdiv : 128 ∣ k+j+3*m+5 := by
    refine ⟨q*(j+3), ?_⟩
    calc
      k+j+3*m+5 = 2^(2*m+2)*(j+3) := hgate
      _ = (128*q)*(j+3) := by rw [hq]
      _ = 128*(q*(j+3)) := by ac_rfl
  have hhmod : (k+j+3*m+5)%128=0 := Nat.mod_eq_zero_of_dvd hdiv
  have hlow : 4*m+4 ≤ 2^(2*m+2) := power_linear_bound m
  have hp1 : 1≤2^(2*m+2) := by omega
  have hmul : j ≤ 2^(2*m+2)*j := by
    have hh := Nat.mul_le_mul_right j hp1
    simpa using hh
  have hdist : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add, Nat.mul_comm]
  constructor
  · omega
  constructor
  · omega
  · omega

theorem blank_no_high_stop_four (j m k : Nat)
    (hm : 4≤m) (hj : j%64=57)
    (hres : (j+31)%128=(3*m)%128)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨hx,hs,hy⟩ := high_four_cylinder j m k hm hj hres hgate
  exact blank_no_four_link (2*j+3) k hx hs hy

#print axioms high_four_cylinder
#print axioms blank_no_high_stop_four
end BB6.Agent29New
