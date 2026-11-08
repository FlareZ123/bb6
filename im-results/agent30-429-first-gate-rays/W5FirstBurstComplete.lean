import FirstGateRays
import BB429Burst
import Lean.Elab.Tactic.Omega

namespace BB429FirstGateRays

/-- Complete classification of right-five even-side J parameters whose
    *initial consecutive first-branch burst* ever lands exactly on the fatal
    gate. This theorem does not decide later non-first-branch continuations. -/
theorem even_exp_iff (k : Nat) :
    (∃ n, 2*3+(4*k+17)+3*n+13 = 4*((3+3)*2^n)) ↔
    (∃ m, k = evenK m) := by
  constructor
  · rintro ⟨n,hn⟩
    have hmod : n%4=0 := by omega
    have hn0 : n ≠ 0 := by
      intro hz
      subst n
      simp at hn
      omega
    have hge : 4 ≤ n := by omega
    let m : Nat := n/4-1
    have he : n = 4*(m+1) := by dsimp [m]; omega
    have hp := two_pow_ge (4*(m+1))
    have hk : k = evenK m := by
      rw [he] at hn
      dsimp [evenK]
      omega
    exact ⟨m,hk⟩
  · rintro ⟨m,rfl⟩
    refine ⟨4*(m+1), ?_⟩
    have ha := anc_formula 3 (4*(m+1)) (by omega)
    have he := evenK_anc m
    omega

/-- Complete classification for the odd-side right-five J endpoints.
    The first-branch fatal depth must equal 1 modulo 4. -/
theorem odd_exp_iff (k : Nat) :
    (∃ n, 2*11+(4*k+10)+3*n+13 = 4*((11+3)*2^n)) ↔
    (∃ m, k = oddK m) := by
  constructor
  · rintro ⟨n,hn⟩
    have hmod : n%4=1 := by omega
    let m : Nat := n/4
    have he : n = 4*m+1 := by dsimp [m]; omega
    have hp := two_pow_ge (4*m+1)
    have hk : k = oddK m := by
      rw [he] at hn
      dsimp [oddK]
      omega
    exact ⟨m,hk⟩
  · rintro ⟨m,rfl⟩
    refine ⟨4*m+1, ?_⟩
    have ha := anc_formula 11 (4*m+1) (by omega)
    have he := oddK_anc m
    omega

/-- Exact iff for any number of consecutive first-branch steps, including
    zero, from the even right-five boundary's canonical J return. -/
theorem even_firstburst_gateway_iff (k : Nat) :
    (∃ n a b, BB429Burst.firstRun n (3,4*k+17)=some (a,b) ∧ b+1=2*a) ↔
    (∃ m, k=evenK m) := by
  exact (BB429Burst.burst_gateway_iff 3 (4*k+17)).trans (even_exp_iff k)

/-- Exact iff for the odd boundary return; any seed not matching K_odd
    cannot reach the fatal line *before its first non-first branch*. -/
theorem odd_firstburst_gateway_iff (k : Nat) :
    (∃ n a b, BB429Burst.firstRun n (11,4*k+10)=some (a,b) ∧ b+1=2*a) ↔
    (∃ m, k=oddK m) := by
  exact (BB429Burst.burst_gateway_iff 11 (4*k+10)).trans (odd_exp_iff k)

#print axioms even_exp_iff
#print axioms odd_exp_iff
#print axioms even_firstburst_gateway_iff
#print axioms odd_firstburst_gateway_iff
end BB429FirstGateRays
