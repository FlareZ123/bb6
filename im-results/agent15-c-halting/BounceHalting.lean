import BounceCalc
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- Infinite arithmetic seed family of all terminal even bounces. -/
def haltSeed (k : Nat) : Nat → Nat
  | 0 => 5
  | n+1 => haltSeed (2*k+4) n + (2*k+5)

theorem seed_lower (k n : Nat) : 5 ≤ haltSeed k n := by
  induction n generalizing k with
  | zero => simp [haltSeed]
  | succ n ih =>
      rw [haltSeed]
      have h := ih (2*k+4)
      omega

theorem seed_succ_large (k n : Nat) : 2*k+8 < haltSeed k (n+1) := by
  rw [haltSeed]
  have h := seed_lower (2*k+4) n
  omega

/-- Every arithmetic seed halts the exact bounce interpreter. -/
theorem seed_halts (k n : Nat) (hk : k%2=0) :
    (bounce k (haltSeed k n)).2 = none := by
  induction n generalizing k with
  | zero =>
      have he : ¬ k%2=1 := by omega
      simp [haltSeed, bounce, he]
  | succ n ih =>
      have he : ¬ k%2=1 := by omega
      have hn : ¬ haltSeed k (n+1) < 4 := by
        have h := seed_lower k (n+1)
        omega
      have h4 : haltSeed k (n+1) ≠ 4 := by
        have h := seed_lower k (n+1)
        omega
      have h5 : haltSeed k (n+1) ≠ 5 := by
        have h := seed_succ_large k n
        omega
      have hs : ¬ haltSeed k (n+1) ≤ 2*k+8 := by
        have h := seed_succ_large k n
        omega
      have hk' : (2*k+4)%2=0 := by omega
      have hi := ih (2*k+4) hk'
      rw [bounce]
      simp only [if_neg hn,if_neg he,if_neg h4,if_neg h5,if_neg hs]
      have hc : haltSeed k (n+1) - (2*k+5) = haltSeed (2*k+4) n := by
        rw [haltSeed]
        omega
      simp only [hc, hi]

theorem odd_bounce_nonhalt (c k : Nat) (hc : 4 ≤ c) (hk : k%2=1) :
    (bounce k c).2 ≠ none := by
  induction c using Nat.strongRecOn generalizing k with
  | ind c ih =>
      have hlow : ¬ c < 4 := by omega
      by_cases hs : c ≤ 2*k+6
      · rw [bounce]
        simp [hlow,hk,hs]
      · have hdec : c-(2*k+3) < c := by omega
        have hnew : 4 ≤ c-(2*k+3) := by omega
        have hk' : (2*k+3)%2=1 := by omega
        have hh := ih _ hdec (2*k+3) hnew hk'
        rw [bounce]
        simp only [if_neg hlow,if_pos hk,if_neg hs]
        exact hh

/-- Exact necessary condition for a halting even-middle bounce. -/
theorem even_bounce_halt_only_seed (c k : Nat) (hc : 4 ≤ c)
    (hk : k%2=0) (h : (bounce k c).2 = none) :
    ∃ n, c = haltSeed k n := by
  induction c using Nat.strongRecOn generalizing k with
  | ind c ih =>
      have hlow : ¬ c < 4 := by omega
      have he : ¬ k%2=1 := by omega
      by_cases h4 : c=4
      · subst c
        simp [bounce,he] at h
      · by_cases h5 : c=5
        · subst c
          exact ⟨0,rfl⟩
        · by_cases hs : c ≤ 2*k+8
          · rw [bounce] at h
            simp [hlow,he,h4,h5,hs] at h
          · have hdec : c-(2*k+5)<c := by omega
            have hnew : 4≤c-(2*k+5) := by omega
            have hk' : (2*k+4)%2=0 := by omega
            have hrec : (bounce (2*k+4) (c-(2*k+5))).2 = none := by
              have hh := h
              rw [bounce] at hh
              simpa only [if_neg hlow,if_neg he,if_neg h4,if_neg h5,if_neg hs] using hh
            obtain ⟨n,hn⟩ := ih _ hdec (2*k+4) hnew hk' hrec
            refine ⟨n+1, ?_⟩
            rw [haltSeed]
            omega

/-- The complete infinite halting family, for all bounce inputs of height at least four. -/
theorem bounce_halts_iff_seed (k c : Nat) (hc : 4 ≤ c) :
    (bounce k c).2 = none ↔ k%2=0 ∧ ∃ n, c=haltSeed k n := by
  constructor
  · intro h
    by_cases hk : k%2=0
    · exact ⟨hk,even_bounce_halt_only_seed c k hc hk h⟩
    · have hodd : k%2=1 := by omega
      exact False.elim ((odd_bounce_nonhalt c k hc hodd) h)
  · rintro ⟨hk,n,he⟩
    subst c
    exact seed_halts k n hk

/-- Exact dyadic closed form, expressed with nonnegative coefficients. -/
theorem seed_power_equation (k n : Nat) :
    haltSeed k n + 3*n + 2*(k+4) = 2^(n+1)*(k+4)+5 := by
  induction n generalizing k with
  | zero => simp [haltSeed] <;> omega
  | succ n ih =>
      rw [haltSeed]
      calc
        haltSeed (2*k+4) n + (2*k+5) + 3*(n+1) + 2*(k+4)
            = haltSeed (2*k+4) n + 3*n + 2*((2*k+4)+4) := by omega
        _ = 2^(n+1)*((2*k+4)+4)+5 := ih (2*k+4)
        _ = 2^((n+1)+1)*(k+4)+5 := by
          have heq : (2*k+4)+4=2*(k+4) := by omega
          rw [heq]
          calc
            2^(n+1)*(2*(k+4))+5 = (2^(n+1)*2)*(k+4)+5 :=
              congrArg (fun z : Nat => z+5) (Nat.mul_assoc (2^(n+1)) 2 (k+4)).symm
            _ = 2^((n+1)+1)*(k+4)+5 :=
              congrArg (fun z : Nat => z*(k+4)+5) (Nat.pow_succ 2 (n+1)).symm

/-- Equivalent scalar Diophantine halting condition, with no recursive seed. -/
theorem bounce_halts_iff_power (k c : Nat) (hc : 4 ≤ c) :
    (bounce k c).2 = none ↔
    k%2=0 ∧ ∃ n, c+3*n+2*(k+4)=2^(n+1)*(k+4)+5 := by
  rw [bounce_halts_iff_seed k c hc]
  constructor
  · rintro ⟨hk,n,rfl⟩
    exact ⟨hk,n,seed_power_equation k n⟩
  · rintro ⟨hk,n,h⟩
    have hseed := seed_power_equation k n
    exact ⟨hk,n,by omega⟩

#print axioms seed_power_equation
#print axioms bounce_halts_iff_power
#print axioms even_bounce_halt_only_seed
#print axioms bounce_halts_iff_seed
#print axioms seed_halts
#print axioms odd_bounce_nonhalt
end BB6.Agent15
