import SectionHalting
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

private theorem seed_eq_iff (k c n : Nat) :
    c=haltSeed k n ↔ c+3*n+2*(k+4)=2^(n+1)*(k+4)+5 := by
  have hp := seed_power_equation k n
  constructor <;> intro h <;> omega

private theorem pow_shift (n : Nat) : 2^(n+4)=2^(n+1)*8 := by
  have he : n+4=(n+1)+3 := by omega
  rw [he, Nat.pow_add]

/-- Complete direct single-exponential arithmetic description of all
    two-counter section states on which Machine C immediately stops. -/
theorem section_halts_iff_diophantine (a k : Nat) :
    secNext (a,k) = none ↔
      (a=0 ∧ k=0) ∨
      (a=1 ∧ 4≤k ∧ ∃ n, 2*k+3*n+8=2^(n+4)) ∨
      (2≤a ∧ 1≤k ∧ a<2*k ∧ a%2=1 ∧
       ∃ n, 2*k+a+3*n+4=2^(n+1)*(a+3)) := by
  rw [section_halts_iff_seed]
  constructor
  · rintro (h0|h1|h2)
    · exact Or.inl h0
    · rcases h1 with ⟨ha,hk,n,hs⟩
      have hp := (seed_eq_iff 4 (2*k-3) n).mp hs
      have heq := pow_shift n
      exact Or.inr (Or.inl ⟨ha,hk,n,by omega⟩)
    · rcases h2 with ⟨ha,hk,hr,hodd,n,hs⟩
      have hp := (seed_eq_iff (a-1) (2*k-a+3) n).mp hs
      have heq : a-1+4=a+3 := by omega
      rw [heq] at hp
      exact Or.inr (Or.inr ⟨ha,hk,hr,hodd,n,by omega⟩)
  · rintro (h0|h1|h2)
    · exact Or.inl h0
    · rcases h1 with ⟨ha,hk,n,he⟩
      have hp := seed_power_equation 4 n
      have heq := pow_shift n
      have hs : 2*k-3=haltSeed 4 n := by omega
      exact Or.inr (Or.inl ⟨ha,hk,n,hs⟩)
    · rcases h2 with ⟨ha,hk,hr,hodd,n,he⟩
      have hp := seed_power_equation (a-1) n
      have heq : a-1+4=a+3 := by omega
      rw [heq] at hp
      have hs : 2*k-a+3=haltSeed (a-1) n := by omega
      exact Or.inr (Or.inr ⟨ha,hk,hr,hodd,n,hs⟩)

#print axioms section_halts_iff_diophantine
end BB6.Agent15
