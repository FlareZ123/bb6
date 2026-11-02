import BounceParity
import Lean.Elab.Tactic.Omega
namespace BB6.Agent49
open BB6.Agent46 (bounce)
theorem small_section_bounce_gate (a k : Nat)
    (ha : 2≤a) (hsmall : a<2*k) :
    ((bounce (a-1) (2*k-a+3)).2=none ↔
      a%2=1 ∧ ∃ n : Nat, 2*k+a+4+3*n=(a+3)*2^(n+1)) := by
  have hc : 4≤2*k-a+3 := by omega
  rw [bounce_power_criterion (a-1) (2*k-a+3) hc]
  constructor
  · rintro ⟨he,n,hn⟩
    have hp : a%2=1 := by omega
    refine ⟨hp,n,?_⟩
    have heq : a-1+4=a+3 := by omega
    rw [heq] at hn
    omega
  · rintro ⟨hp,n,hn⟩
    have he : (a-1)%2=0 := by omega
    refine ⟨he,n,?_⟩
    have heq : a-1+4=a+3 := by omega
    rw [heq]
    omega
theorem even_small_section_bounce_survives (a k : Nat)
    (ha : 2≤a) (he : a%2=0) (hsmall : a<2*k) :
    (bounce (a-1) (2*k-a+3)).2 ≠ none := by
  intro hh
  have hcrit := (small_section_bounce_gate a k ha hsmall).mp hh
  omega
#print axioms small_section_bounce_gate
#print axioms even_small_section_bounce_survives
end BB6.Agent49
