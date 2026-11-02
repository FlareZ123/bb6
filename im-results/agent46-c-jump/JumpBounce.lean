import JumpSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

private theorem high_odd_bounce (k c : Nat) (hk : k%2=1) (hc : 4≤c) :
    BB6CLine.nextC (0,k,c) = some (2*k+3,0,c) := by
  obtain ⟨d, rfl⟩ : ∃ d, c=d+4 := ⟨c-4,by omega⟩
  change (if k%2=0 then some (4*(k/2)+2,2,d+1)
      else some (4*(k/2)+5,0,d+4)) = some (2*k+3,0,d+4)
  have hne : k%2≠0 := by omega
  have hdiv : k%2 + 2*(k/2) = k := Nat.mod_add_div k 2
  simp only [hne, ite_false, Option.some.injEq, Prod.mk.injEq]
  constructor
  · omega
  · trivial

private theorem high_even_bounce (k c : Nat) (hk : k%2=0) (hc : 4≤c) :
    BB6CLine.nextC (0,k,c) = some (2*k+2,2,c-3) := by
  obtain ⟨d, rfl⟩ : ∃ d, c=d+4 := ⟨c-4,by omega⟩
  change (if k%2=0 then some (4*(k/2)+2,2,d+1)
      else some (4*(k/2)+5,0,d+4)) = some (2*k+2,2,(d+4)-3)
  have hdiv : k%2 + 2*(k/2) = k := Nat.mod_add_div k 2
  simp only [hk, ite_true, Option.some.injEq, Prod.mk.injEq]
  constructor
  · omega
  · constructor
    · trivial
    · omega

theorem odd_bounce_to_three (k c : Nat) (hk : k%2=1)
    (hc : 4≤c) (hbound : c-3≤2*k+3) :
    run (1+(c-3)) (some (0,k,c)) = some (2*k+3-(c-3),c-3,3) := by
  have hfirst := high_odd_bounce k c hk hc
  have hnum : 1+(c-3) = (c-3)+1 := by omega
  rw [hnum]
  change run (c-3) ((some (0,k,c)).bind BB6CLine.nextC) = _
  simp only [Option.bind_some, hfirst]
  have hh := run_high (c-3) (2*k+3) 0 c hbound (by omega)
  rw [hh]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · constructor
    · omega
    · omega

theorem even_bounce_to_three (k c : Nat) (hk : k%2=0)
    (hc : 6≤c) (hbound : c-6≤2*k+2) :
    run (1+(c-6)) (some (0,k,c)) = some (2*k+2-(c-6),2+(c-6),3) := by
  have hfirst := high_even_bounce k c hk (by omega)
  have hnum : 1+(c-6)=(c-6)+1 := by omega
  rw [hnum]
  change run (c-6) ((some (0,k,c)).bind BB6CLine.nextC) = _
  simp only [Option.bind_some, hfirst]
  have hh := run_high (c-6) (2*k+2) 2 (c-3) hbound (by omega)
  rw [hh]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · constructor
    · trivial
    · omega

#print axioms odd_bounce_to_three
#print axioms even_bounce_to_three
end BB6.Agent46
