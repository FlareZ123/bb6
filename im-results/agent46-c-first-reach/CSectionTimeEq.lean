import CSectionCoincidence
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46CFirstReach
open BB6.Agent8Section BB6.Agent8TotalC BB6.Agent8ComputableC

/-- The bounded scanner and recursive arithmetic section use exactly the
    same count of original CLine transitions on every successful return. -/
theorem fastTime_eq_secTime_of_some (p q : Nat × Nat)
    (h : BB6.Agent46.secNext p = some q) :
    fastTime p = BB6.Agent46.secTime p := by
  have hg : fastNext p = some q := by
    rw [fast_scanner_eq_arithmetic]
    exact h
  have hexactFast : run BB6CLine.nextC (fastTime p) (some (embed p)) =
      some (embed q) := by
    simpa [hg] using fastNext_exact p
  have hsec := BB6.Agent46.section_exact p.1 p.2
  have hemb : BB6.Agent46.embed0 = embed := by
    funext x
    rcases x with ⟨a,k⟩
    rfl
  rw [hemb] at hsec
  have hexactSec : run BB6CLine.nextC (BB6.Agent46.secTime p) (some (embed p)) =
      some (embed q) := by
    rcases p with ⟨a,k⟩
    simpa [BB6.Agent46.run_eq,embed,h] using hsec
  by_cases hlt : fastTime p < BB6.Agent46.secTime p
  · rcases p with ⟨a,k⟩
    rcases q with ⟨b,c⟩
    have hf := BB6.Agent15.section_no_early_c0 a k (fastTime (a,k))
      (by have hh := (fastTime_bounds (a,k)).1; omega) hlt b c
    have hr : BB6.Agent46.run (fastTime (a,k)) (some (a,k,0)) =
        some (b,c,0) := by
      rw [BB6.Agent46.run_eq]
      simpa [embed] using hexactFast
    exact False.elim (hf hr)
  · by_cases hlt2 : BB6.Agent46.secTime p < fastTime p
    · have hf := fastNext_first p (BB6.Agent46.secTime p)
        (by rcases p with ⟨a,k⟩; exact BB6.Agent46.sec_positive a k) hlt2
      rw [hexactSec] at hf
      simp [BB6.Agent8Scan.finish,decode,embed] at hf
    · omega

#print axioms fastTime_eq_secTime_of_some
end BB6.Agent46CFirstReach
