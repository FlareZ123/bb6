import CSectionComputable
import SectionUnique
import SectionFirstReturn
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46CFirstReach
open BB6.Agent8Section BB6.Agent8TotalC BB6.Agent8ComputableC

/-- The bounded first-hit scanner and the recursive arithmetic Machine C
    section algorithm compute exactly the same successor for all counter pairs. -/
theorem fast_scanner_eq_arithmetic (p : Nat × Nat) :
    fastNext p = BB6.Agent46.secNext p := by
  have hinj : Function.Injective embed := by
    intro u v h
    rcases u with ⟨x,y⟩
    rcases v with ⟨x',y'⟩
    simp only [embed, Prod.mk.injEq] at h ⊢
    exact ⟨h.1,h.2.1⟩
  have hfirstFast : ∀ u j v, 1 ≤ j → j < fastTime u →
      run BB6CLine.nextC j (some (embed u)) ≠ some (embed v) := by
    intro u j v hj hlt heq
    have h := fastNext_first u j hj hlt
    rw [heq] at h
    simp [BB6.Agent8Scan.finish, decode, embed] at h
  have hfirstArith : ∀ u j v, 1 ≤ j → j < BB6.Agent46.secTime u →
      run BB6CLine.nextC j (some (embed u)) ≠ some (embed v) := by
    intro u j v hj hlt heq
    rcases u with ⟨a,k⟩
    rcases v with ⟨b,c⟩
    have hf := BB6.Agent15.section_no_early_c0 a k j (by omega) hlt b c
    apply hf
    simpa only [embed, BB6.Agent46.run_eq] using heq
  have hexactArith : ∀ u,
      run BB6CLine.nextC (BB6.Agent46.secTime u) (some (embed u)) =
        (BB6.Agent46.secNext u).map embed := by
    intro u
    rcases u with ⟨a,k⟩
    have hh := BB6.Agent46.section_exact a k
    have he : BB6.Agent46.embed0 = embed := by
      funext x
      rcases x with ⟨a,b⟩
      rfl
    rw [he] at hh
    simpa only [BB6.Agent46.run_eq, embed] using hh
  exact BB6.Agent46SectionReach.unique_first_section
    BB6CLine.nextC embed fastTime fastNext hinj
    BB6.Agent46.secTime BB6.Agent46.secNext
    (fun u => (fastTime_bounds u).1)
    (fun u => by rcases u with ⟨a,k⟩; exact BB6.Agent46.sec_positive a k)
    fastNext_exact hexactArith hfirstFast hfirstArith p

#print axioms fast_scanner_eq_arithmetic
end BB6.Agent46CFirstReach
