import Agent46CBridge
import SectionPower
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- A deterministic option-valued section eventually stops exactly when
    one successfully visited section state has an immediate stopping edge. -/
theorem run_none_iff_guard {α : Type} (f : α → Option α) (start : α) :
    (∃ m, BB6.Agent8Section.run f m (some start)=none) ↔
    (∃ m s, BB6.Agent8Section.run f m (some start)=some s ∧ f s=none) := by
  constructor
  · rintro ⟨m,hm⟩
    have aux : ∀ m, BB6.Agent8Section.run f m (some start)=none →
        ∃ n s, BB6.Agent8Section.run f n (some start)=some s ∧ f s=none := by
      intro j
      induction j with
      | zero =>
          intro hh
          simp [BB6.Agent8Section.run] at hh
      | succ j ih =>
          intro hh
          cases hp : BB6.Agent8Section.run f j (some start) with
          | none => exact ih hp
          | some s =>
              refine ⟨j,s,hp,?_⟩
              simpa [BB6.Agent8Section.run,hp] using hh
    exact aux m hm
  · rintro ⟨m,s,hs,hstop⟩
    refine ⟨m+1,?_⟩
    simp [BB6.Agent8Section.run,hs,hstop]

/-- Complete blank-origin halt gateway for Machine C, in explicit
    single-exponential Diophantine form and source-certified semantics. -/
theorem blank_halts_iff_diophantine_gateway :
    BB6.CReachBridge.RunHalts ↔
      ∃ m a k, BB6.Agent8Section.run secNext m (some (5,1))=some (a,k) ∧
        ((a=0 ∧ k=0) ∨
         (a=1 ∧ 4≤k ∧ ∃ n, 2*k+3*n+8=2^(n+4)) ∨
         (2≤a ∧ 1≤k ∧ a<2*k ∧ a%2=1 ∧
          ∃ n, 2*k+a+3*n+4=2^(n+1)*(a+3))) := by
  rw [blank_halts_iff_arithmetic]
  constructor
  · rintro ⟨m,hm⟩
    obtain ⟨j,s,hs,ht⟩ := (run_none_iff_guard secNext (5,1)).mp ⟨m,hm⟩
    rcases s with ⟨a,k⟩
    exact ⟨j,a,k,hs,(section_halts_iff_diophantine a k).mp ht⟩
  · rintro ⟨m,a,k,hs,hguard⟩
    have hstop := (section_halts_iff_diophantine a k).mpr hguard
    exact (run_none_iff_guard secNext (5,1)).mpr ⟨m,(a,k),hs,hstop⟩

#print axioms run_none_iff_guard
#print axioms blank_halts_iff_diophantine_gateway
end BB6.Agent15
