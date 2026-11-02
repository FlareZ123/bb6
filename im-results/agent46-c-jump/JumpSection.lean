import JumpMacro
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- The first return from the dominant half-plane a>=2k, k>=1, is affine. -/
theorem section_dominant (a k : Nat) (hk : 1 ≤ k) (ha : 2*k ≤ a) :
    BB6.Agent8Section.run BB6CLine.nextC (2*k+1) (some (a,k,0)) =
      some (a-2*k,2*k+2,0) := by
  have hfirst : BB6CLine.nextC (a,k,0) = some (a-2,1,2*k+1) := by
    obtain ⟨u, rfl⟩ : ∃ u, a = u+2 := ⟨a-2,by omega⟩
    simp [BB6CLine.nextC]
  have hp : (2*k-2) ≤ a-2 := by omega
  have hc : (2*k-2)+3 ≤ 2*k+1 := by omega
  have hhigh := run_high (2*k-2) (a-2) 1 (2*k+1) hp hc
  have hsimp :
      some (a-2-(2*k-2),1+(2*k-2),(2*k+1)-(2*k-2)) =
        (some (a-2*k,2*k-1,3) : Option S) := by
    congr 1
    simp only [Prod.mk.injEq]
    omega
  rw [hsimp] at hhigh
  have hnum : 2*k+1 = 1+(2*k-2)+2 := by omega
  rw [hnum, BB6.Agent8Section.run_add]
  rw [BB6.Agent8Section.run_add]
  rw [BB6.Agent8Section.run_succ_head]
  have hfirstRun : BB6.Agent8Section.run BB6CLine.nextC 1 (some (a,k,0)) =
      some (a-2,1,2*k+1) := by simp [BB6.Agent8Section.run, hfirst]
  rw [hfirstRun]
  rw [← run_eq (2*k-2) (some (a-2,1,2*k+1))]
  rw [hhigh]
  simp [BB6.Agent8Section.run, BB6CLine.nextC] <;> omega

#print axioms section_dominant
end BB6.Agent46
