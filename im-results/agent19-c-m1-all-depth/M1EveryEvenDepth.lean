import M1AllDepth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19M1EveryEven
open BB6.Agent19M1
open BB6.Agent4Four

private theorem split_even_depth (r : Nat) (hr : 2≤r) (heven : r%2=0) :
    (∃ h, r=4*h+2) ∨ (∃ h, r=4*h+4) := by
  have hc : r%4=2 ∨ r%4=0 := by omega
  rcases hc with hc|hc
  · exact Or.inl ⟨(r-2)/4, by omega⟩
  · exact Or.inr ⟨(r-4)/4, by omega⟩

/-- For every even strict-image depth r>=2, there is a genuine m=1
    high stopping point excluded from every blank-section iterate. -/
theorem every_even_depth_has_unreachable_m1_stopping
    (r : Nat) (hr : 2≤r) (heven : r%2=0) :
    ∃ s t j k,
      j=4*s+2*r+2 ∧ k=bandY r t ∧
      k+j+8=16*(j+3) ∧
      ∀ time, BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
        some (2*j+3,k) := by
  rcases split_even_depth r hr heven with ⟨h,hh⟩|⟨h,hh⟩
  · have hx := a_x 0 h
    have hy := a_y 0 h
    have hs := ja_high_stop 0 h
    have hblank := ja_blank_unreachable 0 h
    refine ⟨sa 0 h,4,ja 0 h,15*ja 0 h+40,?_,?_,?_,?_⟩
    · omega
    · rw [hh]
      simpa using hy
    · simp only [show (2:Nat)^(2*1+2)=16 by decide] at hs
      omega
    · intro time
      exact hblank time
  · have hx := b_x 0 h
    have hy := b_y 0 h
    have hs := jb_high_stop 0 h
    have hblank := jb_blank_unreachable 0 h
    refine ⟨sb 0 h,13,jb 0 h,15*jb 0 h+40,?_,?_,?_,?_⟩
    · omega
    · rw [hh]
      simpa using hy
    · simp only [show (2:Nat)^(2*1+2)=16 by decide] at hs
      omega
    · intro time
      exact hblank time

#print axioms every_even_depth_has_unreachable_m1_stopping
end BB6.Agent19M1EveryEven
