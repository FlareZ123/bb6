import M3FourSeeds
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19M3EveryOdd
open BB6.Agent19OddTower
open BB6.Agent4Four

private theorem split_odd_depth (r : Nat) (hr : 5≤r) (hodd : r%2=1) :
    (∃ h, r=5+8*h) ∨ (∃ h, r=7+8*h) ∨
    (∃ h, r=9+8*h) ∨ (∃ h, r=11+8*h) := by
  have hc : r%8=5 ∨ r%8=7 ∨ r%8=1 ∨ r%8=3 := by omega
  rcases hc with hc|hc|hc|hc
  · exact Or.inl ⟨(r-5)/8, by omega⟩
  · exact Or.inr (Or.inl ⟨(r-7)/8, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(r-9)/8, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(r-11)/8, by omega⟩))

private theorem package (r0 s0 t h : Nat)
    (hs : K 3 r0 t h+J 3 r0 s0 t h+3*3+5=
      (2:Nat)^(2*3+2)*(J 3 r0 s0 t h+3)) :
    ∃ s t' j k,
      j=4*s+2*R 3 r0 h+2 ∧
      k=bandY (R 3 r0 h) t' ∧
      k+j+14=256*(j+3) ∧
      ∀ time, BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
        some (2*j+3,k) := by
  refine ⟨S 3 r0 s0 t h,t,J 3 r0 s0 t h,K 3 r0 t h, rfl,rfl,?_,?_⟩
  · simpa only [show (2:Nat)^(2*3+2)=256 by decide,
      show 3*3+5=14 by decide] using hs
  · intro time
    exact tower_blank_excluded _ _ _ _ _ _

/-- For every odd strict image depth r>=5, at least one genuine m=3
    high-stopping point lies in the permanently blank-unreachable cylinder. -/
theorem every_odd_depth_has_unreachable_m3_stopping
    (r : Nat) (hr : 5≤r) (hodd : r%2=1) :
    ∃ s t j k,
      j=4*s+2*r+2 ∧ k=bandY r t ∧
      k+j+14=256*(j+3) ∧
      ∀ time, BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
        some (2*j+3,k) := by
  rcases split_odd_depth r hr hodd with
    ⟨h,he⟩|⟨h,he⟩|⟨h,he⟩|⟨h,he⟩
  · have heq : r=R 3 5 h := by dsimp [R]; omega
    rw [heq]
    exact package 5 (BB6.Agent19GeneralM3.s 0 0)
      (BB6.Agent19GeneralM3.t 0 0) h (by
        simpa only [BB6.Agent19GeneralM3.m,
          show (2:Nat)^(2*3+2)=256 by decide] using
          BB6.Agent19OddTower.m3_tower_stopping 0 0 h)
  · have heq : r=R 3 7 h := by dsimp [R]; omega
    rw [heq]
    exact package 7 (BB6.Agent19M3Four.s 0 0)
      (BB6.Agent19M3Four.t 0 0) h (by
        simpa only [BB6.Agent19M3Four.r] using
          BB6.Agent19M3Four.extra_three_stopping 0 0 h)
  · have heq : r=R 3 9 h := by dsimp [R]; omega
    rw [heq]
    exact package 9 (BB6.Agent19M3Four.s 1 0)
      (BB6.Agent19M3Four.t 1 0) h (by
        simpa only [BB6.Agent19M3Four.r] using
          BB6.Agent19M3Four.extra_three_stopping 1 0 h)
  · have heq : r=R 3 11 h := by dsimp [R]; omega
    rw [heq]
    exact package 11 (BB6.Agent19M3Four.s 2 0)
      (BB6.Agent19M3Four.t 2 0) h (by
        simpa only [BB6.Agent19M3Four.r] using
          BB6.Agent19M3Four.extra_three_stopping 2 0 h)

#print axioms every_odd_depth_has_unreachable_m3_stopping
end BB6.Agent19M3EveryOdd
