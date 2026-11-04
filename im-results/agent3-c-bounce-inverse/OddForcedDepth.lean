import OddForcedNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3

/-- Unique source-exact predecessor in the original odd/odd gate. -/
def depthParentOdd (x y : Nat) : Nat × Nat :=
  ((x+y-4)/2,(x+3*y-10)/4)

/-- Unique source-exact predecessor in the original even/odd seven gate. -/
def depthParentSeven (x y : Nat) : Nat × Nat :=
  ((x+y-5)/2,(x+3*y-9)/4)

/-- Two successive odd/odd gates are impossible: an odd gate has even first parent. -/
theorem depth_no_odd_odd (x y : Nat) (h : oddLowGate x y) :
    ¬ oddLowGate (depthParentOdd x y).1 (depthParentOdd x y).2 := by
  simp only [oddLowGate,depthParentOdd] at *
  omega

/-- Two successive seven gates are impossible: seven has odd first parent. -/
theorem depth_no_seven_seven (x y : Nat) (h : evenSevenGate x y) :
    ¬ evenSevenGate (depthParentSeven x y).1 (depthParentSeven x y).2 := by
  simp only [evenSevenGate,depthParentSeven] at *
  omega

/-- The S-O-S pattern is arithmetically impossible. The middle odd gate would
    have total sum divisible by sixteen, contradicting its exact-value guard. -/
theorem depth_no_seven_odd_seven (x y : Nat) (hs : evenSevenGate x y)
    (ho : oddLowGate (depthParentSeven x y).1 (depthParentSeven x y).2) :
    ¬ evenSevenGate
        (depthParentOdd (depthParentSeven x y).1 (depthParentSeven x y).2).1
        (depthParentOdd (depthParentSeven x y).1 (depthParentSeven x y).2).2 := by
  simp only [evenSevenGate,oddLowGate,depthParentOdd,depthParentSeven] at *
  omega

/-- Exactly the two source-certified unique-parent operations, without an
    invented edge. -/
def depthForcedEdge (s t : Nat × Nat) : Prop :=
  (oddLowGate s.1 s.2 ∧ t=depthParentOdd s.1 s.2) ∨
  (evenSevenGate s.1 s.2 ∧ t=depthParentSeven s.1 s.2)

/-- A seven gate has at most two consecutive forced inverse edges. -/
theorem depth_no_three_from_seven (s u v w : Nat × Nat)
    (hs : evenSevenGate s.1 s.2) (h1 : depthForcedEdge s u)
    (h2 : depthForcedEdge u v) (h3 : depthForcedEdge v w) : False := by
  rcases h1 with ⟨ho,_⟩ | ⟨_,rfl⟩
  · simp only [evenSevenGate,oddLowGate] at *
    omega
  rcases h2 with ⟨ho,rfl⟩ | ⟨hs2,_⟩
  · rcases h3 with ⟨ho2,_⟩ | ⟨hs3,_⟩
    · exact (depth_no_odd_odd (depthParentSeven s.1 s.2).1
        (depthParentSeven s.1 s.2).2 ho) ho2
    · exact (depth_no_seven_odd_seven s.1 s.2 hs ho) hs3
  · exact (depth_no_seven_seven s.1 s.2 hs) hs2

/-- Universally, no four consecutive odd/odd or seven-sector forced original
    Machine C inverses exist. The bound is independent of counter size. -/
theorem depth_no_four (s t u v w : Nat × Nat)
    (h1 : depthForcedEdge s t) (h2 : depthForcedEdge t u)
    (h3 : depthForcedEdge u v) (h4 : depthForcedEdge v w) : False := by
  rcases h1 with ⟨ho,rfl⟩ | ⟨hs,rfl⟩
  · rcases h2 with ⟨ho2,h2eq⟩ | ⟨hs2,h2eq⟩
    · exact (depth_no_odd_odd s.1 s.2 ho) ho2
    · exact depth_no_three_from_seven (depthParentOdd s.1 s.2)
        u v w hs2 (Or.inr ⟨hs2,h2eq⟩) h3 h4
  · exact depth_no_three_from_seven s (depthParentSeven s.1 s.2)
      u v hs (Or.inr ⟨hs,rfl⟩) h2 h3

/-- The upper bound three is sharp for the source-exact gates. -/
theorem depth_three_example :
    depthForcedEdge (3,33) (16,23) ∧
    depthForcedEdge (16,23) (17,19) ∧
    depthForcedEdge (17,19) (16,16) := by
  simp [depthForcedEdge, oddLowGate, evenSevenGate, depthParentOdd, depthParentSeven]

#print axioms depth_no_four
#print axioms depth_three_example

end BB6.Agent3
