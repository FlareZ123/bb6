import JointMod128Root
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Joint

/-- Union of the four newly source-proven forbidden high stopping
parameter cylinders, independent of the stopping Diophantine equation. -/
def newHighClass (j m : Nat) : Prop :=
  (4≤m ∧ j%8=5 ∧ (j+31)%128=(3*m)%128) ∨
  (4≤m ∧ j%32=17 ∧ (j+31)%128=(3*m)%128) ∨
  (4≤m ∧ j%64=57 ∧ (j+31)%128=(3*m)%128) ∨
  (m%32=6 ∧ (j+51)%256=(9*m)%256)

/-- Every high parameter excluded by these four NEW root arguments
satisfies ALL the previous combined Agent19 source-verified high
filters. Thus each new family is genuinely absent from the prior
finite/infinite congruence sieve, for all magnitudes and indices. -/
theorem new_high_class_previously_allowed (j m : Nat)
    (hc : newHighClass j m) : BB6.Agent19Joint.highAllowed j m := by
  have hodd : j%2=1 := by
    rcases hc with h0 | h1 | h2 | h3 <;> omega
  have hdy : ∀ n, ¬(n+4≤2*m+2 ∧
      (j+3*m+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,_,hpar⟩
    by_cases hn : n%2=0
    · simp only [if_pos hn] at hpar
      omega
    · simp only [if_neg hn] at hpar
      omega
  have hfin :
     ¬(2≤m ∧ j%4=3 ∧ (j+3*m+7)%16=0) ∧
     ¬(2≤m ∧ j%4=1 ∧ (j+3*m+11)%32=0) ∧
     ¬(4≤m ∧ ((m%4=0 ∧ (j+m)%32=26) ∨ (m%4=1 ∧ (j+m)%32=2))) ∧
     ¬(m=1 ∧ j%32=1) ∧
     ¬(2≤m ∧ j%2=1 ∧ (j+3*m+5)%8=0) ∧
     ¬(m%32=5 ∧ j%32=12) ∧
     ¬ (2≤m ∧ j%8=7 ∧ (j+3*m+15)%64=0) ∧
     ¬ (2≤m ∧ j%8=3 ∧ (j+3*m+47)%64=0) ∧
     ¬ (3≤m ∧ j%8=5 ∧ (j+3*m+27)%128=0) ∧
     ¬ (3≤m ∧ j%8=1 ∧ (j+3*m+91)%128=0) := by
    rcases hc with h0 | h1 | h2 | h3 <;> omega
  dsimp [BB6.Agent19Joint.highAllowed,
    BB6.Agent3.jointHighRectAllowed, BB6.Agent3.jointHighAllowed]
  rcases hfin with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  exact ⟨⟨h1,h2,h3,h4,h5⟩,h6,hdy,h7,h8,h9,h10⟩

#print axioms new_high_class_previously_allowed
end BB6.Agent29Joint
