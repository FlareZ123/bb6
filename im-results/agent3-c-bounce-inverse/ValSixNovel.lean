import JointMod128Root
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix

def valSixHighClass (j m : Nat) : Prop :=
  (4≤m ∧ m%8=4 ∧ (j+191)%256=(3*m)%256) ∨
  (4≤m ∧ j%128=81 ∧ (j+63)%256=(3*m)%256)

/-- Both new valuation-six forbidden high families lie entirely
inside the PREVIOUS source-verified Agent19+Agent29 allowed parameter
region. Thus the two new root proofs genuinely strengthen that sieve
at every magnitude; overlap is ruled out by universal arithmetic. -/
theorem new_val_six_previously_allowed (j m : Nat)
    (hc : valSixHighClass j m) :
    BB6.Agent29Joint.highAllowedPlus j m := by
  have hx : (2*j+3)%8=5 := by
    rcases hc with h1 | h2 <;> omega
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
     ¬(2≤m ∧ j%8=7 ∧ (j+3*m+15)%64=0) ∧
     ¬(2≤m ∧ j%8=3 ∧ (j+3*m+47)%64=0) ∧
     ¬(3≤m ∧ j%8=5 ∧ (j+3*m+27)%128=0) ∧
     ¬(3≤m ∧ j%8=1 ∧ (j+3*m+91)%128=0) ∧
     ¬(4≤m ∧ j%8=5 ∧ (j+31)%128=(3*m)%128) ∧
     ¬(4≤m ∧ j%32=17 ∧ (j+31)%128=(3*m)%128) ∧
     ¬(4≤m ∧ j%64=57 ∧ (j+31)%128=(3*m)%128) ∧
     ¬(m%32=6 ∧ (j+51)%256=(9*m)%256) := by
    rcases hc with h1 | h2 <;> omega
  dsimp [BB6.Agent29Joint.highAllowedPlus,
    BB6.Agent19Joint.highAllowed,
    BB6.Agent3.jointHighRectAllowed, BB6.Agent3.jointHighAllowed]
  rcases hfin with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14⟩
  exact ⟨⟨⟨⟨h1,h2,h3,h4,h5⟩,h6⟩,hdy,h7,h8,h9,h10⟩,h11,h12,h13,h14⟩

/-- Disjoint explicit infinite progressions of formerly admitted indices
now proven blank-unreachable by ValSixJoint. -/
theorem val_six_progressions (n : Nat) :
    valSixHighClass (77+256*n) (4+256*n) ∧
    valSixHighClass (81+128*n) (48+128*n) := by
  dsimp [valSixHighClass]
  omega

theorem val_six_progressions_prior_allowed (n : Nat) :
    BB6.Agent29Joint.highAllowedPlus (77+256*n) (4+256*n) ∧
    BB6.Agent29Joint.highAllowedPlus (81+128*n) (48+128*n) := by
  obtain ⟨h1,h2⟩ := val_six_progressions n
  exact ⟨new_val_six_previously_allowed _ _ h1,
    new_val_six_previously_allowed _ _ h2⟩

#print axioms new_val_six_previously_allowed
#print axioms val_six_progressions
#print axioms val_six_progressions_prior_allowed
end BB6.Agent3ValSix
