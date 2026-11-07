import ValSixC58
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11C58ValSix

/-- Every member of this infinite high-dyadic family survives all
    previous exact ValSixFull and C58 source-derived necessary filters.
    It is thereby an independent new source gate, not an overlap. -/
theorem previous_combined_admits_high_dyadic (r : Nat) :
    highAllowed (7+64*r) 3 := by
  let j := 7+64*r
  have hbase : BB6.Agent3.jointHighAllowed j 3 := by
    unfold BB6.Agent3.jointHighAllowed
    dsimp [j]
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j 3 := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hbase,by dsimp [j]; omega⟩
  have hdy : ∀ n, ¬(n+4≤2*3+2 ∧
      (j+3*3+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,_,hx⟩
    have hx1 : (2*j+3)%8=1 := by dsimp [j]; omega
    by_cases heven : n%2=0
    · simp [heven] at hx
      omega
    · simp [heven] at hx
      omega
  have h19 : BB6.Agent19Joint.highAllowed j 3 := by
    unfold BB6.Agent19Joint.highAllowed
    refine ⟨hrect,hdy,?_,?_,?_,?_⟩ <;> dsimp [j] <;> omega
  have h29 : BB6.Agent29Joint.highAllowedPlus j 3 := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨h19,by omega,by omega,by omega,by omega⟩
  have hval : BB6.Agent3ValSix.highAllowedValSixThree j 3 := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    exact ⟨⟨h29,by omega,by omega⟩,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j 3 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by dsimp [j]; omega,by dsimp [j]; omega⟩
  have hfive : BB6.Agent19Five.highAllowed j 3 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  let k := 2^(2*3+2)*(j+3)-(j+3*3+5)
  have hk : k=2539+16320*r := by
    dsimp [k,j]
    omega
  have hguard : ¬(4≤k ∧ k%2=0 ∧ ((2*j+3)+k)%4=1) := by
    rw [hk]
    omega
  have hnorm : BB6.Agent15.affineNormalize (2*j+3) k=(2*j+3,k) := by
    simp [BB6.Agent15.affineNormalize,hguard]
  have hright : (BB6.Agent15.affineNormalize (2*j+3) k).2 ≠ 4 := by
    rw [hnorm,hk]
    omega
  have hall : BB6.Agent3ValSix.highAllowedValSixFull j 3 := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    refine ⟨hval,hfive,?_,?_,?_,?_⟩
    · dsimp [j]; omega
    · dsimp [j]; omega
    · omega
    · simpa [k] using hright
  have hnot58 : ¬(3≤3 ∧ j%32=31 ∧ (j+3*3+5)%256=198) := by
    dsimp [j]
    omega
  exact ⟨hall,hnot58⟩

/-- Every parameter above matches the new dyadic class, uniformly. -/
theorem prior_high_dyadic_matches_new_class (r : Nat) :
    3≤3 ∧ 3%4=3 ∧ ((7+64*r)+9*3+14)%64=48 := by
  omega

/-- At the next inverse depth (r=3), an infinite high family with
    m=5 survives the entire previous ValSixFull+C58 sieve. This is
    disjoint from the earlier depth-two family m%4=3. -/
theorem previous_combined_admits_high_depth_three (t : Nat) :
    highAllowed (37+128*t) 5 := by
  let j := 37+128*t
  have hbase : BB6.Agent3.jointHighAllowed j 5 := by
    unfold BB6.Agent3.jointHighAllowed
    dsimp [j]
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j 5 := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hbase,by dsimp [j]; omega⟩
  have hdy : ∀ n, ¬(n+4≤2*5+2 ∧
      (j+3*5+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,_,hx⟩
    have hx1 : (2*j+3)%8=5 := by dsimp [j]; omega
    by_cases heven : n%2=0
    · simp [heven] at hx
      omega
    · simp [heven] at hx
      omega
  have h19 : BB6.Agent19Joint.highAllowed j 5 := by
    unfold BB6.Agent19Joint.highAllowed
    refine ⟨hrect,hdy,?_,?_,?_,?_⟩ <;> dsimp [j] <;> omega
  have h29 : BB6.Agent29Joint.highAllowedPlus j 5 := by
    unfold BB6.Agent29Joint.highAllowedPlus
    refine ⟨h19,?_,?_,?_,?_⟩ <;> dsimp [j] <;> omega
  have hval : BB6.Agent3ValSix.highAllowedValSixThree j 5 := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    refine ⟨⟨h29,?_,?_⟩,?_⟩ <;> dsimp [j] <;> omega
  have h11 : BB6.Agent11Joint.highAllowed j 5 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by dsimp [j]; omega,by dsimp [j]; omega⟩
  have hfive : BB6.Agent19Five.highAllowed j 5 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  let k := 2^(2*5+2)*(j+3)-(j+3*5+5)
  have hk : k=163783+524160*t := by
    dsimp [k,j]
    omega
  have hguard : ¬(4≤k ∧ k%2=0 ∧ ((2*j+3)+k)%4=1) := by
    rw [hk]
    omega
  have hnorm : BB6.Agent15.affineNormalize (2*j+3) k=(2*j+3,k) := by
    simp [BB6.Agent15.affineNormalize,hguard]
  have hright : (BB6.Agent15.affineNormalize (2*j+3) k).2 ≠ 4 := by
    rw [hnorm,hk]
    omega
  have hall : BB6.Agent3ValSix.highAllowedValSixFull j 5 := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    refine ⟨hval,hfive,?_,?_,?_,?_⟩
    · dsimp [j]; omega
    · dsimp [j]; omega
    · omega
    · simpa [k] using hright
  have hnot58 : ¬(3≤5 ∧ j%32=31 ∧ (j+3*5+5)%256=198) := by
    dsimp [j]
    omega
  exact ⟨hall,hnot58⟩

/-- Uniform depth-three high-gate residues. -/
theorem prior_high_depth_three_matches_new_class (t : Nat) :
    2≤3 ∧ 3≤5 ∧ 3+4≤2*5+2 ∧
    5%4=(2*3+3)%4 ∧
    ((37+128*t)+9*5+14)%2^(3+4)=3*2^(3+2) := by
  omega

#print axioms previous_combined_admits_high_depth_three
#print axioms prior_high_depth_three_matches_new_class
#print axioms previous_combined_admits_high_dyadic
#print axioms prior_high_dyadic_matches_new_class
end BB6.Agent11C58ValSix
