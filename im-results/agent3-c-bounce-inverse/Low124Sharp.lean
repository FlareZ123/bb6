import MixedUniversalSharp
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Remove one known unique true-source predecessor from any arbitrary-start
section trace. -/
private theorem pull_124_unique (start : Nat×Nat) (time x y u v : Nat)
    (huni : ∀ a k, secNext (a,k)=some (x,y) → a=u ∧ k=v)
    (h : BB6.Agent8Section.run secNext (time+1) (some start)=some (x,y)) :
    BB6.Agent8Section.run secNext time (some start)=some (u,v) := by
  change (BB6.Agent8Section.run secNext time (some start)).bind secNext =
    some (x,y) at h
  cases hp : BB6.Agent8Section.run secNext time (some start) with
  | none => simp [hp] at h
  | some p =>
      rcases p with ⟨a,k⟩
      have hed : secNext (a,k)=some (x,y) := by simpa [hp] using h
      obtain ⟨ha,hk⟩ := huni a k hed
      simpa only [ha,hk] using hp

/-- Exact length-four authentic inverse chain and no length-five ancestry,
for all nonnegative parameters and every hypothetical starting state.
This universal sharpness is independent of any blank-start assumption. -/
theorem rectangle_124_all_start_sharp (a b : Nat) :
    (BB6.Agent8Section.run secNext 4
       (some (56*a+216*b+196,4*a+20*b+17)) =
       some (64*a+1,128*b+124)) ∧
    (∀ (start : Nat×Nat) (time : Nat),
       BB6.Agent8Section.run secNext (time+5) (some start) ≠
         some (64*a+1,128*b+124)) := by
  let x0 := 64*a+1
  let y0 := 128*b+124
  let x1 := 64*a+128*b+123
  let y1 := 64*b+61
  let x2 := 32*a+96*b+90
  let y2 := 16*a+80*b+74
  let x3 := 48*a+176*b+162
  let y3 := 8*a+40*b+36
  let x4 := 56*a+216*b+196
  let y4 := 4*a+20*b+17
  have hg0 : 6≤y0 ∧ y0%2=0 ∧ (x0+y0)%8≠0 ∧ (x0+y0)%8≠7 := by
    dsimp [x0,y0]; omega
  have hg1 : x1%2=1 ∧ y1%2=1 ∧ 5≤y1 ∧
      (x1+y1)%4=0 ∧ (x1+y1)%16≠0 ∧ 24≤x1+y1 := by
    dsimp [x1,y1]; omega
  have hg2 : 6≤y2 ∧ y2%2=0 ∧ (x2+y2)%8≠0 ∧ (x2+y2)%8≠7 := by
    dsimp [x2,y2]; omega
  have hg3 : 6≤y3 ∧ y3%2=0 ∧ (x3+y3)%8≠0 ∧ (x3+y3)%8≠7 := by
    dsimp [x3,y3]; omega
  have he0 : secNext (x1,y1)=some (x0,y0) := by
    apply (section_even_right_six_iff x1 y1 x0 y0 hg0.1 hg0.2.1
      hg0.2.2.1 hg0.2.2.2).mpr
    dsimp [x0,y0,x1,y1]
    constructor <;> omega
  have he1 : secNext (x2,y2)=some (x1,y1) := by
    apply (oddodd_lowval_parent_iff x2 y2 x1 y1 hg1.1 hg1.2.1
      hg1.2.2.1 hg1.2.2.2.1 hg1.2.2.2.2.1 hg1.2.2.2.2.2).mpr
    dsimp [x1,y1,x2,y2]
    constructor <;> omega
  have he2 : secNext (x3,y3)=some (x2,y2) := by
    apply (section_even_right_six_iff x3 y3 x2 y2 hg2.1 hg2.2.1
      hg2.2.2.1 hg2.2.2.2).mpr
    dsimp [x2,y2,x3,y3]
    constructor <;> omega
  have he3 : secNext (x4,y4)=some (x3,y3) := by
    apply (section_even_right_six_iff x4 y4 x3 y3 hg3.1 hg3.2.1
      hg3.2.2.1 hg3.2.2.2).mpr
    dsimp [x3,y3,x4,y4]
    constructor <;> omega
  have hu0 : ∀ u v, secNext (u,v)=some (x0,y0) → u=x1 ∧ v=y1 := by
    intro u v h
    have hh := (section_even_right_six_iff u v x0 y0 hg0.1 hg0.2.1
      hg0.2.2.1 hg0.2.2.2).mp h
    dsimp [x0,y0,x1,y1] at *
    omega
  have hu1 : ∀ u v, secNext (u,v)=some (x1,y1) → u=x2 ∧ v=y2 := by
    intro u v h
    have hh := (oddodd_lowval_parent_iff u v x1 y1 hg1.1 hg1.2.1
      hg1.2.2.1 hg1.2.2.2.1 hg1.2.2.2.2.1 hg1.2.2.2.2.2).mp h
    dsimp [x1,y1,x2,y2] at *
    omega
  have hu2 : ∀ u v, secNext (u,v)=some (x2,y2) → u=x3 ∧ v=y3 := by
    intro u v h
    have hh := (section_even_right_six_iff u v x2 y2 hg2.1 hg2.2.1
      hg2.2.2.1 hg2.2.2.2).mp h
    dsimp [x2,y2,x3,y3] at *
    omega
  have hu3 : ∀ u v, secNext (u,v)=some (x3,y3) → u=x4 ∧ v=y4 := by
    intro u v h
    have hh := (section_even_right_six_iff u v x3 y3 hg3.1 hg3.2.1
      hg3.2.2.1 hg3.2.2.2).mp h
    dsimp [x3,y3,x4,y4] at *
    omega
  constructor
  · change BB6.Agent8Section.run secNext 4 (some (x4,y4))=some (x0,y0)
    simp [BB6.Agent8Section.run, he0,he1,he2,he3]
  · intro start time ht
    have ht0 : BB6.Agent8Section.run secNext ((time+4)+1)
        (some start)=some (x0,y0) := by
      simpa only [show (time+4)+1=time+5 by omega] using ht
    have hp1 := pull_124_unique start (time+4) x0 y0 x1 y1 hu0 ht0
    have hp2 := pull_124_unique start (time+3) x1 y1 x2 y2 hu1 (by
      simpa only [show (time+3)+1=time+4 by omega] using hp1)
    have hp3 := pull_124_unique start (time+2) x2 y2 x3 y3 hu2 (by
      simpa only [show (time+2)+1=time+3 by omega] using hp2)
    have hp4 := pull_124_unique start (time+1) x3 y3 x4 y4 hu3 (by
      simpa only [show (time+1)+1=time+2 by omega] using hp3)
    change (BB6.Agent8Section.run secNext time (some start)).bind secNext =
      some (x4,y4) at hp4
    cases hp : BB6.Agent8Section.run secNext time (some start) with
    | none => simp [hp] at hp4
    | some q =>
        rcases q with ⟨u,v⟩
        have hed : secNext (u,v)=some (x4,y4) := by simpa [hp] using hp4
        have hi := section_odd_image u v x4 y4 hed (by dsimp [y4];omega)
          (by dsimp [y4];omega)
        dsimp [x4,y4] at hi
        omega

#print axioms rectangle_124_all_start_sharp
end BB6.Agent3
