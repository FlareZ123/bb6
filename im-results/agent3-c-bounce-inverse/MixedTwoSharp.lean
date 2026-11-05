import MixedFourNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- A general exact two-link backward sector. The first two links are
    authentic and unique; the second predecessor has no source parents.
    In particular the target has maximal incoming ancestry exactly two. -/
theorem mixed_two_step_sharp (x y : Nat)
    (hfirst : oddLowGate x y)
    (hsecond : let a1 := (x+y-4)/2
               let k1 := (x+3*y-10)/4
               BB6.Agent46.sixEvenRightGate a1 k1)
    (hbad : let a1 := (x+y-4)/2
            let k1 := (x+3*y-10)/4
            let a2 := a1+k1-2
            let k2 := (k1-2)/2
            5≤k2 ∧ k2%2=1 ∧
            ((a2+k2)%4=1 ∨ (a2+k2)%4=2)) :
    (∀ (start : Nat × Nat) (time : Nat),
       BB6.Agent8Section.run secNext (time+3) (some start) ≠ some (x,y)) ∧
    (∃ start : Nat × Nat,
     BB6.Agent8Section.run secNext 2 (some start)=some (x,y)) := by
  rcases hfirst with ⟨hx,hy,hy5,h4,h16,hsize⟩
  let a1 := (x+y-4)/2
  let k1 := (x+3*y-10)/4
  let a2 := a1+k1-2
  let k2 := (k1-2)/2
  change BB6.Agent46.sixEvenRightGate a1 k1 at hsecond
  change 5≤k2 ∧ k2%2=1 ∧
    ((a2+k2)%4=1 ∨ (a2+k2)%4=2) at hbad
  rcases hsecond with ⟨h6,he,h0,h7⟩
  have hmath1 : x+y=2*a1+4 ∧ x+3*y=4*k1+10 := by
    dsimp [a1,k1]
    omega
  have hedge1 : secNext (a1,k1)=some (x,y) :=
    (oddodd_lowval_parent_iff a1 k1 x y hx hy hy5 h4 h16 hsize).mpr hmath1
  have hedge2 : secNext (a2,k2)=some (a1,k1) := by
    apply (BB6.Agent46.section_even_right_six_iff a2 k2 a1 k1 h6 he h0 h7).mpr
    dsimp [a2,k2]
    exact ⟨rfl,rfl⟩
  constructor
  · intro start time hh
    have ht1 : BB6.Agent8Section.run secNext ((time+2)+1) (some start)=
        some (x,y) := by
      simpa only [show time+3=(time+2)+1 by omega] using hh
    change (BB6.Agent8Section.run secNext (time+2) (some start)).bind secNext =
      some (x,y) at ht1
    cases hp1 : BB6.Agent8Section.run secNext (time+2) (some start) with
    | none => simp [hp1] at ht1
    | some p1 =>
        rcases p1 with ⟨a,b⟩
        have hEdge1 : secNext (a,b)=some (x,y) := by
          simpa [hp1] using ht1
        have hab := (oddodd_lowval_parent_iff a b x y hx hy hy5 h4 h16 hsize).mp hEdge1
        have ha1 : a=a1 := by dsimp [a1]; omega
        have hb1 : b=k1 := by dsimp [k1]; omega
        rw [ha1,hb1] at hp1
        change (BB6.Agent8Section.run secNext (time+1) (some start)).bind secNext =
          some (a1,k1) at hp1
        cases hp2 : BB6.Agent8Section.run secNext (time+1) (some start) with
        | none => simp [hp2] at hp1
        | some p2 =>
            rcases p2 with ⟨c,d⟩
            have hEdge2 : secNext (c,d)=some (a1,k1) := by
              simpa [hp2] using hp1
            have hcd := (BB6.Agent46.section_even_right_six_iff
              c d a1 k1 h6 he h0 h7).mp hEdge2
            have hc2 : c=a2 := by dsimp [a2]; omega
            have hd2 : d=k2 := by dsimp [k2]; omega
            rw [hc2,hd2] at hp2
            change (BB6.Agent8Section.run secNext time (some start)).bind secNext =
              some (a2,k2) at hp2
            cases hp3 : BB6.Agent8Section.run secNext time (some start) with
            | none => simp [hp3] at hp2
            | some p3 =>
                rcases p3 with ⟨e,f⟩
                have hEdge3 : secNext (e,f)=some (a2,k2) := by
                  simpa [hp3] using hp2
                have hi := BB6.Agent3.section_odd_image e f a2 k2
                  hEdge3 hbad.1 hbad.2.1
                omega
  · refine ⟨(a2,k2),?_⟩
    simp [BB6.Agent8Section.run,hedge1,hedge2]

#print axioms mixed_two_step_sharp
end BB6.Agent3
