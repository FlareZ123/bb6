import CFourHierarchy
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Four
open BB6.Agent46

/-- Each recursively lifted strict-image cone is unreachable at ALL
    times from the true blank initial section, with no finite cutoff. -/
theorem cone_blank_unreachable_all_depths (r time x y : Nat)
    (h : Cone r x y) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  induction r generalizing time x y with
  | zero =>
      have hy : 34≤y := by exact Nat.le_trans (by omega) h.1
      have hsector : ((x+y)%8=1 ∧ y%16=10) ∨
          ((x+y)%8=3 ∧ y%16=2) := by
        left
        exact ⟨h.2.2,h.2.1⟩
      exact BB6.Agent34Three.cone_blank_unreachable time x y hy hsector
  | succ r ih =>
      change 6≤y ∧ y%2=0 ∧ (x+y)%4=1 ∧
        Cone r (x+y-2) ((y-2)/2) at h
      cases time with
      | zero =>
          intro ht
          simp [BB6.Agent8Section.run] at ht
          omega
      | succ n =>
          intro ht
          change (BB6.Agent8Section.run secNext n (some (5,1))).bind secNext =
            some (x,y) at ht
          cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
          | none => simp [hp] at ht
          | some p =>
              rcases p with ⟨a,k⟩
              have hs : secNext (a,k)=some (x,y) := by simpa [hp] using ht
              have hinv : sectionPreimageAll a k x y :=
                (section_preimage_all_iff a k x y).mp hs
              obtain ⟨ha,hk⟩ := BB6.Agent4Three.only_direct_mod4_one a k x y
                h.1 h.2.1 h.2.2.1 hinv
              have hprev : Cone r a k := by
                have hk' : k=(y-2)/2 := by omega
                simpa only [ha,hk'] using h.2.2.2
              exact ih n a k hprev hp

/-- Every member of every exact-density strict-image lattice is
    permanently absent from the original Machine C blank orbit. -/
theorem blank_excludes_all_depth_cylinders (r s t time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (8*s+7+4*r,bandY r t) := by
  exact cone_blank_unreachable_all_depths r time _ _
    (each_cone_has_cylinder r s t)

#print axioms cone_blank_unreachable_all_depths
#print axioms blank_excludes_all_depth_cylinders
end BB6.Agent4Four
