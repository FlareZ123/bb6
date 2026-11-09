import TowerArithmetic
import ThreeConeProper
import ValuationOneOrbit
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Tower
open BB6.Agent46

/-- A missing-image residue inherited from the exact original section. -/
theorem no_parent_odd (a k x y : Nat)
  (hy : 5 ≤ y) (ho : y % 2 = 1) (hs : (x+y)%4=2) :
  secNext (a,k) ≠ some (x,y) := by
  intro hedge
  have hh := BB6.Agent3.section_odd_image a k x y hedge hy ho
  omega

/-- In the odd-sum 1/3/5 mod-8 sectors, every section predecessor is direct. -/
theorem unique_direct (a k x y : Nat)
  (hy : 6 ≤ y) (he : y % 2 = 0)
  (hs : (x+y)%8=1 ∨ (x+y)%8=3 ∨ (x+y)%8=5)
  (hedge : secNext (a,k)=some (x,y)) :
  a=x+y-2 ∧ k=(y-2)/2 := by
  by_cases hval : (x+y)%4=1
  · let u := (x+y)/4
    have hv : x+y+1=2*(2*u+1) := by dsimp [u]; omega
    obtain ⟨ha,hk⟩ :=
      (BB6.Agent34Valuation.val1_parent_iff a k x y u (by omega)
        (Or.inr hv)).mp hedge
    exact ⟨ha,by omega⟩
  · have hs3 : (x+y)%8=3 := by omega
    have hcopy : BB6.Agent34Broad.sectionPreimageAll a k x y :=
      (BB6.Agent46.section_preimage_all_iff a k x y).mp hedge
    obtain ⟨ha,hk⟩ :=
      BB6.Agent34Three.only_direct a k x y hy he (Or.inr hs3) hcopy
    exact ⟨ha,by omega⟩

theorem direct_exists (x y : Nat)
  (hy : 6≤y) (he : y%2=0) :
  secNext (x+y-2,(y-2)/2)=some (x,y) :=
  BB6.Agent34ThreeProper.direct_predecessor x y hy he

/-- An n-edge path from an arbitrary source in the original section. -/
def path : Nat → Nat × Nat → Prop
| 0, _ => True
| n+1, p => ∃ q, secNext q=some p ∧ path n q

/-- A cone point has n consecutive authentic section ancestors, but
    there cannot be n+1 such ancestors, from any starting section state. -/
theorem exact_depth (n x y : Nat) (h : cone n (x,y)) :
    path n (x,y) ∧ ¬path (n+1) (x,y) := by
  induction n generalizing x y with
  | zero =>
      change 5≤y ∧ y%2=1 ∧ (x+y)%4=2 at h
      rcases h with ⟨hy,ho,hs⟩
      constructor
      · trivial
      · intro hh
        change (∃ q, secNext q=some (x,y) ∧ path 0 q) at hh
        rcases hh with ⟨⟨a,k⟩,hedge,_⟩
        exact no_parent_odd a k x y hy ho hs hedge
  | succ n ih =>
      change 6≤y ∧ y%2=0 ∧
        ((x+y)%8=1 ∨ (x+y)%8=3 ∨ (x+y)%8=5) ∧
        cone n (x+y-2,(y-2)/2) at h
      rcases h with ⟨hy,he,hs,hinner⟩
      obtain ⟨hhas,hno⟩ := ih (x+y-2) ((y-2)/2) hinner
      constructor
      · change ∃ q, secNext q=some (x,y) ∧ path n q
        exact ⟨(x+y-2,(y-2)/2),direct_exists x y hy he,hhas⟩
      · intro hh
        change (∃ q, secNext q=some (x,y) ∧ path (n+1) q) at hh
        rcases hh with ⟨⟨a,k⟩,hedge,hchain⟩
        obtain ⟨ha,hk⟩ := unique_direct a k x y hy he hs hedge
        have hp : (a,k)=(x+y-2,(y-2)/2) := by
          exact Prod.ext ha hk
        have hcontra : path (n+1) (x+y-2,(y-2)/2) := by
          simpa only [hp] using hchain
        exact hno hcontra

#print axioms no_parent_odd
#print axioms unique_direct
/-- The actual blank-derived section state (5,1) cannot reach ANY
    forced ancestry cone at any depth or any time, including early times. -/
theorem cone_blank_unreachable (n x y : Nat)
    (h : cone n (x,y)) (time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  induction n generalizing x y time with
  | zero =>
      change 5≤y ∧ y%2=1 ∧ (x+y)%4=2 at h
      rcases h with ⟨hy,ho,hs⟩
      cases time with
      | zero =>
          intro ht
          simp [BB6.Agent8Section.run] at ht
          omega
      | succ t =>
          intro ht
          change (BB6.Agent8Section.run secNext t (some (5,1))).bind secNext =
            some (x,y) at ht
          cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
          | none => simp [hp] at ht
          | some p =>
              rcases p with ⟨a,k⟩
              have he : secNext (a,k)=some (x,y) := by
                simpa [hp] using ht
              exact no_parent_odd a k x y hy ho hs he
  | succ n ih =>
      change 6≤y ∧ y%2=0 ∧
        ((x+y)%8=1 ∨ (x+y)%8=3 ∨ (x+y)%8=5) ∧
        cone n (x+y-2,(y-2)/2) at h
      rcases h with ⟨hy,he,hs,hinner⟩
      cases time with
      | zero =>
          intro ht
          simp [BB6.Agent8Section.run] at ht
          omega
      | succ t =>
          intro ht
          change (BB6.Agent8Section.run secNext t (some (5,1))).bind secNext =
            some (x,y) at ht
          cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
          | none => simp [hp] at ht
          | some p =>
              rcases p with ⟨a,k⟩
              have hedge : secNext (a,k)=some (x,y) := by
                simpa [hp] using ht
              obtain ⟨ha,hk⟩ := unique_direct a k x y hy he hs hedge
              have hprev : BB6.Agent8Section.run secNext t (some (5,1)) =
                  some (x+y-2,(y-2)/2) := by
                simpa only [ha,hk] using hp
              exact ih (x+y-2) ((y-2)/2) hinner t hprev

/-- Every depth occurs over an infinite two-dimensional congruence cylinder.
    These states lie in I_n, outside I_(n+1), and outside the blank orbit. -/
theorem strict_every_depth (n t x : Nat)
    (hx : 8≤x) (hres : x%8=xr n) :
    path n (x,b t n) ∧
    ¬path (n+1) (x,b t n) ∧
    (∀ time, BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (x,b t n)) := by
  have hc := cylinder_cone n t x hx hres
  obtain ⟨hyes,hno⟩ := exact_depth n x (b t n) hc
  exact ⟨hyes,hno,fun time => cone_blank_unreachable n x (b t n) hc time⟩

#print axioms cone_blank_unreachable
#print axioms strict_every_depth

#print axioms exact_depth
end BB6.Agent11Tower
