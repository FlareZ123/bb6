import OddSevenSliver
import OddOddLowVal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- All original Machine C returns in the even/odd sum-plus-one
    valuation-three sector have exactly one authentic predecessor. -/
theorem odd_seven_unique_parent (x y : Nat)
    (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y+1)%16=8) (hsize : 23≤x+y) :
    ∃ a k, secNext (a,k)=some (x,y) ∧
      ∀ b c, secNext (b,c)=some (x,y) → b=a ∧ c=k := by
  let a := (x+y-5)/2
  let k := (x+3*y-9)/4
  have hsum : x+y=2*a+5 := by dsimp [a]; omega
  have hcost : x+3*y=4*k+9 := by dsimp [k]; omega
  have hedge : secNext (a,k)=some (x,y) :=
    (odd_seven_parent_iff a k x y hx hy hy5 hs hsize).mpr ⟨hsum,hcost⟩
  refine ⟨a,k,hedge,?_⟩
  intro b c hbc
  have hh := (odd_seven_parent_iff b c x y hx hy hy5 hs hsize).mp hbc
  omega

/-- Source-exact every-time reachability iff of a large even/odd target
    and its unique original predecessor, without finite quotient assumptions. -/
theorem odd_seven_blank_reach_iff (x y : Nat)
    (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y+1)%16=8) (hsize : 23≤x+y) :
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (x,y)) ↔
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some ((x+y-5)/2,(x+3*y-9)/4)) := by
  let a := (x+y-5)/2
  let k := (x+3*y-9)/4
  have hsum : x+y=2*a+5 := by dsimp [a]; omega
  have hcost : x+3*y=4*k+9 := by dsimp [k]; omega
  have hedge : secNext (a,k)=some (x,y) :=
    (odd_seven_parent_iff a k x y hx hy hy5 hs hsize).mpr ⟨hsum,hcost⟩
  change (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (x,y)) ↔
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (a,k))
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero =>
        simp [BB6.Agent8Section.run] at hn
        omega
    | succ n =>
        cases hr : BB6.Agent8Section.run secNext n (some (5,1)) with
        | none => simp [BB6.Agent8Section.run,hr] at hn
        | some p =>
            rcases p with ⟨b,c⟩
            have hed : secNext (b,c)=some (x,y) := by
              simpa [BB6.Agent8Section.run,hr] using hn
            have eq := (odd_seven_parent_iff b c x y hx hy hy5 hs hsize).mp hed
            have hb : b=a := by omega
            have hc : c=k := by omega
            refine ⟨n,?_⟩
            rwa [hb,hc] at hr
  · rintro ⟨n,hn⟩
    refine ⟨n+1,?_⟩
    simp [BB6.Agent8Section.run,hn,hedge]

/-- Every such exact original-section predecessor decreases the weighted
    mass by seven, a rank decrease uniform over the complete sector. -/
theorem odd_seven_parent_mass (a k x y : Nat)
    (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y+1)%16=8) (hsize : 23≤x+y)
    (hedge : secNext (a,k)=some (x,y)) :
    a+2*k+7=x+2*y := by
  have h := (odd_seven_parent_iff a k x y hx hy hy5 hs hsize).mp hedge
  omega

#print axioms odd_seven_unique_parent
#print axioms odd_seven_blank_reach_iff
#print axioms odd_seven_parent_mass
end BB6.Agent3
