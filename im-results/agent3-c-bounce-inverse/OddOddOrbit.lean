import OddOddWedge
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Every odd-odd section output whose sum has exact 2-adic valuation two
    has one actual source predecessor, with an explicit arithmetic formula. -/
theorem oddodd_unique_parent (x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%8=4) :
    ∃ a k, secNext (a,k)=some (x,y) ∧
      ∀ b c, secNext (b,c)=some (x,y) → b=a ∧ c=k := by
  let a := (x+y-4)/2
  let k := (x+3*y-10)/4
  have hsum : x+y=2*a+4 := by dsimp [a]; omega
  have hcost : x+3*y=4*k+10 := by dsimp [k]; omega
  have hedge : secNext (a,k)=some (x,y) :=
    (oddodd_parent_iff a k x y hx hy hy5 hs).mpr ⟨hsum,hcost⟩
  refine ⟨a,k,hedge,?_⟩
  intro b c hbc
  have hh := (oddodd_parent_iff b c x y hx hy hy5 hs).mp hbc
  omega

/-- A uniform exact one-step backward reduction for the *genuine blank
    section orbit*, for every odd-odd target with v2(x+y)=2. -/
theorem oddodd_blank_reach_iff (x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%8=4) :
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (x,y)) ↔
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some ((x+y-4)/2,(x+3*y-10)/4)) := by
  let a := (x+y-4)/2
  let k := (x+3*y-10)/4
  have hsum : x+y=2*a+4 := by dsimp [a]; omega
  have hcost : x+3*y=4*k+10 := by dsimp [k]; omega
  have hedge : secNext (a,k)=some (x,y) :=
    (oddodd_parent_iff a k x y hx hy hy5 hs).mpr ⟨hsum,hcost⟩
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
            have eq := (oddodd_parent_iff b c x y hx hy hy5 hs).mp hed
            have hb : b=a := by omega
            have hc : c=k := by omega
            refine ⟨n,?_⟩
            rwa [hb,hc] at hr
  · rintro ⟨n,hn⟩
    refine ⟨n+1,?_⟩
    simp [BB6.Agent8Section.run,hn,hedge]

#print axioms oddodd_unique_parent
#print axioms oddodd_blank_reach_iff
end BB6.Agent3
