import OddOddVal3
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Every large odd-odd return with 2-adic sum valuation exactly 3 has
    exactly one source input, which is a genuine original-section edge. -/
theorem oddodd_val3_unique_parent (x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%16=8) (hsize : 24≤x+y) :
    ∃ a k, secNext (a,k)=some (x,y) ∧
      ∀ b c, secNext (b,c)=some (x,y) → b=a ∧ c=k := by
  let a := (x+y-4)/2
  let k := (x+3*y-10)/4
  have hsum : x+y=2*a+4 := by dsimp [a]; omega
  have hcost : x+3*y=4*k+10 := by dsimp [k]; omega
  have hedge : secNext (a,k)=some (x,y) :=
    (oddodd_val3_parent_iff a k x y hx hy hy5 hs hsize).mpr ⟨hsum,hcost⟩
  refine ⟨a,k,hedge,?_⟩
  intro b c hbc
  have hh := (oddodd_val3_parent_iff b c x y hx hy hy5 hs hsize).mp hbc
  omega

/-- An exact all-time source-certified blank-reachability iff on the
    entire infinite odd/odd sum valuation-three sector. -/
theorem oddodd_val3_blank_reach_iff (x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%16=8) (hsize : 24≤x+y) :
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (x,y)) ↔
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some ((x+y-4)/2,(x+3*y-10)/4)) := by
  let a := (x+y-4)/2
  let k := (x+3*y-10)/4
  have hsum : x+y=2*a+4 := by dsimp [a]; omega
  have hcost : x+3*y=4*k+10 := by dsimp [k]; omega
  have hedge : secNext (a,k)=some (x,y) :=
    (oddodd_val3_parent_iff a k x y hx hy hy5 hs hsize).mpr ⟨hsum,hcost⟩
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
            have eq := (oddodd_val3_parent_iff b c x y hx hy hy5 hs hsize).mp hed
            have hb : b=a := by omega
            have hc : c=k := by omega
            refine ⟨n,?_⟩
            rwa [hb,hc] at hr
  · rintro ⟨n,hn⟩
    refine ⟨n+1,?_⟩
    simp [BB6.Agent8Section.run,hn,hedge]

#print axioms oddodd_val3_unique_parent
#print axioms oddodd_val3_blank_reach_iff
end BB6.Agent3
