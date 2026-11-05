import MixedOdd16TwoConstruct
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Exact original blank-section reachability in the formerly branching
    high-valuation odd/odd sector: a target is genuinely reachable iff
    at least one of its TWO source-authentic predecessor states is.
    Holds at arbitrarily large counters and arbitrary predecessor depth. -/
theorem oddodd_sum16_blank_reach_iff (x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hsize : 64≤y)
    (hmod : (x+y)%32=16) :
    CReach x y ↔
      CReach ((x+y-4)/2) ((x+3*y-10)/4) ∨
      CReach ((x+y-16)/8) ((7*x+15*y-88)/16) := by
  let a0 := (x+y-4)/2
  let k0 := (x+3*y-10)/4
  let a2 := (x+y-16)/8
  let k2 := (7*x+15*y-88)/16
  obtain ⟨he0,he2⟩ := oddodd_sum16_two_parent_exist x y hx hy hsize hmod
  constructor
  · rintro ⟨time,hr⟩
    cases time with
    | zero =>
        simp [BB6.Agent8Section.run] at hr
        omega
    | succ n =>
        cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
        | none => simp [BB6.Agent8Section.run,hp] at hr
        | some p =>
            rcases p with ⟨a,k⟩
            have he : secNext (a,k)=some (x,y) := by
              simpa [BB6.Agent8Section.run,hp] using hr
            have hparent := oddodd_sum16_mod32_two_predecessors
              a k x y hx hy hsize hmod he
            rcases hparent with ⟨ha,hk⟩ | ⟨ha,hk⟩
            · exact Or.inl ⟨n,by simpa only [ha,hk] using hp⟩
            · exact Or.inr ⟨n,by simpa only [ha,hk] using hp⟩
  · rintro (⟨n,hn⟩ | ⟨n,hn⟩)
    · exact ⟨n+1,by simpa [BB6.Agent8Section.run,hn,he0]⟩
    · exact ⟨n+1,by simpa [BB6.Agent8Section.run,hn,he2]⟩

#print axioms oddodd_sum16_blank_reach_iff
end BB6.Agent3
