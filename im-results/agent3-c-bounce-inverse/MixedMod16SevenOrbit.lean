import MixedMod16SevenFull
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Exact genuine Machine C blank reachability in the previously branching
    even-right mod16-seven source sector: the target is reached iff at
    least one of its two authentic source predecessors is reached.
    No branch truncation or finite blank computation horizon is used. -/
theorem mod16_seven_blank_reach_iff (x y : Nat)
    (hx : x%2=1) (he : y%2=0) (hmod : (x+y+1)%16=8)
    (hy : 64≤y) :
    CReach x y ↔
      CReach (x+y-2) ((y-2)/2) ∨
      CReach ((x+y+1)/4-3)
        ((x+2*y-((x+y+1)/4-3)-10)/2) := by
  let ad := x+y-2
  let kd := (y-2)/2
  let ab := (x+y+1)/4-3
  let kb := (x+2*y-ab-10)/2
  have hparent := mod16_seven_two_exact_parents x y hx he hmod hy
  dsimp only at hparent
  rcases hparent with ⟨hed,heb,_,huniq⟩
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
            have hstep : secNext (a,k)=some (x,y) := by
              simpa [BB6.Agent8Section.run,hp] using hr
            rcases huniq a k hstep with ⟨ha,hk⟩ | ⟨ha,hk⟩
            · left
              exact ⟨n,by simpa only [ha,hk] using hp⟩
            · right
              exact ⟨n,by simpa only [ha,hk] using hp⟩
  · intro h
    rcases h with ⟨n,hn⟩ | ⟨n,hn⟩
    · refine ⟨n+1,?_⟩
      simpa [BB6.Agent8Section.run,hn,hed]
    · refine ⟨n+1,?_⟩
      simpa [BB6.Agent8Section.run,hn,heb]

#print axioms mod16_seven_blank_reach_iff
end BB6.Agent3
