import ZeroEvenUniversal
import Agent3COrbitIff
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- A genuine source edge transports reachability from the authentic
    Machine C blank section through one return. -/
theorem blank_reach_step (a k x y : Nat)
    (hr : CReach a k)
    (hs : secNext (a,k)=some (x,y)) :
    CReach x y := by
  rcases hr with ⟨n,hn⟩
  exact ⟨n+1,by simpa [BB6.Agent8Section.run,hn,hs]⟩

/-- Every genuinely blank-reached (0,y), y even >=16, has a genuine
    predecessor from exactly one of three complete arithmetic sectors;
    each alternative also suffices for genuine future reachability.
    This has NO unknown fixed inverse-depth parameter: r,u are quantified. -/
theorem zero_even_blank_reach_iff (y : Nat)
    (hy : 16≤y) (he : y%2=0) :
    CReach 0 y ↔
      CReach (y-2) (y/2-1) ∨
      (∃ r u : Nat, 2≤u ∧ y=8*4^r*u ∧
        CReach (2*u-2) (y-(u+4+3*r))) ∨
      (∃ r : Nat, y=16*4^r ∧ CReach 0 (y-(3*r+6))) := by
  constructor
  · rintro ⟨time,hr⟩
    cases time with
    | zero =>
      simp [BB6.Agent8Section.run] at hr
    | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
        simp [BB6.Agent8Section.run,hp] at hr
      | some p =>
        rcases p with ⟨a,k⟩
        have hs : secNext (a,k)=some (0,y) := by
          simpa [BB6.Agent8Section.run,hp] using hr
        rcases (zero_even_preimages_iff a k y hy he).mp hs with
            ⟨ha,hk⟩ | ⟨r,u,hu,hyEq,ha,hk⟩ | ⟨r,hyEq,ha,hk⟩
        · exact Or.inl ⟨n,by rwa [ha,hk] at hp⟩
        · exact Or.inr (Or.inl ⟨r,u,hu,hyEq,⟨n,by rwa [ha,hk] at hp⟩⟩)
        · exact Or.inr (Or.inr ⟨r,hyEq,⟨n,by rwa [ha,hk] at hp⟩⟩)
  · rintro (hd | ⟨r,u,hu,hyEq,hr⟩ | ⟨r,hyEq,hr⟩)
    · apply blank_reach_step (y-2) (y/2-1) 0 y hd
      apply (zero_even_preimages_iff (y-2) (y/2-1) y hy he).mpr
      exact Or.inl ⟨rfl,rfl⟩
    · have hs : secNext (2*u-2) (y-(u+4+3*r))=some (0,y) :=
        (zero_even_preimages_iff (2*u-2) (y-(u+4+3*r)) y hy he).mpr
          (Or.inr (Or.inl ⟨r,u,hu,hyEq,rfl,rfl⟩))
      exact blank_reach_step _ _ _ _ hr hs
    · have hs : secNext 0 (y-(3*r+6))=some (0,y) :=
        (zero_even_preimages_iff 0 (y-(3*r+6)) y hy he).mpr
          (Or.inr (Or.inr ⟨r,hyEq,rfl,rfl⟩))
      exact blank_reach_step _ _ _ _ hr hs

#print axioms blank_reach_step
#print axioms zero_even_blank_reach_iff
end BB6.Agent3
