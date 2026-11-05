import MixedUniversalAncestry
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- If the four-sector normalizer ends in a globally forbidden odd-image
    residue, the target has an exact finite maximal incoming ancestry from
    every possible starting pair. The normalizer gives its actual root. -/
theorem mixed_four_global_sharp (x y : Nat)
    (hbad : let p := mixedFourNormalize x y
      5≤p.2 ∧ p.2%2=1 ∧ ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2)) :
    ∃ d : Nat,
      BB6.Agent8Section.run secNext d
        (some (mixedFourNormalize x y))=some (x,y) ∧
      ∀ (start : Nat × Nat) (time : Nat),
        BB6.Agent8Section.run secNext (time+d+1) (some start) ≠
        some (x,y) := by
  obtain ⟨d,hf,hp⟩ := mixed_four_all_start_exact_ancestry x y
  refine ⟨d,hf,?_⟩
  intro start time h
  have h2 : BB6.Agent8Section.run secNext ((time+1)+d) (some start)=
      some (x,y) := by
    simpa only [show (time+1)+d=time+d+1 by omega] using h
  have hp1 := hp start (time+1) h2
  let p := mixedFourNormalize x y
  change 5≤p.2 ∧ p.2%2=1 ∧
    ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2) at hbad
  change BB6.Agent8Section.run secNext (time+1) (some start)=some p at hp1
  change (BB6.Agent8Section.run secNext time (some start)).bind secNext =
    some p at hp1
  cases hprev : BB6.Agent8Section.run secNext time (some start) with
  | none => simp [hprev] at hp1
  | some q =>
      rcases q with ⟨a,k⟩
      have hed : secNext (a,k)=some p := by simpa [hprev] using hp1
      have hi := BB6.Agent3.section_odd_image a k p.1 p.2 hed
        hbad.1 hbad.2.1
      omega

#print axioms mixed_four_global_sharp
end BB6.Agent3
