import CAltFifthStrict
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Five
open BB6.Agent46

/-- The new fifth-versus-sixth cylinder arises by a single genuine
    direct lift of the fourth-versus-fifth cylinder. -/
theorem five_edges_exist (r t : Nat) (ht : 2≤t) :
    ∃ a0 b0 a1 b1 a2 b2 a3 b3 a4 b4,
      secNext (a0,b0)=some (a1,b1) ∧
      secNext (a1,b1)=some (a2,b2) ∧
      secNext (a2,b2)=some (a3,b3) ∧
      secNext (a3,b3)=some (a4,b4) ∧
      secNext (a4,b4)=some (64*r+61,128*t+30) := by
  obtain ⟨a0,b0,a1,b1,a2,b2,a3,b3,h0,h1,h2,h3⟩ :=
    four_edges_exist (r+2*t+1) t ht
  have hlast : secNext (64*(r+2*t+1)+25,64*t+14)=
      some (64*r+61,128*t+30) := by
    have hh := BB6.Agent34ThreeProper.direct_predecessor
      (64*r+61) (128*t+30) (by omega) (by omega)
    have hx : (64*r+61)+(128*t+30)-2=64*(r+2*t+1)+25 := by omega
    have hy : ((128*t+30)-2)/2=64*t+14 := by omega
    simpa only [hx,hy] using hh
  exact ⟨a0,b0,a1,b1,a2,b2,a3,b3,64*(r+2*t+1)+25,
    64*t+14,h0,h1,h2,h3,hlast⟩

/-- Every six-step original source ancestry is forbidden, including
    the bounce branch at the lower source image level. -/
theorem six_edges_impossible
    (r t u v a b c d e f g h i j : Nat)
    (ht : 2≤t) (he : (r+t)%2=0)
    (h0 : secNext (u,v)=some (a,b))
    (h1 : secNext (a,b)=some (c,d))
    (h2 : secNext (c,d)=some (e,f))
    (h3 : secNext (e,f)=some (g,h))
    (h4 : secNext (g,h)=some (i,j))
    (h5 : secNext (i,j)=some (64*r+61,128*t+30)) : False := by
  have hInv : sectionPreimageAll i j (64*r+61) (128*t+30) :=
    (section_preimage_all_iff i j _ _).mp h5
  have hcopy : BB6.Agent34Broad.sectionPreimageAll i j _ _ := hInv
  obtain ⟨hi,hj⟩ := BB6.Agent34Three.only_direct
    i j (64*r+61) (128*t+30)
    (by omega) (by omega) (Or.inr (by omega)) hcopy
  have hparent : secNext (g,h)=
      some (64*(r+2*t+1)+25,64*t+14) := by
    have hxi : i=64*(r+2*t+1)+25 := by omega
    have hyj : j=64*t+14 := by omega
    simpa only [hxi,hyj] using h4
  have hpar : ((r+2*t+1)+t)%2=1 := by omega
  exact five_edges_impossible (r+2*t+1) t u v a b c d e f g h
    ht hpar h0 h1 h2 h3 hparent

/-- Strict fifth versus sixth images, at positive cylinder density 1/16384.
    Its source predecessors are genuine, so this is a sharp gap. -/
theorem exactly_five_not_six (r t : Nat)
    (ht : 2≤t) (he : (r+t)%2=0) :
    (∃ a0 b0 a1 b1 a2 b2 a3 b3 a4 b4,
      secNext (a0,b0)=some (a1,b1) ∧
      secNext (a1,b1)=some (a2,b2) ∧
      secNext (a2,b2)=some (a3,b3) ∧
      secNext (a3,b3)=some (a4,b4) ∧
      secNext (a4,b4)=some (64*r+61,128*t+30)) ∧
    (∀ u v a b c d e f g h i j,
      ¬ (secNext (u,v)=some (a,b) ∧
         secNext (a,b)=some (c,d) ∧
         secNext (c,d)=some (e,f) ∧
         secNext (e,f)=some (g,h) ∧
         secNext (g,h)=some (i,j) ∧
         secNext (i,j)=some (64*r+61,128*t+30))) := by
  refine ⟨five_edges_exist r t ht,?_⟩
  intro u v a b c d e f g h i j ⟨h0,h1,h2,h3,h4,h5⟩
  exact six_edges_impossible r t u v a b c d e f g h i j
    ht he h0 h1 h2 h3 h4 h5

/-- All true blank-section times exclude this strict fifth/sixth image cone. -/
theorem sixth_blank_unreachable (r t time : Nat)
    (ht : 2≤t) (he : (r+t)%2=0) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (64*r+61,128*t+30) := by
  cases time with
  | zero =>
      intro hit
      simp [BB6.Agent8Section.run] at hit
  | succ n =>
      intro hit
      change (BB6.Agent8Section.run secNext n (some (5,1))).bind secNext =
        some (64*r+61,128*t+30) at hit
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [hp] at hit
      | some p =>
          rcases p with ⟨i,j⟩
          have hstep : secNext (i,j)=some (64*r+61,128*t+30) := by
            simpa [hp] using hit
          have hInv : sectionPreimageAll i j _ _ :=
            (section_preimage_all_iff i j _ _).mp hstep
          have hcopy : BB6.Agent34Broad.sectionPreimageAll i j _ _ := hInv
          obtain ⟨hi,hj⟩ := BB6.Agent34Three.only_direct
            i j (64*r+61) (128*t+30)
            (by omega) (by omega) (Or.inr (by omega)) hcopy
          have hx : i=64*(r+2*t+1)+25 := by omega
          have hy : j=64*t+14 := by omega
          rw [hx,hy] at hp
          have hpar : ((r+2*t+1)+t)%2=1 := by omega
          exact fifth_blank_unreachable (r+2*t+1) t n ht hpar hp

#print axioms exactly_five_not_six
#print axioms sixth_blank_unreachable
end BB6.Agent4Five
