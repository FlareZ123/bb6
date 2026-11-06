import RootMod128Inverse
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29New
open BB6.Agent46

/-- For odd/even outputs with sum plus one congruent to 96 modulo 128
and first counter 5 modulo 8, both possible bounce parents violate
the authentic blank orbit's odd-right image invariant. -/
theorem sum96_forced_root_iff (x y : Nat)
    (hx : x%8=5) (hy : y%2=0)
    (hmod : (x+y+1)%128=96) (hbig : 48≤x+y+1) :
    BB6.Agent3.CReach x y ↔ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
  constructor
  · rintro ⟨time,hr⟩
    cases time with
    | zero =>
        simp [BB6.Agent8Section.run] at hr
        omega
    | succ t =>
        cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
        | none => simp [BB6.Agent8Section.run,hp] at hr
        | some p =>
            rcases p with ⟨a,k⟩
            have hedge : secNext (a,k)=some (x,y) := by
              simpa [BB6.Agent8Section.run,hp] using hr
            rcases section_sum96_mod128_inverse a k x y hx (by omega)
                (by omega) hmod hbig hedge with hdir | hbd
            · rcases hdir with ⟨ha,hk⟩
              refine ⟨t,?_⟩
              have ht : k=(y-2)/2 := by omega
              simpa only [ha,ht] using hp
            · obtain ⟨hodd,hbad,hlarge⟩ :=
                bounce_parents_forbidden x y a k hx hy hmod hbd
              cases t with
              | zero =>
                  simp [BB6.Agent8Section.run] at hp
                  omega
              | succ t' =>
                  have hi := BB6.Agent3.blank_section_odd_image t' a k hp hlarge hodd
                  omega
  · rintro ⟨t,hr⟩
    have hedge := direct_even_section x y (by omega) (by omega)
    refine ⟨t+1,?_⟩
    simpa [BB6.Agent8Section.run,hr,hedge]

#print axioms sum96_forced_root_iff
/-- An unbounded two-link exclusion for the authentic blank-rooted
Machine C section. The new valuation-five inverse rule sends any alleged
root to its direct parent; a second source-exact affine inverse lands in
the forbidden odd-right image class. -/
theorem blank_no_two_link (x y : Nat)
    (hx : x%16=13) (hmod : (x+y+1)%128=96) (hy : 34≤y) :
    ¬ BB6.Agent3.CReach x y := by
  intro h
  have hx8 : x%8=5 := by omega
  have hyeven : y%2=0 := by omega
  have h1 := (sum96_forced_root_iff x y hx8 hyeven hmod (by omega)).mp h
  let a := x+y-2
  let k := (y-2)/2
  have hprops := two_link_terminal x y hx hmod hy
  obtain ⟨hk4,hkeven,hsum,hk5,hkodd,hsum2⟩ := hprops
  have h2 : BB6.Agent3.CReach (a+k-2) ((k-2)/2) :=
    (BB6.Agent15.blank_reach_iff_affine a k hk4 hkeven hsum).mp h1
  rcases h2 with ⟨time,hr⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hr
      omega
  | succ t =>
      have hi := BB6.Agent3.blank_section_odd_image t
        (a+k-2) ((k-2)/2) hr hk5 hkodd
      omega

#print axioms blank_no_two_link
end BB6.Agent29New
