import Agent49SmallOutputSource
import Agent8SharpMass14OddSource

/-!
All-input conditional 27-unit two-step growth for the high positive sector
of Cryptids #623: even a >=6, positive d, and a+d >=100. Every dependency
imports the unchanged original highLevelNext. Unlike a finite simulation,
the theorem quantifies over all natural coordinates and successor states.
It does not by itself handle a=0,2,4 or d=0; blank-root conclusions must
address those sectors separately.
-/

namespace BB6.Agent49TwoStep27HighSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

/-- Combine the original-source even/odd 14-unit theorems. -/
theorem next_even_positive_mass14 (a d aa dd : Nat)
    (heven : a%2=0) (hlarge : 6≤a) (hdpos : 0<d)
    (hmass : 16≤a+d)
    (hstep : next (.D a d)=some (.D aa dd)) :
    a+d+14≤aa+dd := by
  by_cases hd2 : d%2=0
  · exact BB6.Agent8SharpSource.next_even_six_even_d_mass14
      a d aa dd heven hlarge hdpos hd2 hstep
  · have hodd : d%2=1 := by omega
    have hex : ¬(a=6 ∧ d=3) := by omega
    exact BB6.Agent8SharpSource.next_even_six_odd_d_mass14
      a d aa dd heven hlarge hdpos hodd hex hstep

theorem high_even_two_step_gain27 (a d b e c f : Nat)
    (ha : a%2=0) (ha6 : 6≤a) (hd : 0<d) (hm : 100≤a+d)
    (h1 : next (.D a d)=some (.D b e))
    (h2 : next (.D b e)=some (.D c f)) :
    a+d+27≤c+f := by
  have hb : b%2=0 := BB6.Agent49ParitySource.next_preserves_even a d b e ha h1
  have h7 := BB6.Agent49ParitySource.next_strict_mass b e c f h2
  by_cases hsmall : b≤4
  · have h20 := BB6.Agent49SmallOutputSource.next_small_first_gain20
      a d b e ha ha6 hd hm hsmall h1
    omega
  · have hb6 : 6≤b := by omega
    have he2 := BB6.Agent49SmallOutputSource.next_output_second_two a d b e h1
    have h14a := next_even_positive_mass14
      a d b e ha ha6 hd (by omega) h1
    have h14b := next_even_positive_mass14
      b e c f hb hb6 (by omega) (by omega) h2
    omega

#print axioms high_even_two_step_gain27
end BB6.Agent49TwoStep27HighSource
