import Agent8SharpMass21LowSource
namespace BB6.Agent8SharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

theorem next_even_positive_mass14 (a d aa dd : Nat)
    (heven : a%2=0) (hlarge : 6≤a) (hdpos : 0<d) (hmass :16≤a+d)
    (hstep : next (.D a d) = some (.D aa dd)) :
    a+d+14 ≤ aa+dd := by
  by_cases hd2 : d%2=0
  · exact next_even_six_even_d_mass14 a d aa dd heven hlarge hdpos hd2 hstep
  · have hodd : d%2=1 := by omega
    have hex : ¬ (a=6 ∧ d=3) := by omega
    exact next_even_six_odd_d_mass14 a d aa dd heven hlarge hdpos hodd hex hstep

/-- A sharp 21-unit bound over every surviving two-step high-mass even sector. -/
theorem two_step_gain_21 (a d b e c f : Nat)
    (ha : a%2=0) (hb : b%2=0) (hmass : 16≤a+d)
    (h1 : next (.D a d) = some (.D b e))
    (h2 : next (.D b e) = some (.D c f))
    (h7first : a+d+7≤b+e) (h7second : b+e+7≤c+f) :
    a+d+21≤c+f := by
  by_cases hlarge : 6≤a
  · by_cases hzero : d=0
    · subst d
      have hx := high_zero_exact a (by omega)
      rw [hx] at h1
      cases h1
      have hh := next_even_positive_mass14 (a-4) 14 c f (by omega)
        (by omega) (by omega) (by omega) h2
      omega
    · have hh := next_even_positive_mass14 a d b e ha hlarge (by omega)
        hmass h1
      omega
  · have hsmall : a≤4 := by omega
    have hesc := small_even_escape_seven a d b e ha hsmall hmass h1
    have hh := next_even_positive_mass14 b e c f hb hesc.1 (by omega)
      (by omega) h2
    omega

#print axioms next_even_positive_mass14
#print axioms two_step_gain_21
end BB6.Agent8SharpSource
