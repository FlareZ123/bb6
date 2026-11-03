import Agent8SharpMass14OddFiveSource
namespace BB6.Agent8SharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

theorem next_even_six_odd_d_mass14 (a d aa dd : Nat)
    (heven : a%2=0) (hlarge : 6≤a) (hdpos : 0<d)
    (hdodd : d%2=1) (hex : ¬ (a=6 ∧ d=3))
    (hstep : next (.D a d) = some (.D aa dd)) :
    a+d+14≤aa+dd := by
  simp only [next,highLevelNext] at hstep
  have hn : a≠0 := by omega
  simp only [if_neg hn] at hstep
  by_cases h1 : d%2=1 ∧ a≥d+5
  · simp only [if_pos h1] at hstep
    by_cases ha0 : a-d-5=0
    · have hm:=drainB_mass_even_big_zero (d+3) (by omega) (by omega) 5 aa dd
        (by simpa only [ha0] using hstep)
      omega
    · have hm:=drainB_mass_even_big_pos10 (d+3) (by omega) (by omega)
        (a-d-5) 5 aa dd (by omega) hstep
      omega
  · simp only [if_neg h1] at hstep
    have h2 : ¬ (d%2=0 ∧ a≥d+3) := by omega
    simp only [if_neg h2] at hstep
    have hp : a%2≠1 := by omega
    simp only [if_neg hp] at hstep
    have h4 : a≠d+2 := by omega
    simp only [if_neg h4] at hstep
    simp only [if_pos hdodd] at hstep
    by_cases ha8 : 8≤a
    · have hm:=drainB_mass_odd_big11 (a-1) (by omega) (by omega)
        (d+4-a) 3 aa dd (by omega) hstep
      omega
    · have ha6 : a=6 := by omega
      have hd5 : 5≤d := by omega
      subst a
      have harg : d+4-6=d-2 := by omega
      rw [harg,drain_five_exact (d-2) (by omega)] at hstep
      cases hstep
      omega

#print axioms next_even_six_odd_d_mass14
end BB6.Agent8SharpSource
