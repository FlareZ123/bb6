import Agent49ExactLeftSectorSource

/-!
Complete odd-third, positive-even-first one-step failure criterion of original
Cryptids #623. This is the genuine highLevelNext source function, not a
replacement simulator. It does not classify reachable blank-root states.
-/

namespace BB6.Agent49OddSector
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49FastSpectrum
open BB6.Agent49LeftSector

theorem odd_near_none_iff_spectrum (a d : Nat)
    (hd : d%2=1) (ha : 0<a) (he : a%2=0) (hn : a≤d+3) :
    (highLevelNext (.D a d)=none) ↔
      d+4-a ∈ fastSpectrum (a-1) := by
  have haz : a≠0 := by omega
  have hfar : ¬(d%2=1 ∧ a≥d+5) := by omega
  have heven : ¬(d%2=0 ∧ a≥d+3) := by omega
  have hodd : a%2≠1 := by omega
  have hdiag : a≠d+2 := by omega
  have hs : highLevelNext (.D a d) = drainB (d+4-a) (a-1) 3 := by
    simp only [highLevelNext, if_neg haz, if_neg hfar, if_neg heven,
      if_neg hodd, if_neg hdiag, if_pos hd]
  rw [hs]
  exact drain_none_iff_fastSpectrum (d+4-a) (a-1) 3

/-- All odd-third states with positive even first counter have this
complete two-sector finite-spectrum fatality test. -/
theorem odd_even_none_iff_two_spectra (a d : Nat)
    (hd : d%2=1) (ha : 0<a) (he : a%2=0) :
    (highLevelNext (.D a d)=none) ↔
      (a≥d+5 ∧ a-d-5 ∈ fastSpectrum (d+3)) ∨
      (a≤d+3 ∧ d+4-a ∈ fastSpectrum (a-1)) := by
  by_cases hfar : d+5≤a
  · have hn : ¬(a≤d+3) := by omega
    rw [odd_left_none_iff_spectrum a d hd hfar]
    simp only [ge_iff_le, hfar, true_and, hn, false_and, or_false]
  · have hnear : a≤d+3 := by omega
    rw [odd_near_none_iff_spectrum a d hd ha he hnear]
    have hnot : ¬a≥d+5 := by omega
    simp only [ge_iff_le, hnot, false_and, hnear, true_and, false_or]

#print axioms odd_near_none_iff_spectrum
#print axioms odd_even_none_iff_two_spectra
end BB6.Agent49OddSector
