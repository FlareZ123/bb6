import Agent22RobustBand
import Agent49SharpSpectrumCapacitySource

/-!
The original-machine source correspondence for the separately kernel-checked
ternary band theorem. The only imported semantic bridge is Agent49's exact
original-Cryptids drain_none_iff_badAll theorem.
No blank-origin reachability is asserted.
-/

namespace BB6.Agent22RobustBandSource
open BB6Robust
open BB6.Agent49FullSpectrum
open BB6.Agent49Capacity
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- The independently proved total recursive predicate agrees at every input
with Agent49's exact source-authenticated fatality interpreter. -/
theorem bad_source_eq (b : Nat) : ∀ a, bad a b = badAll a b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      intro a
      rw [bad, badAll]
      by_cases hz : b=0
      · simp [hz]
      · simp only [if_neg hz]
        by_cases h0 : b%3=0
        · simp only [if_pos h0]
          exact ih (b/3-1) (by omega) (a+1)
        · simp only [if_neg h0]
          by_cases h1 : b%3=1
          · simp only [if_pos h1]
            by_cases ha : a=0
            · simp [ha]
            · simp only [if_neg ha]
              exact ih (b/3) (by omega) (a-1)
          · simp only [if_neg h1]
            by_cases ha : a=0
            · simp only [if_pos ha]
              exact ih (b/3) (by omega) 0
            · simp only [if_neg ha]
              exact ih (b/3+1) (by omega) (a-1)

theorem boundary_source_eq (n : Nat) : u n = boundary n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [u, boundary]
      omega

/-- All original-source drains in an exponential neighbourhood of the
ternary-ones boundary fail regardless of their third-counter value. -/
theorem original_drain_fatal_band (k n a e d : Nat)
    (hn : a+2*k+2≤n) (he : e≤3^k) :
    drainB a (boundary n+e) d = none := by
  apply (drain_none_iff_badAll a (boundary n+e) d).2
  rw [←boundary_source_eq n]
  rw [←bad_source_eq (u n+e) a]
  exact band_fatal k n a e hn he

/-- A fully explicit infinite linear subfamily with first counter three. -/
theorem original_linear_family (q d : Nat) (hq : 1≤q) :
    drainB 3 (boundary (2*q+5)+(8*q+26)) d = none := by
  apply (drain_none_iff_badAll _ _ d).2
  rw [←boundary_source_eq (2*q+5)]
  rw [←bad_source_eq (u (2*q+5)+(8*q+26)) 3]
  exact linear_band_fatal q hq

/-- Exact maximal consecutive fatal band in the unmodified original B-drain.
The first surviving block follows at offset escape r, for all r,a,d. -/
theorem original_sharp_initial_band (r a d : Nat) :
    (∀ e : Nat, e < escape r →
      drainB a (boundary (a+r)+e) d = none) ∧
    drainB a (boundary (a+r)+escape r) d ≠ none := by
  constructor
  · intro e he
    apply (drain_none_iff_badAll a (boundary (a+r)+e) d).2
    rw [←boundary_source_eq (a+r)]
    rw [←bad_source_eq (u (a+r)+e) a]
    exact (exact_initial_band r a).1 e he
  · intro hbad
    have hh := (drain_none_iff_badAll a
      (boundary (a+r)+escape r) d).1 hbad
    rw [←boundary_source_eq (a+r)] at hh
    rw [←bad_source_eq (u (a+r)+escape r) a] at hh
    have hs := (exact_initial_band r a).2
    rw [hs] at hh
    cases hh


/-- The immediately preceding block is always a surviving B-drain. -/
theorem original_left_neighbor_survives (n a d : Nat) :
    drainB a (boundary (n+1)-1) d ≠ none := by
  intro hbad
  have hh := (drain_none_iff_badAll a (boundary (n+1)-1) d).1 hbad
  rw [←boundary_source_eq (n+1)] at hh
  rw [←bad_source_eq (u (n+1)-1) a] at hh
  have hs := left_neighbor_safe n a
  rw [hs] at hh
  cases hh

/-- All original source odd/far-left sectors whose B-block belongs to the
sharp fatal corridor are forced to fail in the next high-level evaluation. -/
theorem odd_far_left_sharp_fatal (r a d e : Nat)
    (hd : d%2=1) (hfar : d+5≤a)
    (hblock : d+3=boundary (a-d-5+r)+e)
    (he : e<escape r) :
    highLevelNext (.D a d) = none := by
  have ha : a≠0 := by omega
  have hc : d%2=1 ∧ a≥d+5 := ⟨hd,hfar⟩
  have hs := (original_sharp_initial_band r (a-d-5) 5).1 e he
  rw [←hblock] at hs
  simpa only [highLevelNext,if_neg ha,if_pos hc] using hs

/-- Same exact sharp corridor in original even/far-left sectors. -/
theorem even_far_left_sharp_fatal (r a d e : Nat)
    (hd : d%2=0) (hfar : d+3≤a)
    (hblock : d+2=boundary (a-d-2+r)+e)
    (he : e<escape r) :
    highLevelNext (.D a d) = none := by
  have ha : a≠0 := by omega
  have hodd : ¬(d%2=1 ∧ a≥d+5) := by omega
  have hc : d%2=0 ∧ a≥d+3 := ⟨hd,hfar⟩
  have hs := (original_sharp_initial_band r (a-d-2) 2).1 e he
  rw [←hblock] at hs
  simpa only [highLevelNext,if_neg ha,if_neg hodd,if_pos hc] using hs

#print axioms original_left_neighbor_survives
#print axioms odd_far_left_sharp_fatal
#print axioms even_far_left_sharp_fatal

#print axioms original_sharp_initial_band

#print axioms bad_source_eq
#print axioms original_drain_fatal_band
#print axioms original_linear_family
end BB6.Agent22RobustBandSource
