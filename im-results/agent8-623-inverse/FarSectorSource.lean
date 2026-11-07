import Agent8DrainSectorSource
import Agent49ParitySource

/-!
Certified far-sector two-step safety for the unmodified #623 source.
Assumes the first accelerated transition succeeds. Concludes that
the immediately following transition also succeeds in four extreme sectors.
These sectors are sufficient predicates, not blank-orbit closure.
-/

namespace BB6.Agent8FarSectorSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8DrainSectorSource
open BB6.Agent49ParitySource

/-- Complete original high-level source transition succeeds in the
strong far-left sector. -/
theorem farLeftSafe (b e : Nat)
    (hbig : 2*e+8 ≤ b) :
    ∃ c f, highLevelNext (.D b e) = some (.D c f) := by
  have hb : b ≠ 0 := by omega
  by_cases he : e % 2 = 1
  · have hbranch : e%2=1 ∧ b≥e+5 := ⟨he,by omega⟩
    have harg : e+3 ≤ b-e-5 := by omega
    have hbudget : e+3 ≤ ternaryOnes (b-e-5) :=
      Nat.le_trans harg (ternaryOnes_ge _)
    obtain ⟨c,f,hdr⟩ := drainB_safe_ones (e+3) (b-e-5) 5 hbudget
    have hstep : highLevelNext (.D b e) = drainB (b-e-5) (e+3) 5 := by
      simp only [highLevelNext, if_neg hb, if_pos hbranch]
    exact ⟨c,f,hstep.trans hdr⟩
  · have hpar : e%2=0 := by omega
    have hnot : ¬(e%2=1 ∧ b≥e+5) := by omega
    have hbranch : e%2=0 ∧ b≥e+3 := ⟨hpar,by omega⟩
    have harg : e+2 ≤ b-e-2 := by omega
    have hbudget : e+2 ≤ ternaryOnes (b-e-2) :=
      Nat.le_trans harg (ternaryOnes_ge _)
    obtain ⟨c,f,hdr⟩ := drainB_safe_ones (e+2) (b-e-2) 2 hbudget
    have hstep : highLevelNext (.D b e) = drainB (b-e-2) (e+2) 2 := by
      simp only [highLevelNext, if_neg hb, if_neg hnot, if_pos hbranch]
    exact ⟨c,f,hstep.trans hdr⟩

/-- Strongly left-dominated state, odd second counter. -/
theorem odd_far_left_two_step (a d aa dd : Nat)
    (ha : 0<a) (he : d%2=1) (hfar : 37*d+131 ≤ a)
    (hs : highLevelNext (.D a d) = some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd) = some (.D bb ee) := by
  have h0 : a ≠ 0 := by omega
  have h1 : d%2=1 ∧ a≥d+5 := ⟨he,by omega⟩
  simp only [highLevelNext, if_neg h0, if_pos h1] at hs
  have hcone := drainB_left_sector (a-d-5) (d+3) 5 aa dd hs
    (by omega)
  exact farLeftSafe aa dd hcone

/-- Strongly left-dominated state, even second counter. -/
theorem even_far_left_two_step (a d aa dd : Nat)
    (ha : 0<a) (he : d%2=0) (hfar : 37*d+86 ≤ a)
    (hs : highLevelNext (.D a d) = some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd) = some (.D bb ee) := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : d%2=0 ∧ a≥d+3 := ⟨he,by omega⟩
  simp only [highLevelNext, if_neg h0, if_neg h1, if_pos h2] at hs
  have hcone := drainB_left_sector (a-d-2) (d+2) 2 aa dd hs
    (by omega)
  exact farLeftSafe aa dd hcone

/-- Strongly right-dominated state, odd second counter. -/
theorem odd_far_right_two_step (a d aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=1) (hfar : 40*a ≤ d)
    (hs : highLevelNext (.D a d) = some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd) = some (.D bb ee) := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2 ≠ 1 := by omega
  have h4 : a ≠ d+2 := by omega
  simp only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
    if_neg h3, if_neg h4, if_pos hd] at hs
  have hcone := drainB_left_sector (d+4-a) (a-1) 3 aa dd hs
    (by omega)
  exact farLeftSafe aa dd hcone

/-- Strongly right-dominated state, even second counter. -/
theorem even_far_right_two_step (a d aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=0) (hfar : 40*a ≤ d)
    (hs : highLevelNext (.D a d) = some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd) = some (.D bb ee) := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2 ≠ 1 := by omega
  have h4 : a ≠ d+2 := by omega
  have h5 : d%2 ≠ 1 := by omega
  simp only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
    if_neg h3, if_neg h4, if_neg h5] at hs
  cases hev : evalA (d+1-a) a (2*a+5) with
  | none => simp [hev] at hs
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [hev, Option.bind_some] at hs
    have hh := evalA_first_lower (d+1-a) a (2*a+5) a1 b1 d1 hev
    have hi := evalA_third_upper (d+1-a) a (2*a+5) a1 b1 d1 hev
    have hq := BB6.Agent8DrainLogDepthSource.evalA_second_le_quotient
      (d+1-a) a (2*a+5) a1 b1 d1 hev
    have hcone : 2*d1+36*b1+8 ≤ a1 := by omega
    have hscone := drainB_left_sector a1 b1 d1 aa dd hs hcone
    exact farLeftSafe aa dd hscone

#print axioms farLeftSafe
#print axioms odd_far_left_two_step
#print axioms even_far_left_two_step
#print axioms odd_far_right_two_step
#print axioms even_far_right_two_step
end BB6.Agent8FarSectorSource
