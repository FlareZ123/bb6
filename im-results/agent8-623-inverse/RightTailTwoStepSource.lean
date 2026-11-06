import Agent49TernaryShiftSource

/-!
An all-natural right-ray two-step safety lemma for #623, importing the
unmodified DeepMind high-level transition through Agent49's certified source
module. This concerns synthetic source section states, with no blank-root claim.
-/

namespace BB6.Agent8RightTailTwoStepSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49TernaryShiftSource

/-- Every even-first-counter far-left state above a universal linear
threshold survives its next complete accelerated transition. -/
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
      simp [highLevelNext,hb,hbranch]
    exact ⟨c,f,hstep.trans hdr⟩
  · have hpar : e%2=0 := by omega
    have hnot : ¬(e%2=1 ∧ b≥e+5) := by omega
    have hbranch : e%2=0 ∧ b≥e+3 := ⟨hpar,by omega⟩
    have harg : e+2 ≤ b-e-2 := by omega
    have hbudget : e+2 ≤ ternaryOnes (b-e-2) :=
      Nat.le_trans harg (ternaryOnes_ge _)
    obtain ⟨c,f,hdr⟩ := drainB_safe_ones (e+2) (b-e-2) 2 hbudget
    have hstep : highLevelNext (.D b e) = drainB (b-e-2) (e+2) 2 := by
      simp [highLevelNext,hb,hnot,hbranch]
    exact ⟨c,f,hstep.trans hdr⟩

/-- On an odd right ray in the source's certified translation domain,
all sufficiently far translates survive two complete transitions. -/
theorem rightOddTwoStepTail (a d : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=1) (hside : a≤d)
    (hbudget : a-1≤ternaryOnes (d+4-a)) :
    ∃ N, ∀ t ≥ N, ∃ b e c f,
      highLevelNext (.D a (d+2*t)) = some (.D b e) ∧
      highLevelNext (.D b e) = some (.D c f) := by
  obtain ⟨b0,e0,hdr⟩ := drainB_safe_ones (a-1) (d+4-a) 3 hbudget
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2 ≠ 1 := by omega
  have h4 : a ≠ d+2 := by omega
  have hbase : highLevelNext (.D a d) = some (.D b0 e0) := by
    simpa only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_pos hd] using hdr
  refine ⟨e0+4, ?_⟩
  intro t ht
  have hshift := highLevel_right_odd_shift_ones a d t ha he hd hside hbudget
  have hfirst : highLevelNext (.D a (d+2*t)) = some (.D (b0+2*t) e0) := by
    rw [hshift,hbase]
    rfl
  have hbig : 2*e0+8 ≤ b0+2*t := by omega
  obtain ⟨c,f,hsecond⟩ := farLeftSafe (b0+2*t) e0 hbig
  exact ⟨b0+2*t,e0,c,f,hfirst,hsecond⟩

/-- The corresponding even right ray. -/
theorem rightEvenTwoStepTail (a d : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=0) (hside : a≤d)
    (hbudget : a<ternaryOnes (d+1-a)) :
    ∃ N, ∀ t ≥ N, ∃ b e c f,
      highLevelNext (.D a (d+2*t)) = some (.D b e) ∧
      highLevelNext (.D b e) = some (.D c f) := by
  obtain ⟨a1,b1,d1,hev,hb1⟩ :=
    evalA_ones_budget (d+1-a) a (2*a+5) hbudget
  obtain ⟨b0,e0,hdr⟩ := drainB_safe_ones b1 a1 d1 hb1
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2 ≠ 1 := by omega
  have h4 : a ≠ d+2 := by omega
  have h5 : d%2 ≠ 1 := by omega
  have hbase : highLevelNext (.D a d) = some (.D b0 e0) := by
    simpa only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_neg h5, hev, Option.bind_some] using hdr
  refine ⟨e0+4, ?_⟩
  intro t ht
  have hshift := highLevel_right_even_shift_ones a d t ha he hd hside hbudget
  have hfirst : highLevelNext (.D a (d+2*t)) = some (.D (b0+2*t) e0) := by
    rw [hshift,hbase]
    rfl
  have hbig : 2*e0+8 ≤ b0+2*t := by omega
  obtain ⟨c,f,hsecond⟩ := farLeftSafe (b0+2*t) e0 hbig
  exact ⟨b0+2*t,e0,c,f,hfirst,hsecond⟩

#print axioms farLeftSafe
#print axioms rightOddTwoStepTail
#print axioms rightEvenTwoStepTail

end BB6.Agent8RightTailTwoStepSource
