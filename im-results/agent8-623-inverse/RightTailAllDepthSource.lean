import Agent8RightTailTwoStepSource

/-!
Pointwise all-finite-depth safe tails for the exact source #623 high-level map.
For each requested finite number of consecutive accelerator steps, there is
an input counter threshold that guarantees that many successful steps.
The threshold depends on the requested depth; no uniform infinite orbit or
blank-start nonhalting statement follows.
-/

namespace BB6.Agent8RightTailAllDepthSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49TernaryShiftSource
open BB6.Agent8RightTailTwoStepSource

/-- A source section admits n complete, successful accelerated transitions. -/
def Continues : Nat → HighLevelState → Prop
  | 0, _ => True
  | n+1, s => ∃s', highLevelNext s = some s' ∧ Continues n s'

/-- For every fixed second counter and every finite depth, sufficiently
large first counters guarantee that many complete accelerated transitions. -/
theorem leftTailAllDepth (n : Nat) :
    ∀ e, ∃ B, ∀ b ≥ B, Continues n (.D b e) := by
  induction n with
  | zero =>
    intro e
    exact ⟨0, by intro b hb; trivial⟩
  | succ n ih =>
    intro e
    let base := 2*e+8
    obtain ⟨b0,e0,hbase⟩ := farLeftSafe base e (by dsimp [base]; omega)
    obtain ⟨N,hN⟩ := ih e0
    refine ⟨base+N, ?_⟩
    intro b hb
    let t := b-base
    have hdecomp : base+t=b := by dsimp [t]; omega
    have hshift : highLevelNext (.D (base+t) e) =
        (highLevelNext (.D base e)).map (liftFirstState t) := by
      by_cases he : e%2=1
      · have hb : e+5≤base := by dsimp [base]; omega
        have hbudget : e+3≤ternaryOnes (base-e-5) := by
          have hg := ternaryOnes_ge (base-e-5)
          dsimp [base] at *
          omega
        exact highLevel_far_odd_shift_ones base e t he hb hbudget
      · have hpar : e%2=0 := by omega
        have hb : e+3≤base := by dsimp [base]; omega
        have hbudget : e+2≤ternaryOnes (base-e-2) := by
          have hg := ternaryOnes_ge (base-e-2)
          dsimp [base] at *
          omega
        exact highLevel_far_even_shift_ones base e t hpar hb hbudget
    have hstep : highLevelNext (.D b e) = some (.D (b0+t) e0) := by
      rw [←hdecomp,hshift,hbase]
      rfl
    have hn : N≤b0+t := by dsimp [t]; omega
    exact ⟨.D (b0+t) e0,hstep,hN (b0+t) hn⟩

/-- A sufficient affine return with shifted first counter transfers every
finite tail property to all sufficiently large ray parameters. -/
theorem rightShiftAllDepth (n a d b0 e0 : Nat)
    (hbase : highLevelNext (.D a d) = some (.D b0 e0))
    (hshift : ∀t, highLevelNext (.D a (d+2*t)) =
      (highLevelNext (.D a d)).map (liftFirstState (2*t))) :
    ∃N, ∀t≥N, Continues (n+1) (.D a (d+2*t)) := by
  obtain ⟨B,hB⟩ := leftTailAllDepth n e0
  refine ⟨B,?_⟩
  intro t ht
  have hs : highLevelNext (.D a (d+2*t)) = some (.D (b0+2*t) e0) := by
    rw [hshift,hbase]
    rfl
  have hb : B≤b0+2*t := by omega
  exact ⟨.D (b0+2*t) e0, hs, hB (b0+2*t) hb⟩

/-- Every complete source right-odd ray has pointwise all-finite-depth
survival in its far tail. -/
theorem rightOddAllDepth (n a d : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=1) (hside : a≤d)
    (hbudget : a-1≤ternaryOnes (d+4-a)) :
    ∃N,∀t≥N, Continues (n+1) (.D a (d+2*t)) := by
  obtain ⟨b0,e0,hdr⟩ := drainB_safe_ones (a-1) (d+4-a) 3 hbudget
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2 ≠ 1 := by omega
  have h4 : a ≠ d+2 := by omega
  have hbase : highLevelNext (.D a d) = some (.D b0 e0) := by
    simpa only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_pos hd] using hdr
  exact rightShiftAllDepth n a d b0 e0 hbase
    (fun t => highLevel_right_odd_shift_ones a d t ha he hd hside hbudget)

/-- Every complete source right-even ray has pointwise all-finite-depth
survival in its far tail. -/
theorem rightEvenAllDepth (n a d : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=0) (hside : a≤d)
    (hbudget : a<ternaryOnes (d+1-a)) :
    ∃N,∀t≥N, Continues (n+1) (.D a (d+2*t)) := by
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
  exact rightShiftAllDepth n a d b0 e0 hbase
    (fun t => highLevel_right_even_shift_ones a d t ha he hd hside hbudget)

/-- For any desired finite depth, all sufficiently large second counters
at a fixed positive even first counter admit that many complete transitions. -/
theorem evenFirstAllDepth (n a : Nat) (ha : 0<a) (he : a%2=0) :
    ∃D,∀d≥D, Continues (n+1) (.D a d) := by
  have hOddBudget : a-1≤ternaryOnes ((2*a+1)+4-a) := by
    have hg := ternaryOnes_ge ((2*a+1)+4-a)
    omega
  obtain ⟨No,hNo⟩ := rightOddAllDepth n a (2*a+1) ha he
    (by omega) (by omega) hOddBudget
  have hEvenBudget : a<ternaryOnes ((2*a+2)+1-a) := by
    have hg := ternaryOnes_ge ((2*a+2)+1-a)
    omega
  obtain ⟨Ne,hNe⟩ := rightEvenAllDepth n a (2*a+2) ha he
    (by omega) (by omega) hEvenBudget
  refine ⟨2*a+2+2*(No+Ne),?_⟩
  intro d hd
  by_cases hpar : d%2=1
  · let t := (d-(2*a+1))/2
    have hdecomp : d = (2*a+1)+2*t := by dsimp [t]; omega
    have ht : No≤t := by dsimp [t]; omega
    simpa [hdecomp] using hNo t ht
  · have hpar0 : d%2=0 := by omega
    let t := (d-(2*a+2))/2
    have hdecomp : d = (2*a+2)+2*t := by dsimp [t]; omega
    have ht : Ne≤t := by dsimp [t]; omega
    simpa [hdecomp] using hNe t ht

#print axioms leftTailAllDepth
#print axioms rightOddAllDepth
#print axioms rightEvenAllDepth
#print axioms evenFirstAllDepth
end BB6.Agent8RightTailAllDepthSource
