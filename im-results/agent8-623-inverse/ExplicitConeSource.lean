import Agent8SharpCounterBoundsSource
import Agent8RightTailAllDepthSource

/-!
Explicit all-finite-depth safe cones for original-source Cryptids #623.
Unlike the pointwise eventual-tail theorem, each guaranteed region has an
explicit linear-in-the-opposite-counter threshold for every chosen depth.
-/
namespace BB6.Agent8ExplicitConeSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent8UpperCounterSource
open BB6.Agent8RightTailTwoStepSource
open BB6.Agent8RightTailAllDepthSource

/-- Uniform sharp-derived bounds for every completed far-left return. -/
theorem farLeftCoordinateBounds (a d b e : Nat)
    (hwide : 2*d+8≤a)
    (hnext : highLevelNext (.D a d) = some (.D b e)) :
    a≤b+2*d+8 ∧ e≤7*d+26 := by
  have h0 : a≠0 := by omega
  by_cases hd : d%2=1
  · have hb : d%2=1 ∧ a≥d+5 := ⟨hd,by omega⟩
    have hr : drainB (a-d-5) (d+3) 5 = some (.D b e) := by
      simpa only [highLevelNext, if_neg h0, if_pos hb] using hnext
    have hp := drainB_sharp_bounds (d+3) (a-d-5) 5 b e hr
    constructor <;> omega
  · have hpar : d%2=0 := by omega
    have hnot : ¬(d%2=1 ∧ a≥d+5) := by omega
    have hb : d%2=0 ∧ a≥d+3 := ⟨hpar,by omega⟩
    have hr : drainB (a-d-2) (d+2) 2 = some (.D b e) := by
      simpa only [highLevelNext, if_neg h0, if_neg hnot, if_pos hb] using hnext
    have hp := drainB_sharp_bounds (d+2) (a-d-2) 2 b e hr
    constructor <;> omega

/-- An explicit two-step safe cone with no input first-counter parity
assumption; its numerical slope follows the sharp drain bounds. -/
theorem farLeftTwoStepWide (a d : Nat)
    (hwide : 16*d+68≤a) :
    ∃ b e c f,
      highLevelNext (.D a d)=some (.D b e) ∧
      highLevelNext (.D b e)=some (.D c f) := by
  have hbase : 2*d+8≤a := by omega
  obtain ⟨b,e,hfirst⟩ := farLeftSafe a d hbase
  have hcoord := farLeftCoordinateBounds a d b e hbase hfirst
  have hnextsafe : 2*e+8≤b := by omega
  obtain ⟨c,f,hsecond⟩ := farLeftSafe b e hnextsafe
  exact ⟨b,e,c,f,hfirst,hsecond⟩

/-- Universal linear coefficients for an arbitrary requested number of
complete accelerated sections, irrespective of the second-counter parity. -/
def coneSlope : Nat → Nat
  | 0 => 0
  | n+1 => 7*coneSlope n+2

def coneOffset : Nat → Nat
  | 0 => 0
  | n+1 => coneOffset n+26*coneSlope n+8

theorem leftExplicitAllDepth (n : Nat) :
    ∀ a d, coneSlope n*d+coneOffset n≤a → Continues n (.D a d) := by
  induction n with
  | zero =>
      intro a d h
      trivial
  | succ n ih =>
      intro a d hwide
      have hbase : 2*d+8≤a := by
        have h := hwide
        simp only [coneSlope,coneOffset, Nat.add_mul] at h
        omega
      obtain ⟨b,e,hfirst⟩ := farLeftSafe a d hbase
      obtain ⟨hl,hu⟩ := farLeftCoordinateBounds a d b e hbase hfirst
      have hmul : coneSlope n*e≤coneSlope n*(7*d+26) :=
        Nat.mul_le_mul_left _ hu
      have hthreshold : coneSlope n*(7*d+26)+coneOffset n+2*d+8≤a := by
        calc
          _ = (7*coneSlope n+2)*d+
                (coneOffset n+26*coneSlope n+8) := by
                simp only [Nat.mul_add,Nat.add_mul]
                ac_rfl
          _ = coneSlope (n+1)*d+coneOffset (n+1) := by
                simp only [coneSlope,coneOffset]
          _ ≤ a := hwide
      have hnext : coneSlope n*e+coneOffset n≤b := by omega
      change ∃ s, highLevelNext (.D a d)=some s ∧ Continues n s
      exact ⟨.D b e,hfirst,ih b e hnext⟩

/-- Every strong right-side section with positive even first counter
successfully completes its next source transition. -/
theorem farRightOneSafe (a d : Nat)
    (ha : 0<a) (he : a%2=0) (hwide : 2*a+2≤d) :
    ∃b e, highLevelNext (.D a d) = some (.D b e) := by
  have h0 : a≠0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2≠1 := by omega
  have h4 : a≠d+2 := by omega
  by_cases hd : d%2=1
  · have hbudget : a-1≤ternaryOnes (d+4-a) := by
      have hg := ternaryOnes_ge (d+4-a)
      omega
    obtain ⟨b,e,hdr⟩ := drainB_safe_ones (a-1) (d+4-a) 3 hbudget
    have hnext : highLevelNext (.D a d) = drainB (d+4-a) (a-1) 3 := by
      simp only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
        if_neg h3, if_neg h4, if_pos hd]
    exact ⟨b,e,hnext.trans hdr⟩
  · have hpar : d%2=0 := by omega
    have hnot : d%2≠1 := by omega
    have hbudget : a<ternaryOnes (d+1-a) := by
      have hg := ternaryOnes_ge (d+1-a)
      omega
    obtain ⟨aa,bb,dd,hev,hb⟩ :=
      evalA_ones_budget (d+1-a) a (2*a+5) hbudget
    obtain ⟨b,e,hdr⟩ := drainB_safe_ones bb aa dd hb
    have hnext : highLevelNext (.D a d) =
        (evalA (d+1-a) a (2*a+5)).bind fun p => drainB p.1 p.2.1 p.2.2 := by
      simp only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
        if_neg h3, if_neg h4, if_neg hnot]
    refine ⟨b,e,?_⟩
    rw [hnext,hev]
    exact hdr

/-- The first return of a strong right-side state lies in a controlled
linear wedge, regardless of odd or even second counter. -/
theorem farRightCoordinateBounds (a d b e : Nat)
    (ha : 0<a) (he : a%2=0) (hwide : 2*a+2≤d)
    (hnext : highLevelNext (.D a d) = some (.D b e)) :
    d≤b+2*a ∧ e≤7*a+7 := by
  have h0 : a≠0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2≠1 := by omega
  have h4 : a≠d+2 := by omega
  by_cases hd : d%2=1
  · have hr : drainB (d+4-a) (a-1) 3 = some (.D b e) := by
      simpa only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
        if_neg h3, if_neg h4, if_pos hd] using hnext
    have hp := drainB_sharp_bounds (a-1) (d+4-a) 3 b e hr
    constructor <;> omega
  · have hnot : d%2≠1 := by omega
    have hstep : (evalA (d+1-a) a (2*a+5)).bind
        (fun p => drainB p.1 p.2.1 p.2.2) = some (.D b e) := by
      simpa only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
        if_neg h3, if_neg h4, if_neg hnot] using hnext
    cases hev : evalA (d+1-a) a (2*a+5) with
    | none => simp [hev] at hstep
    | some p =>
        rcases p with ⟨aa,bb,dd⟩
        simp only [hev,Option.bind_some] at hstep
        have hp := evalA_joint_bounds (d+1-a) a (2*a+5) aa bb dd hev
        have hr := drainB_sharp_bounds bb aa dd b e hstep
        constructor <;> omega

/-- Explicit strong-right cone for any finite depth (one additional step
moves into the explicit far-left cone). -/
theorem rightExplicitAllDepth (n a d : Nat)
    (ha : 0<a) (he : a%2=0)
    (hwide : (7*coneSlope n+2)*a+
      (7*coneSlope n+coneOffset n+2)≤d) :
    Continues (n+1) (.D a d) := by
  have hbase : 2*a+2≤d := by
    have h := hwide
    simp only [Nat.add_mul] at h
    omega
  obtain ⟨b,e,hfirst⟩ := farRightOneSafe a d ha he hbase
  obtain ⟨hl,hu⟩ := farRightCoordinateBounds a d b e ha he hbase hfirst
  have hmul : coneSlope n*e≤coneSlope n*(7*a+7) :=
    Nat.mul_le_mul_left _ hu
  have hthreshold : coneSlope n*(7*a+7)+coneOffset n+2*a+2≤d := by
    calc
      _ = (7*coneSlope n+2)*a+(7*coneSlope n+coneOffset n+2) := by
        simp only [Nat.mul_add,Nat.add_mul]
        rw [Nat.mul_comm (coneSlope n) 7]
        ac_rfl
      _ ≤d := hwide
  have hnext : coneSlope n*e+coneOffset n≤b := by omega
  change ∃ s, highLevelNext (.D a d)=some s ∧ Continues n s
  exact ⟨.D b e,hfirst,leftExplicitAllDepth n b e hnext⟩

#print axioms farRightOneSafe
#print axioms farRightCoordinateBounds
#print axioms rightExplicitAllDepth
#print axioms farLeftCoordinateBounds
#print axioms farLeftTwoStepWide
#print axioms leftExplicitAllDepth
end BB6.Agent8ExplicitConeSource
