import Agent49TernaryBufferSource

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# No uniform quadratic ratio-four gap invariant on the #623 affine cone

For canonical gap
  g(a,d) = |a-4d| if a>=d, and |d-4a| otherwise,
and smaller counter m=min(a,d), no fixed positive constant C makes
g(a,d)^2 >= C*m forward-invariant, even on the strong old affine cone.

The source-authentic family is
  D(2,d) -> D(d,9),  d even and d>=36.
Both endpoints lie in the old affine cone (hence in the exact four-sector
newAffineCone). Their gap ratios are
  g(2,d)^2 / 2 = (d-8)^2/2,
  g(d,9)^2 / 9 = (d-36)^2/9.
Taking d=36+2*floor(sqrt(C)) makes the first at least C and the second
strictly less than C. Thus the 20k root's observed g^2/m >= 17 tail cannot
be promoted to a state-local cone invariant; any proof of that root property
must retain genuine root history.
-/

namespace BB6.Agent27QuadraticGap

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49TernaryBufferSource

/-- Natural absolute difference. -/
def natAbsDiff (x y : Nat) : Nat :=
  if x ≤ y then y-x else x-y

/-- Absolute canonical ratio-four gap, with the root scan's sector convention. -/
def canonicalGap (a d : Nat) : Nat :=
  if a ≥ d then natAbsDiff a (4*d) else natAbsDiff d (4*a)

/-- The smaller counter, written explicitly to keep the ratio convention visible. -/
def smallerCounter (a d : Nat) : Nat :=
  if a ≤ d then a else d

/-- The old linear affine cone is contained in the exact four-sector cone. -/
theorem oldAffineCone_subset_newAffineCone (a d : Nat)
    (h : oldAffineCone a d) : newAffineCone a d := by
  rcases h with hl | hl | hr | hr
  · rcases hl with ⟨hd, hgap⟩
    refine Or.inl ⟨hd, ?_, ?_⟩
    · omega
    · have harg : d+3 ≤ a-d-5 := by omega
      exact Nat.le_trans harg (ternaryOnes_ge _)
  · rcases hl with ⟨hd, hgap⟩
    refine Or.inr (Or.inl ⟨hd, ?_, ?_⟩)
    · omega
    · have harg : d+2 ≤ a-d-2 := by omega
      exact Nat.le_trans harg (ternaryOnes_ge _)
  · rcases hr with ⟨ha0, ha, hd, hgap⟩
    refine Or.inr (Or.inr (Or.inl ⟨ha0, ha, ?_, hd, ?_⟩))
    · omega
    · have harg : a-1 ≤ d+4-a := by omega
      exact Nat.le_trans harg (ternaryOnes_ge _)
  · rcases hr with ⟨ha0, ha, hd, hgap⟩
    refine Or.inr (Or.inr (Or.inr ⟨ha0, ha, ?_, hd, ?_⟩))
    · omega
    · have harg : a+1 ≤ d+1-a := by omega
      have htn : d+1-a ≤ ternaryOnes (d+1-a) := ternaryOnes_ge _
      have hbudget : a+1 ≤ ternaryOnes (d+1-a) := Nat.le_trans harg htn
      omega

/-- The original high-level evaluator maps every even d>=36 by this exact edge. -/
theorem highLevelNext_two_d (d : Nat)
    (hd : d%2=0) (hge : 36≤d) :
    highLevelNext (.D 2 d) = some (.D d 9) := by
  simp only [highLevelNext]
  have h0 : 2 ≠ 0 := by omega
  simp only [if_neg h0]
  have hleftOdd : ¬(d%2=1 ∧ 2≥d+5) := by omega
  simp only [if_neg hleftOdd]
  have hleftEven : ¬(d%2=0 ∧ 2≥d+3) := by omega
  simp only [if_neg hleftEven]
  have hfirstOdd : 2%2≠1 := by omega
  simp only [if_neg hfirstOdd]
  have hgapTwo : 2≠d+2 := by omega
  simp only [if_neg hgapTwo]
  have hrightOdd : d%2≠1 := by omega
  simp only [if_neg hrightOdd]
  have heval : evalA (d+1-2) 2 (2*2+5) = some (d,0,9) := by
    simp [evalA]
    omega
  simp only [heval, Option.bind_some]
  simp [drainB]

theorem old_cone_source (d : Nat) (hd : 36≤d) (heven : d%2=0) :
    oldAffineCone 2 d := by
  unfold oldAffineCone
  exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, heven, by omega⟩))

theorem old_cone_target (d : Nat) (hd : 36≤d) :
    oldAffineCone d 9 := by
  unfold oldAffineCone
  exact Or.inl ⟨by omega, by omega⟩

theorem canonicalGap_two_d (d : Nat) (hd : 36≤d) :
    canonicalGap 2 d = d-8 := by
  unfold canonicalGap natAbsDiff
  have h1 : ¬2≥d := by omega
  have h2 : ¬d≤8 := by omega
  simp [h1, h2]

theorem canonicalGap_d_nine (d : Nat) (hd : 36≤d) :
    canonicalGap d 9 = d-36 := by
  unfold canonicalGap natAbsDiff
  have h1 : d≥9 := by omega
  by_cases h2 : d≤36
  · have heq : d=36 := by omega
    simp [h1, h2, heq]
  · simp [h1, h2]

/-- For d=36+2*sqrt(C), the source satisfies the proposed C-gap bound. -/
theorem quadratic_gap_source_bound (C : Nat) (hC : 0<C) :
    C * smallerCounter 2 (36+2*Nat.sqrt C) ≤
      canonicalGap 2 (36+2*Nat.sqrt C)^2 := by
  let t := Nat.sqrt C
  let d := 36+2*t
  have hd : 36≤d := by dsimp [d]; omega
  have hroot : C < (t+1)*(t+1) := by
    simpa [t, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt C
  have hbase : t+1 ≤ t+14 := by omega
  have hpow : (t+1)*(t+1) ≤ (t+14)*(t+14) :=
    Nat.mul_le_mul hbase hbase
  have hC' : C ≤ (t+14)*(t+14) := Nat.le_trans (Nat.le_of_lt hroot) hpow
  have hgap : canonicalGap 2 d = 2*(t+14) := by
    rw [canonicalGap_two_d d hd]
    dsimp [d]
    omega
  have hsmall : smallerCounter 2 d = 2 := by
    simp [smallerCounter, show 2≤d by omega]
  change C * smallerCounter 2 d ≤ canonicalGap 2 d^2
  rw [hsmall, hgap]
  nlinarith

/-- For d=36+2*sqrt(C), the target strictly violates the same C-gap bound. -/
theorem quadratic_gap_target_fails (C : Nat) (hC : 0<C) :
    canonicalGap (36+2*Nat.sqrt C) 9^2 <
      C * smallerCounter (36+2*Nat.sqrt C) 9 := by
  let t := Nat.sqrt C
  let d := 36+2*t
  have hd : 36≤d := by dsimp [d]; omega
  have hroot : t*t ≤ C := by
    simpa [t] using Nat.sqrt_le' C
  have hgap : canonicalGap d 9 = 2*t := by
    rw [canonicalGap_d_nine d hd]
    dsimp [d]
    omega
  have hsmall : smallerCounter d 9 = 9 := by
    simp [smallerCounter, show ¬d≤9 by omega]
  change canonicalGap d 9^2 < C * smallerCounter d 9
  rw [hgap, hsmall]
  nlinarith

/-- For every positive C, a source/target edge inside the old and new cones
    crosses from g^2>=C*m to g^2<C*m. No uniform quadratic cone invariant exists. -/
theorem no_uniform_quadratic_gap_invariant (C : Nat) (hC : 0<C) :
    ∃ d, 36≤d ∧ d%2=0 ∧
      oldAffineCone 2 d ∧ newAffineCone 2 d ∧
      highLevelNext (.D 2 d) = some (.D d 9) ∧
      oldAffineCone d 9 ∧ newAffineCone d 9 ∧
      C * smallerCounter 2 d ≤ canonicalGap 2 d^2 ∧
      canonicalGap d 9^2 < C * smallerCounter d 9 := by
  let d := 36+2*Nat.sqrt C
  have hd : 36≤d := by dsimp [d]; omega
  have heven : d%2=0 := by dsimp [d]; omega
  have hsOld := old_cone_source d hd heven
  have htOld := old_cone_target d hd
  have hsNew := oldAffineCone_subset_newAffineCone 2 d hsOld
  have htNew := oldAffineCone_subset_newAffineCone d 9 htOld
  have hstep := highLevelNext_two_d d heven hd
  refine ⟨d, hd, heven, hsOld, hsNew, hstep, htOld, htNew, ?_, ?_⟩
  · simpa [d] using quadratic_gap_source_bound C hC
  · simpa [d] using quadratic_gap_target_fails C hC

#print axioms oldAffineCone_subset_newAffineCone
#print axioms highLevelNext_two_d
#print axioms no_uniform_quadratic_gap_invariant

end BB6.Agent27QuadraticGap
