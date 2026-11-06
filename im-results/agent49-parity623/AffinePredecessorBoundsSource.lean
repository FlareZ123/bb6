import Agent49TernaryBufferSource
import Agent8BudgetSource

/-!
Finite inverse envelopes for the four affine outer sectors of original-source #623.
The bounds use exact ray translations to move each sector to a fixed linear boundary,
then bound the ray parameter by the target first counter. The third-counter budget
bounds the remaining base parameter. These are universal predecessor bounds, not
a decision of the blank-root orbit.
-/

namespace BB6.Agent49PredecessorBoundsSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49TernaryShiftSource
open BB6.Agent8BudgetSource

/-- The evaluator never decreases its third counter. -/
theorem evalA_third_ge (a : Nat) :
    ∀ k m aa bb dd, evalA a k m = some (aa,bb,dd) → m ≤ dd := by
  induction a with
  | zero =>
      intro k m aa bb dd h
      rw [evalA] at h
      by_cases h2 : k % 3 = 2
      · simp [h2] at h
        cases h
        omega
      · by_cases h0 : k % 3 = 0
        · simp [h2,h0] at h
        · simp [h2,h0] at h
          cases h
          omega
  | succ a ih =>
      intro k m aa bb dd h
      rw [evalA] at h
      have ha : a+1 ≠ 0 := by omega
      by_cases h2 : k % 3 = 2
      · simp [h2] at h
        cases h
        omega
      · by_cases h0 : k % 3 = 0
        · simp [h2,ha,h0] at h
          cases h
          omega
        · simp [h2,ha,h0] at h
          have hi := ih (k/3) (m+2*(k/3)+3) aa bb dd h
          omega

private theorem highLevel_far_odd_eq (a d : Nat)
    (hd : d%2=1) (hside : d+5≤a) :
    highLevelNext (.D a d) = drainB (a-d-5) (d+3) 5 := by
  have ha : a ≠ 0 := by omega
  have hbranch : d%2=1 ∧ a≥d+5 := ⟨hd,by omega⟩
  simp [highLevelNext,ha,hbranch]
  omega

private theorem highLevel_far_even_eq (a d : Nat)
    (hd : d%2=0) (hside : d+3≤a) :
    highLevelNext (.D a d) = drainB (a-d-2) (d+2) 2 := by
  have ha : a ≠ 0 := by omega
  have hodd : ¬ (d%2=1 ∧ a≥d+5) := by omega
  have heven : d%2=0 ∧ a≥d+3 := ⟨hd,by omega⟩
  simp [highLevelNext,ha,hodd,heven]
  omega

private theorem highLevel_right_odd_eq (a d : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=1) (hside : a≤d) :
    highLevelNext (.D a d) = drainB (d+4-a) (a-1) 3 := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬ (d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2 ≠ 1 := by omega
  have h4 : a ≠ d+2 := by omega
  simp [highLevelNext,h0,h1,h2,h3,h4,hd]
  omega

private theorem highLevel_right_even_eq (a d : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=0) (hside : a≤d) :
    highLevelNext (.D a d) =
      (evalA (d+1-a) a (2*a+5)).bind fun p => drainB p.1 p.2.1 p.2.2 := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬ (d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2 ≠ 1 := by omega
  have h4 : a ≠ d+2 := by omega
  have h5 : d%2 ≠ 1 := by omega
  simp [highLevelNext,h0,h1,h2,h3,h4,h5]
  omega

private theorem extractFirstShift (a d t x y : Nat)
    (hshift : highLevelNext (.D (a+t) d) =
      (highLevelNext (.D a d)).map (liftFirstState t))
    (hnext : highLevelNext (.D (a+t) d) = some (.D x y)) :
    ∃ x0 y0, highLevelNext (.D a d) = some (.D x0 y0) ∧
      x=x0+t ∧ y=y0 := by
  rw [hnext] at hshift
  cases hbase : highLevelNext (.D a d) with
  | none =>
      simp [hbase] at hshift
  | some s =>
      cases s with
      | D x0 y0 =>
          have hval : HighLevelState.D x y = liftFirstState t (.D x0 y0) := by
            simpa [hbase] using hshift
          simp [liftFirstState] at hval
          rcases hval with ⟨hx,hy⟩
          exact ⟨x0,y0,rfl,hx,hy⟩

private theorem extractRightShift (a d t x y : Nat)
    (hshift : highLevelNext (.D a (d+2*t)) =
      (highLevelNext (.D a d)).map (liftFirstState (2*t)))
    (hnext : highLevelNext (.D a (d+2*t)) = some (.D x y)) :
    ∃ x0 y0, highLevelNext (.D a d) = some (.D x0 y0) ∧
      x=x0+2*t ∧ y=y0 := by
  rw [hnext] at hshift
  cases hbase : highLevelNext (.D a d) with
  | none =>
      simp [hbase] at hshift
  | some s =>
      cases s with
      | D x0 y0 =>
          have hval : HighLevelState.D x y = liftFirstState (2*t) (.D x0 y0) := by
            simpa [hbase] using hshift
          simp [liftFirstState] at hval
          injection hval with hx hy
          exact ⟨x0,y0,rfl,hx,hy⟩

/-- A successful far-left odd predecessor has bounded d and bounded a
in terms of the target (x,y). -/
theorem farLeftOdd_predecessor_envelope (a d x y : Nat)
    (hd : d%2=1) (hside : d+5≤a)
    (hnext : highLevelNext (.D a d) = some (.D x y)) :
    a≤x+2*d+8 ∧ 3*d+14≤y := by
  have hbranch := highLevel_far_odd_eq a d hd hside
  have hdrain : drainB (a-d-5) (d+3) 5 = some (.D x y) := by
    rw [← hbranch]
    exact hnext
  have hthird := drainB_d3 (d+3) (a-d-5) 5 x y hdrain
  have hfirst : a≤x+2*d+8 := by
    by_cases hsmall : a < 2*d+8
    · omega
    · have hbase : 2*d+8≤a := by omega
      let t := a-(2*d+8)
      have heq : (2*d+8)-d-5 = d+3 := by omega
      have hbudget : d+3≤ternaryOnes ((2*d+8)-d-5) := by
        rw [heq]
        exact ternaryOnes_ge (d+3)
      have hshift := highLevel_far_odd_shift_ones (2*d+8) d t hd (by omega) hbudget
      have hdecomp : 2*d+8+t=a := by dsimp [t]; omega
      have hnext' : highLevelNext (.D (2*d+8+t) d) = some (.D x y) := by
        rw [hdecomp]
        exact hnext
      obtain ⟨x0,y0,_,hx,_⟩ :=
        extractFirstShift (2*d+8) d t x y hshift hnext'
      dsimp [t] at hx
      omega
  exact ⟨hfirst,by omega⟩

/-- A successful far-left even predecessor has bounded d and bounded a
in terms of the target (x,y). -/
theorem farLeftEven_predecessor_envelope (a d x y : Nat)
    (hd : d%2=0) (hside : d+3≤a)
    (hnext : highLevelNext (.D a d) = some (.D x y)) :
    a≤x+2*d+4 ∧ 3*d+8≤y := by
  have hbranch := highLevel_far_even_eq a d hd hside
  have hdrain : drainB (a-d-2) (d+2) 2 = some (.D x y) := by
    rw [← hbranch]
    exact hnext
  have hthird := drainB_d3 (d+2) (a-d-2) 2 x y hdrain
  have hfirst : a≤x+2*d+4 := by
    by_cases hsmall : a < 2*d+4
    · omega
    · have hbase : 2*d+4≤a := by omega
      let t := a-(2*d+4)
      have heq : (2*d+4)-d-2 = d+2 := by omega
      have hbudget : d+2≤ternaryOnes ((2*d+4)-d-2) := by
        rw [heq]
        exact ternaryOnes_ge (d+2)
      have hshift := highLevel_far_even_shift_ones (2*d+4) d t hd (by omega) hbudget
      have hdecomp : 2*d+4+t=a := by dsimp [t]; omega
      have hnext' : highLevelNext (.D (2*d+4+t) d) = some (.D x y) := by
        rw [hdecomp]
        exact hnext
      obtain ⟨x0,y0,_,hx,_⟩ :=
        extractFirstShift (2*d+4) d t x y hshift hnext'
      dsimp [t] at hx
      omega
  exact ⟨hfirst,by omega⟩

/-- A successful far-right odd predecessor has bounded a and bounded d
in terms of the target (x,y). -/
theorem farRightOdd_predecessor_envelope (a d x y : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=1) (hside : a≤d)
    (hnext : highLevelNext (.D a d) = some (.D x y)) :
    d≤x+2*a+1 ∧ 3*a≤y := by
  have hbranch := highLevel_right_odd_eq a d ha he hd hside
  have hdrain : drainB (d+4-a) (a-1) 3 = some (.D x y) := by
    rw [← hbranch]
    exact hnext
  have hthird := drainB_d3 (a-1) (d+4-a) 3 x y hdrain
  have hfirst : d≤x+2*a+1 := by
    by_cases hsmall : d < 2*a+1
    · omega
    · have hbase : 2*a+1≤d := by omega
      let t := (d-(2*a+1))/2
      have hdecomp : 2*a+1+2*t=d := by dsimp [t]; omega
      have hbaseOdd : (2*a+1)%2=1 := by omega
      have heq : (2*a+1)+4-a = a+5 := by omega
      have hbudget : a-1≤ternaryOnes ((2*a+1)+4-a) := by
        have h := ternaryOnes_ge (a+5)
        rw [heq]
        omega
      have hshift := highLevel_right_odd_shift_ones a (2*a+1) t ha he hbaseOdd (by omega) hbudget
      have hnext' : highLevelNext (.D a ((2*a+1)+2*t)) = some (.D x y) := by
        rw [hdecomp]
        exact hnext
      obtain ⟨x0,y0,_,hx,_⟩ :=
        extractRightShift a (2*a+1) t x y hshift hnext'
      omega
  exact ⟨hfirst,by omega⟩

/-- A successful far-right even predecessor has bounded a and bounded d
in terms of the target (x,y). -/
theorem farRightEven_predecessor_envelope (a d x y : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=0) (hside : a≤d)
    (hnext : highLevelNext (.D a d) = some (.D x y)) :
    d≤x+2*a+2 ∧ 2*a+5≤y := by
  have hbranch := highLevel_right_even_eq a d ha he hd hside
  have hfirst : d≤x+2*a+2 := by
    by_cases hsmall : d < 2*a+2
    · omega
    · have hbase : 2*a+2≤d := by omega
      let t := (d-(2*a+2))/2
      have hdecomp : 2*a+2+2*t=d := by dsimp [t]; omega
      have hbaseEven : (2*a+2)%2=0 := by omega
      have heq : (2*a+2)+1-a = a+3 := by omega
      have hbudget : a<ternaryOnes ((2*a+2)+1-a) := by
        have h := ternaryOnes_ge (a+3)
        rw [heq]
        omega
      have hshift := highLevel_right_even_shift_ones a (2*a+2) t ha he hbaseEven (by omega) hbudget
      have hnext' : highLevelNext (.D a ((2*a+2)+2*t)) = some (.D x y) := by
        rw [hdecomp]
        exact hnext
      obtain ⟨x0,y0,_,hx,_⟩ :=
        extractRightShift a (2*a+2) t x y hshift hnext'
      omega
  have hbind :
      (evalA (d+1-a) a (2*a+5)).bind
        (fun p => drainB p.1 p.2.1 p.2.2) = some (.D x y) := by
    rw [← hbranch]
    exact hnext
  have hthird : 2*a+5≤y := by
    cases heval : evalA (d+1-a) a (2*a+5) with
    | none =>
        simp [heval] at hbind
    | some p =>
        rcases p with ⟨aa,bb,dd⟩
        have hdd := evalA_third_ge (d+1-a) a (2*a+5) aa bb dd heval
        have hdrain : drainB aa bb dd = some (.D x y) := by
          simpa [heval] using hbind
        have hbudget := drainB_d3 bb aa dd x y hdrain
        omega
  exact ⟨hfirst,hthird⟩

#print axioms evalA_third_ge
#print axioms farLeftOdd_predecessor_envelope
#print axioms farLeftEven_predecessor_envelope
#print axioms farRightOdd_predecessor_envelope
#print axioms farRightEven_predecessor_envelope

end BB6.Agent49PredecessorBoundsSource
