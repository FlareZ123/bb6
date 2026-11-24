import Agent49FlatDrainSource
import Agent49DrainCorrectionGrowth

/-! Original-source adapter for the complete logarithmic inverse windows.
The arithmetic module assumes exactly the certified flat-drain equations. -/
namespace BB6.Agent49InverseWindowSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49FlatDrainSource BB6.Agent49CorrectionGrowth

private theorem zero_drain (a z : Nat) : drainB a 0 z = some (.D a z) := by
  rw [drainB]; simp

private theorem state_inj (a z x y : Nat)
    (h : HighLevelState.D a z = HighLevelState.D x y) : a=x ∧ z=y := by
  cases h
  exact ⟨rfl,rfl⟩

def inverseBudget (y : Nat) : Nat := y.log2+1

def Window (A b z x y : Nat) : Prop :=
  A≤x+inverseBudget y ∧ x≤A+inverseBudget y ∧
  z+3*b≤y ∧ y≤z+3*b+4*inverseBudget y

/-- Every successful original drain, even if its first budget reaches zero,
obeys the output-indexed logarithmic inverse rectangle. -/
theorem source_drain_window (A b z x y : Nat)
    (h : drainB A b z = some (.D x y)) : Window A b z x y := by
  exact inverse_window drainB HighLevelState.D state_inj zero_drain
    drain_three drain_three_one drain_three_one_zero drain_three_two
    drain_three_two_zero A b z x y h

/-- If the output first counter is at least twice the logarithmic budget,
every predecessor drain has a positive-budget trace. Its block count is
therefore uniquely determined by the third-coordinate image and z. -/
theorem source_large_first_trace (A b z x y : Nat)
    (h : drainB A b z = some (.D x y))
    (hx : 2*inverseBudget y ≤ x) :
    ∃ n0 n1 n2, PositiveTrace A b z x y n0 n1 n2 := by
  have hw := source_drain_window A b z x y h
  unfold Window at hw
  have hA : inverseBudget y ≤ A := by omega
  have hy : y<2^(inverseBudget y) := by
    unfold inverseBudget
    by_cases h0 : y=0
    · subst y; decide
    · exact (Nat.log2_lt h0).mp (by omega)
  have hb : b<2^(inverseBudget y) := by omega
  obtain ⟨aa,dd,n0,n1,n2,he,ht⟩ := positive_trace_exists drainB HighLevelState.D
    zero_drain drain_three drain_three_one drain_three_two _ A b z hA hb
  rw [h] at he
  obtain ⟨ha,hd⟩ := state_inj x y aa dd (Option.some.inj he)
  subst aa; subst dd
  exact ⟨n0,n1,n2,ht⟩

theorem source_large_first_image (A b z x y : Nat)
    (h : drainB A b z = some (.D x y))
    (hx : 2*inverseBudget y ≤ x) : y=z+image b := by
  obtain ⟨n0,n1,n2,ht⟩ := source_large_first_trace A b z x y h hx
  exact trace_image ht

theorem source_large_first_unique_block (A B b c z x y : Nat)
    (h : drainB A b z = some (.D x y))
    (h' : drainB B c z = some (.D x y))
    (hx : 2*inverseBudget y ≤ x) : b=c := by
  have h1 := source_large_first_image A b z x y h hx
  have h2 := source_large_first_image B c z x y h' hx
  exact image_injective (by omega)

theorem source_large_first_unique (A B b c z x y : Nat)
    (h : drainB A b z = some (.D x y))
    (h' : drainB B c z = some (.D x y))
    (hx : 2*inverseBudget y ≤ x) : A=B ∧ b=c := by
  have he := source_large_first_unique_block A B b c z x y h h' hx
  subst c
  obtain ⟨_,_,_,ht⟩ := source_large_first_trace A b z x y h hx
  obtain ⟨_,_,_,ht'⟩ := source_large_first_trace B b z x y h' hx
  have hd := trace_drift ht
  have hd' := trace_drift ht'
  omega

private theorem drain_bundle (A a : Nat) :
    drainB A (a+1) 0 = (evalA A a (2*a+5)).bind fun p => drainB p.1 p.2.1 p.2.2 := by
  conv => lhs; rw [drainB]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  have h : 0+2*(a+1)+3=2*a+5 := by omega
  rw [h]
  cases he : evalA A a (2*a+5) with
  | none => rfl
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [Option.bind_some]
    have hh := evalA_second_le A a (2*a+5) a1 b1 d1 he
    rw [if_pos (show b1<a+1 by omega)]

private theorem axis_odd_drain (d : Nat) (hd : d%2=1) :
    drainB (d+1) 2 2 = some (.D (d-1) 14) := by
  have h := drain_three_two (d+1) 0 2 (by omega)
  have h' := drain_three_one d 0 7 (by omega)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.add_sub_cancel] at h h'
  rw [h,h',zero_drain]

/-- Exhaustive affine reconstruction interface for every successful parent.
A successful drain may be summarized by any sound five-argument predicate.
The branch partition is shared by inverse and growth consumers. -/
def ParentEnvelope (P : Nat → Nat → Nat → Nat → Nat → Prop) (a d x y : Nat) : Prop :=
  (a=0 ∧ ((d%2=0 ∧ x=d ∧ y=7) ∨ (d%2=1 ∧ x=d-1 ∧ y=14))) ∨
  (∃ A b, d%2=1 ∧ a≥d+5 ∧ a=A+b+2 ∧ d+3=b ∧ P A b 5 x y) ∨
  (∃ A b, d%2=0 ∧ a≥d+3 ∧ a=A+b ∧ d+2=b ∧ P A b 2 x y) ∨
  (a%2=0 ∧ a=d+2 ∧ P 0 a 2 x y) ∨
  (∃ A b, a%2=0 ∧ d%2=1 ∧ a=b+1 ∧ d+3=A+b ∧ P A b 3 x y) ∨
  (∃ A b, a%2=0 ∧ d%2=0 ∧ a+1=b ∧ d+2=A+b ∧ P A b 0 x y)

theorem parent_envelope_complete (P : Nat → Nat → Nat → Nat → Nat → Prop)
    (hP : ∀ A b z x y, drainB A b z = some (.D x y) → P A b z x y)
    (a d x y : Nat) (h : highLevelNext (.D a d) = some (.D x y)) : ParentEnvelope P a d x y := by
  unfold ParentEnvelope
  by_cases ha : a=0
  · subst a
    left
    refine ⟨rfl,?_⟩
    by_cases hd : d%2=1
    · simp only [highLevelNext,if_pos rfl,if_pos hd] at h
      rw [axis_odd_drain d hd] at h
      obtain ⟨hx,hy⟩ := state_inj (d-1) 14 x y (Option.some.inj h)
      exact Or.inr ⟨hd,hx.symm,hy.symm⟩
    · simp only [highLevelNext,if_pos rfl,if_neg hd] at h
      obtain ⟨hx,hy⟩ := state_inj d 7 x y (Option.some.inj h)
      exact Or.inl ⟨by omega,hx.symm,hy.symm⟩
  · right
    by_cases h1 : d%2=1 ∧ a≥d+5
    · left
      simp only [highLevelNext,if_neg ha,if_pos h1] at h
      exact ⟨a-d-5,d+3,h1.1,h1.2,by omega,rfl,hP _ _ _ _ _ h⟩
    · right
      by_cases h2 : d%2=0 ∧ a≥d+3
      · left
        simp only [highLevelNext,if_neg ha,if_neg h1,if_pos h2] at h
        exact ⟨a-d-2,d+2,h2.1,h2.2,by omega,rfl,hP _ _ _ _ _ h⟩
      · right
        by_cases h3 : a%2=1
        · simp only [highLevelNext,if_neg ha,if_neg h1,if_neg h2,if_pos h3] at h
          cases h
        · by_cases h4 : a=d+2
          · left
            simp only [highLevelNext,if_neg ha,if_neg h1,if_neg h2,if_neg h3,if_pos h4] at h
            exact ⟨by omega,h4,hP _ _ _ _ _ h⟩
          · right
            by_cases h5 : d%2=1
            · left
              simp only [highLevelNext,if_neg ha,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_pos h5] at h
              exact ⟨d+4-a,a-1,by omega,h5,by omega,by omega,hP _ _ _ _ _ h⟩
            · right
              simp only [highLevelNext,if_neg ha,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5] at h
              rw [←drain_bundle] at h
              exact ⟨d+1-a,a+1,by omega,by omega,rfl,by omega,hP _ _ _ _ _ h⟩

def ParentWindow := ParentEnvelope Window

theorem parent_window_complete (a d x y : Nat)
    (h : highLevelNext (.D a d) = some (.D x y)) : ParentWindow a d x y :=
  parent_envelope_complete Window source_drain_window a d x y h

#print axioms source_drain_window
#print axioms source_large_first_trace
#print axioms source_large_first_image
#print axioms source_large_first_unique_block
#print axioms source_large_first_unique
#print axioms parent_envelope_complete
#print axioms parent_window_complete
end BB6.Agent49InverseWindowSource
