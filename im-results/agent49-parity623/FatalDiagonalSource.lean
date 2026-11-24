import Agent49FatalRectangleSource
import Agent49FatalAllPrefix

namespace BB6.Agent49FatalDiagonalSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49FlatDrainSource BB6.Agent49FatalCylinder BB6.Agent49FatalRectangleSource

theorem fullDrainRules : FullRules Fatal where
  toRules := drainRules
  lift2zero := by
    intro b h d
    rw [drain_three_two_zero b d]
    exact h _

theorem drain_bundle (A a : Nat) :
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

theorem parity_shift (P r j : Nat) : (r+2*P*j)%2=r%2 := by
  rw [Nat.mul_assoc]
  omega

/-- Every arithmetic ray parallel to the diagonal eventually contains a
one-return halter, with both initial parities maintained. -/
theorem fatal_diagonal_positive (P a0 d0 : Nat) (hP : 0<P) (ha0 : 0<a0) :
    ∃ j, highLevelNext (.D (a0+2*P*j) (d0+2*P*j))=none := by
  have hp : 0<2*P := by omega
  by_cases h1 : d0%2=1 ∧ a0≥d0+5
  · obtain ⟨j,hj⟩ := fatal_progression_all fullDrainRules (2*P) (a0-d0-5) (d0+3) hp
    refine ⟨j,?_⟩
    have hz : a0+2*P*j≠0 := by omega
    have hg : (d0+2*P*j)%2=1 ∧ a0+2*P*j≥d0+2*P*j+5 := by
      rw [parity_shift]; omega
    have ha : a0+2*P*j-(d0+2*P*j)-5=a0-d0-5 := by omega
    have hb : d0+2*P*j+3=d0+3+2*P*j := by omega
    simp only [highLevelNext,if_neg hz,if_pos hg,ha,hb]
    exact hj 5
  · by_cases h2 : d0%2=0 ∧ a0≥d0+3
    · obtain ⟨j,hj⟩ := fatal_progression_all fullDrainRules (2*P) (a0-d0-2) (d0+2) hp
      refine ⟨j,?_⟩
      have hz : a0+2*P*j≠0 := by omega
      have hg1 : ¬((d0+2*P*j)%2=1 ∧ a0+2*P*j≥d0+2*P*j+5) := by rw [parity_shift]; omega
      have hg2 : (d0+2*P*j)%2=0 ∧ a0+2*P*j≥d0+2*P*j+3 := by rw [parity_shift]; omega
      have ha : a0+2*P*j-(d0+2*P*j)-2=a0-d0-2 := by omega
      have hb : d0+2*P*j+2=d0+2+2*P*j := by omega
      simp only [highLevelNext,if_neg hz,if_neg hg1,if_pos hg2,ha,hb]
      exact hj 2
    · by_cases h3 : a0%2=1
      · refine ⟨0,?_⟩
        simp [highLevelNext,show a0≠0 by omega,h1,h2,h3]
      · have common (j : Nat) :
          (a0+2*P*j≠0) ∧
          ¬((d0+2*P*j)%2=1 ∧ a0+2*P*j≥d0+2*P*j+5) ∧
          ¬((d0+2*P*j)%2=0 ∧ a0+2*P*j≥d0+2*P*j+3) ∧
          (a0+2*P*j)%2≠1 := by
          rw [parity_shift,parity_shift]
          omega
        by_cases h4 : a0=d0+2
        · obtain ⟨j,hj⟩ := fatal_progression_all fullDrainRules (2*P) 0 a0 hp
          refine ⟨j,?_⟩
          obtain ⟨hz,hg1,hg2,hg3⟩ := common j
          have hg4 : a0+2*P*j=d0+2*P*j+2 := by omega
          simp only [highLevelNext,if_neg hz,if_neg hg1,if_neg hg2,if_neg hg3,if_pos hg4]
          exact hj 2
        · by_cases h5 : d0%2=1
          · obtain ⟨j,hj⟩ := fatal_progression_all fullDrainRules (2*P) (d0+4-a0) (a0-1) hp
            refine ⟨j,?_⟩
            obtain ⟨hz,hg1,hg2,hg3⟩ := common j
            have hg4 : a0+2*P*j≠d0+2*P*j+2 := by omega
            have hg5 : (d0+2*P*j)%2=1 := by rw [parity_shift]; exact h5
            have ha : d0+2*P*j+4-(a0+2*P*j)=d0+4-a0 := by omega
            have hb : a0+2*P*j-1=a0-1+2*P*j := by omega
            simp only [highLevelNext,if_neg hz,if_neg hg1,if_neg hg2,if_neg hg3,if_neg hg4,if_pos hg5,ha,hb]
            exact hj 3
          · obtain ⟨j,hj⟩ := fatal_progression_all fullDrainRules (2*P) (d0+1-a0) (a0+1) hp
            refine ⟨j,?_⟩
            obtain ⟨hz,hg1,hg2,hg3⟩ := common j
            have hg4 : a0+2*P*j≠d0+2*P*j+2 := by omega
            have hg5 : (d0+2*P*j)%2≠1 := by rw [parity_shift]; exact h5
            have ha : d0+2*P*j+1-(a0+2*P*j)=d0+1-a0 := by omega
            simp only [highLevelNext,if_neg hz,if_neg hg1,if_neg hg2,if_neg hg3,if_neg hg4,if_neg hg5]
            rw [←drain_bundle,ha]
            have hb : a0+2*P*j+1=a0+1+2*P*j := by omega
            rw [hb]
            exact hj 0

theorem fatal_diagonal (P a0 d0 : Nat) (hP : 0<P) :
    ∃ j, highLevelNext (.D (a0+P*j) (d0+P*j))=none := by
  obtain ⟨j,hj⟩ := fatal_diagonal_positive P (a0+P) (d0+P) hP (by omega)
  refine ⟨2*j+1,?_⟩
  have ha : a0+P*(2*j+1)=a0+P+2*P*j := by
    simp only [Nat.mul_add,Nat.mul_one,←Nat.mul_assoc]
    rw [Nat.mul_comm P 2]
    omega
  have hd : d0+P*(2*j+1)=d0+P+2*P*j := by
    simp only [Nat.mul_add,Nat.mul_one,←Nat.mul_assoc]
    rw [Nat.mul_comm P 2]
    omega
  rw [ha,hd]
  exact hj

#print axioms fatal_diagonal
end BB6.Agent49FatalDiagonalSource
