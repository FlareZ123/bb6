import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
Exact 10-node affine backward cone: an arithmetic progression surviving
parity-aware forward quotient mod384 is nevertheless impossible at every
counter-map time. Each source CounterMove predecessor is either a listed
ray or arithmetically impossible (all equal/middle outputs have D<=2).
All quantifiers cover every k≥0, no cutoff, no floating point.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace BB6.Agent31F321Ray3787
open BB6.Agent31F321Density

private def AffineDead (A D : Nat) : Prop :=
  (∃ k : Nat, A = 6144*k+3788 ∧ D = 6144*k+3787) ∨ (
      (∃ k : Nat, A = 9216*k+5682 ∧ D = 3072*k+1892) ∨ (
      (∃ k : Nat, A = 2304*k+1419 ∧ D = 9984*k+6149) ∨ (
      (∃ k : Nat, A = 7296*k+4494 ∧ D = 4992*k+3073) ∨ (
      (∃ k : Nat, A = 1824*k+1122 ∧ D = 10464*k+6439) ∨ (
      (∃ k : Nat, A = 456*k+279 ∧ D = 11832*k+7276) ∨ (
      (∃ k : Nat, A = 7056*k+4342 ∧ D = 5232*k+3218) ∨ (
      (∃ k : Nat, A = 1764*k+1084 ∧ D = 10524*k+6470) ∨ (
      (∃ k : Nat, A = 9792*k+6031 ∧ D = 2496*k+1535) ∨ (
      (∃ k : Nat, A = 11040*k+6799 ∧ D = 1248*k+766))))))))))

private theorem intro_0 (k:Nat) : AffineDead (6144*k+3788) (6144*k+3787) := by
  unfold AffineDead
  exact Or.inl ⟨k,rfl,rfl⟩

private theorem intro_1 (k:Nat) : AffineDead (9216*k+5682) (3072*k+1892) := by
  unfold AffineDead
  exact Or.inr (Or.inl ⟨k,rfl,rfl⟩)

private theorem intro_2 (k:Nat) : AffineDead (2304*k+1419) (9984*k+6149) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))

private theorem intro_3 (k:Nat) : AffineDead (7296*k+4494) (4992*k+3073) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))

private theorem intro_4 (k:Nat) : AffineDead (1824*k+1122) (10464*k+6439) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))

private theorem intro_5 (k:Nat) : AffineDead (456*k+279) (11832*k+7276) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))))

private theorem intro_6 (k:Nat) : AffineDead (7056*k+4342) (5232*k+3218) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))))

private theorem intro_7 (k:Nat) : AffineDead (1764*k+1084) (10524*k+6470) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))))))

private theorem intro_8 (k:Nat) : AffineDead (9792*k+6031) (2496*k+1535) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))))))

private theorem intro_9 (k:Nat) : AffineDead (11040*k+6799) (1248*k+766) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨k,rfl,rfl⟩)))))))))

private theorem pred_0 (k a d:Nat)
  (hm:CounterMove a d (6144*k+3788) (6144*k+3787)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 9216*k+5682 := by omega
      have hd : d = 3072*k+1892 := by omega
      rw [ha,hd]
      exact intro_1 k
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_1 (k a d:Nat)
  (hm:CounterMove a d (9216*k+5682) (3072*k+1892)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      omega
  | equal =>
      omega
  | far h1 h2 =>
      have ha : a = 2304*k+1419 := by omega
      have hd : d = 9984*k+6149 := by omega
      rw [ha,hd]
      exact intro_2 k
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_2 (k a d:Nat)
  (hm:CounterMove a d (2304*k+1419) (9984*k+6149)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 7296*k+4494 := by omega
      have hd : d = 4992*k+3073 := by omega
      rw [ha,hd]
      exact intro_3 k
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_3 (k a d:Nat)
  (hm:CounterMove a d (7296*k+4494) (4992*k+3073)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 9792*k+6031 := by omega
      have hd : d = 2496*k+1535 := by omega
      rw [ha,hd]
      exact intro_8 k
  | equal =>
      omega
  | far h1 h2 =>
      have ha : a = 1824*k+1122 := by omega
      have hd : d = 10464*k+6439 := by omega
      rw [ha,hd]
      exact intro_4 k
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_4 (k a d:Nat)
  (hm:CounterMove a d (1824*k+1122) (10464*k+6439)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 7056*k+4342 := by omega
      have hd : d = 5232*k+3218 := by omega
      rw [ha,hd]
      exact intro_6 k
  | equal =>
      omega
  | far h1 h2 =>
      have ha : a = 456*k+279 := by omega
      have hd : d = 11832*k+7276 := by omega
      rw [ha,hd]
      exact intro_5 k
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_5 (k a d:Nat)
  (hm:CounterMove a d (456*k+279) (11832*k+7276)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      omega
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_6 (k a d:Nat)
  (hm:CounterMove a d (7056*k+4342) (5232*k+3218)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      omega
  | equal =>
      omega
  | far h1 h2 =>
      have ha : a = 1764*k+1084 := by omega
      have hd : d = 10524*k+6470 := by omega
      rw [ha,hd]
      exact intro_7 k
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_7 (k a d:Nat)
  (hm:CounterMove a d (1764*k+1084) (10524*k+6470)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      omega
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_8 (k a d:Nat)
  (hm:CounterMove a d (9792*k+6031) (2496*k+1535)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 11040*k+6799 := by omega
      have hd : d = 1248*k+766 := by omega
      rw [ha,hd]
      exact intro_9 k
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_9 (k a d:Nat)
  (hm:CounterMove a d (11040*k+6799) (1248*k+766)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      omega
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem no_seed : ¬ AffineDead 1 1 := by
  intro h
  unfold AffineDead at h
  rcases h with ⟨k0,ha0,hd0⟩ | ⟨k1,ha1,hd1⟩ | ⟨k2,ha2,hd2⟩ | ⟨k3,ha3,hd3⟩ | ⟨k4,ha4,hd4⟩ | ⟨k5,ha5,hd5⟩ | ⟨k6,ha6,hd6⟩ | ⟨k7,ha7,hd7⟩ | ⟨k8,ha8,hd8⟩ | ⟨k9,ha9,hd9⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem backward_closed {a d A D : Nat}
  (hm : CounterMove a d A D) (hbad : AffineDead A D) :
  AffineDead a d := by
  unfold AffineDead at hbad
  rcases hbad with ⟨k0,ha0,hd0⟩ | ⟨k1,ha1,hd1⟩ | ⟨k2,ha2,hd2⟩ | ⟨k3,ha3,hd3⟩ | ⟨k4,ha4,hd4⟩ | ⟨k5,ha5,hd5⟩ | ⟨k6,ha6,hd6⟩ | ⟨k7,ha7,hd7⟩ | ⟨k8,ha8,hd8⟩ | ⟨k9,ha9,hd9⟩
  · exact pred_0 k0 a d (by simpa [ha0,hd0] using hm)
  · exact pred_1 k1 a d (by simpa [ha1,hd1] using hm)
  · exact pred_2 k2 a d (by simpa [ha2,hd2] using hm)
  · exact pred_3 k3 a d (by simpa [ha3,hd3] using hm)
  · exact pred_4 k4 a d (by simpa [ha4,hd4] using hm)
  · exact pred_5 k5 a d (by simpa [ha5,hd5] using hm)
  · exact pred_6 k6 a d (by simpa [ha6,hd6] using hm)
  · exact pred_7 k7 a d (by simpa [ha7,hd7] using hm)
  · exact pred_8 k8 a d (by simpa [ha8,hd8] using hm)
  · exact pred_9 k9 a d (by simpa [ha9,hd9] using hm)

private theorem no_reach {n a d:Nat}
  (hr:CounterReach 1 1 n a d) : ¬AffineDead a d := by
  induction hr with
  | nil => exact no_seed
  | step hr hm ih =>
      intro hbad
      exact ih (backward_closed hm hbad)

/-- New unconditional all-time infinite arithmetic-ray exclusion,
    distinct from previously excluded mod384 and odd-depth base-four rays. -/
theorem gate3787_mod6144_never (k n : Nat) :
  ¬ CounterReach 1 1 n (6144*k+3788) (6144*k+3787) := by
  intro hr
  exact no_reach hr (intro_0 k)

#print axioms gate3787_mod6144_never
end BB6.Agent31F321Ray3787
