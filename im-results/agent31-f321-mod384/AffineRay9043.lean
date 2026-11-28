import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-! Seven-node exact affine backward-closed cone for source halting gate
    d≡9043(mod12288). Exhaustive high/far predecessor disjunction is
    proved from original CounterMove, not trusted from generator. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace BB6.Agent31F321Ray9043
open BB6.Agent31F321Density

private def AffineDead (A D : Nat) : Prop :=
  (∃ k : Nat, A = 12288*k+9044 ∧ D = 12288*k+9043) ∨ (
      (∃ k : Nat, A = 18432*k+13566 ∧ D = 6144*k+4520) ∨ (
      (∃ k : Nat, A = 4608*k+3390 ∧ D = 19968*k+14690) ∨ (
      (∃ k : Nat, A = 1152*k+846 ∧ D = 23424*k+17228) ∨ (
      (∃ k : Nat, A = 288*k+210 ∧ D = 24288*k+17858) ∨ (
      (∃ k : Nat, A = 72*k+51 ∧ D = 24504*k+18011) ∨ (
      (∃ k : Nat, A = 12324*k+9057 ∧ D = 12252*k+9004)))))))

private theorem intro_0 (k : Nat) :
  AffineDead (12288*k+9044) (12288*k+9043) := by
  unfold AffineDead
  exact Or.inl ⟨k,rfl,rfl⟩

private theorem intro_1 (k : Nat) :
  AffineDead (18432*k+13566) (6144*k+4520) := by
  unfold AffineDead
  exact Or.inr (Or.inl ⟨k,rfl,rfl⟩)

private theorem intro_2 (k : Nat) :
  AffineDead (4608*k+3390) (19968*k+14690) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))

private theorem intro_3 (k : Nat) :
  AffineDead (1152*k+846) (23424*k+17228) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))

private theorem intro_4 (k : Nat) :
  AffineDead (288*k+210) (24288*k+17858) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))

private theorem intro_5 (k : Nat) :
  AffineDead (72*k+51) (24504*k+18011) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))))

private theorem intro_6 (k : Nat) :
  AffineDead (12324*k+9057) (12252*k+9004) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨k,rfl,rfl⟩))))))

private theorem pred_0 (k a d:Nat)
  (hm:CounterMove a d (12288*k+9044) (12288*k+9043)) :
  AffineDead a d := by
  have hD : 3 ≤ 12288*k+9043 := by omega
  rcases large_second_only_high_far hm hD with ⟨ha,hd⟩ | ⟨ha,hd⟩
  ·
      have hA : a = 18432*k+13566 := by omega
      have hD : d = 6144*k+4520 := by omega
      rw [hA,hD]
      exact intro_1 k
  ·
      omega

private theorem pred_1 (k a d:Nat)
  (hm:CounterMove a d (18432*k+13566) (6144*k+4520)) :
  AffineDead a d := by
  have hD : 3 ≤ 6144*k+4520 := by omega
  rcases large_second_only_high_far hm hD with ⟨ha,hd⟩ | ⟨ha,hd⟩
  ·
      omega
  ·
      have hA : a = 4608*k+3390 := by omega
      have hD : d = 19968*k+14690 := by omega
      rw [hA,hD]
      exact intro_2 k

private theorem pred_2 (k a d:Nat)
  (hm:CounterMove a d (4608*k+3390) (19968*k+14690)) :
  AffineDead a d := by
  have hD : 3 ≤ 19968*k+14690 := by omega
  rcases large_second_only_high_far hm hD with ⟨ha,hd⟩ | ⟨ha,hd⟩
  ·
      omega
  ·
      have hA : a = 1152*k+846 := by omega
      have hD : d = 23424*k+17228 := by omega
      rw [hA,hD]
      exact intro_3 k

private theorem pred_3 (k a d:Nat)
  (hm:CounterMove a d (1152*k+846) (23424*k+17228)) :
  AffineDead a d := by
  have hD : 3 ≤ 23424*k+17228 := by omega
  rcases large_second_only_high_far hm hD with ⟨ha,hd⟩ | ⟨ha,hd⟩
  ·
      omega
  ·
      have hA : a = 288*k+210 := by omega
      have hD : d = 24288*k+17858 := by omega
      rw [hA,hD]
      exact intro_4 k

private theorem pred_4 (k a d:Nat)
  (hm:CounterMove a d (288*k+210) (24288*k+17858)) :
  AffineDead a d := by
  have hD : 3 ≤ 24288*k+17858 := by omega
  rcases large_second_only_high_far hm hD with ⟨ha,hd⟩ | ⟨ha,hd⟩
  ·
      omega
  ·
      have hA : a = 72*k+51 := by omega
      have hD : d = 24504*k+18011 := by omega
      rw [hA,hD]
      exact intro_5 k

private theorem pred_5 (k a d:Nat)
  (hm:CounterMove a d (72*k+51) (24504*k+18011)) :
  AffineDead a d := by
  have hD : 3 ≤ 24504*k+18011 := by omega
  rcases large_second_only_high_far hm hD with ⟨ha,hd⟩ | ⟨ha,hd⟩
  ·
      have hA : a = 12324*k+9057 := by omega
      have hD : d = 12252*k+9004 := by omega
      rw [hA,hD]
      exact intro_6 k
  ·
      omega

private theorem pred_6 (k a d:Nat)
  (hm:CounterMove a d (12324*k+9057) (12252*k+9004)) :
  AffineDead a d := by
  have hD : 3 ≤ 12252*k+9004 := by omega
  rcases large_second_only_high_far hm hD with ⟨ha,hd⟩ | ⟨ha,hd⟩
  ·
      omega
  ·
      omega

private theorem no_seed : ¬ AffineDead 1 1 := by
  intro h
  unfold AffineDead at h
  rcases h with ⟨k0,ha0,hd0⟩ | ⟨k1,ha1,hd1⟩ | ⟨k2,ha2,hd2⟩ | ⟨k3,ha3,hd3⟩ | ⟨k4,ha4,hd4⟩ | ⟨k5,ha5,hd5⟩ | ⟨k6,ha6,hd6⟩
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
  rcases hbad with ⟨k0,ha0,hd0⟩ | ⟨k1,ha1,hd1⟩ | ⟨k2,ha2,hd2⟩ | ⟨k3,ha3,hd3⟩ | ⟨k4,ha4,hd4⟩ | ⟨k5,ha5,hd5⟩ | ⟨k6,ha6,hd6⟩
  · exact pred_0 k0 a d (by simpa [ha0,hd0] using hm)
  · exact pred_1 k1 a d (by simpa [ha1,hd1] using hm)
  · exact pred_2 k2 a d (by simpa [ha2,hd2] using hm)
  · exact pred_3 k3 a d (by simpa [ha3,hd3] using hm)
  · exact pred_4 k4 a d (by simpa [ha4,hd4] using hm)
  · exact pred_5 k5 a d (by simpa [ha5,hd5] using hm)
  · exact pred_6 k6 a d (by simpa [ha6,hd6] using hm)

private theorem no_reach {n a d:Nat}
  (hr:CounterReach 1 1 n a d) : ¬AffineDead a d := by
  induction hr with
  | nil => exact no_seed
  | step hr hm ih =>
      intro hbad
      exact ih (backward_closed hm hbad)

/-- New 7-node closed infinite F321 source gate family, not excluded by
    parity forward quotient or earlier restricted base-four ray proofs. -/
theorem gate9043_mod12288_never (k n : Nat) :
  ¬ CounterReach 1 1 n (12288*k+9044) (12288*k+9043) := by
  intro hr
  exact no_reach hr (intro_0 k)

#print axioms gate9043_mod12288_never
end BB6.Agent31F321Ray9043
