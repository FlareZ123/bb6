import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
Exact 24-node affine backward cone: second arithmetic progression surviving
parity-aware forward quotient mod384 excluded at every source-map time.
Every predecessor of a listed state lies in this finite symbolic cone.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace BB6.Agent31F321Ray7933
open BB6.Agent31F321Density

private def AffineDead (A D : Nat) : Prop :=
  (∃ k : Nat, A = 12288*k+7934 ∧ D = 12288*k+7933) ∨ (
      (∃ k : Nat, A = 3072*k+1982 ∧ D = 21504*k+13879) ∨ (
      (∃ k : Nat, A = 768*k+494 ∧ D = 23808*k+15361) ∨ (
      (∃ k : Nat, A = 192*k+122 ∧ D = 24384*k+15727) ∨ (
      (∃ k : Nat, A = 48*k+29 ∧ D = 24528*k+15814) ∨ (
      (∃ k : Nat, A = 12384*k+7986 ∧ D = 12192*k+7862) ∨ (
      (∃ k : Nat, A = 3096*k+1995 ∧ D = 21480*k+13847) ∨ (
      (∃ k : Nat, A = 13836*k+8919 ∧ D = 10740*k+6922) ∨ (
      (∃ k : Nat, A = 12672*k+8175 ∧ D = 11904*k+7679) ∨ (
      (∃ k : Nat, A = 18624*k+12015 ∧ D = 5952*k+3838) ∨ (
      (∃ k : Nat, A = 13824*k+8922 ∧ D = 10752*k+6938) ∨ (
      (∃ k : Nat, A = 3456*k+2229 ∧ D = 21120*k+13625) ∨ (
      (∃ k : Nat, A = 14016*k+9042 ∧ D = 10560*k+6811) ∨ (
      (∃ k : Nat, A = 3504*k+2259 ∧ D = 21072*k+13588) ∨ (
      (∃ k : Nat, A = 19296*k+12448 ∧ D = 5280*k+3404) ∨ (
      (∃ k : Nat, A = 18432*k+11901 ∧ D = 6144*k+3965) ∨ (
      (∃ k : Nat, A = 21504*k+13884 ∧ D = 3072*k+1981) ∨ (
      (∃ k : Nat, A = 23040*k+14875 ∧ D = 1536*k+989) ∨ (
      (∃ k : Nat, A = 23808*k+15370 ∧ D = 768*k+493) ∨ (
      (∃ k : Nat, A = 5952*k+3841 ∧ D = 18624*k+12016) ∨ (
      (∃ k : Nat, A = 24192*k+15617 ∧ D = 384*k+245) ∨ (
      (∃ k : Nat, A = 24384*k+15740 ∧ D = 192*k+121) ∨ (
      (∃ k : Nat, A = 24480*k+15801 ∧ D = 96*k+59) ∨ (
      (∃ k : Nat, A = 24528*k+15831 ∧ D = 48*k+28))))))))))))))))))))))))

private theorem intro_0 (k:Nat) : AffineDead (12288*k+7934) (12288*k+7933) := by
  unfold AffineDead
  exact Or.inl ⟨k,rfl,rfl⟩

private theorem intro_1 (k:Nat) : AffineDead (3072*k+1982) (21504*k+13879) := by
  unfold AffineDead
  exact Or.inr (Or.inl ⟨k,rfl,rfl⟩)

private theorem intro_2 (k:Nat) : AffineDead (768*k+494) (23808*k+15361) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))

private theorem intro_3 (k:Nat) : AffineDead (192*k+122) (24384*k+15727) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))

private theorem intro_4 (k:Nat) : AffineDead (48*k+29) (24528*k+15814) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))

private theorem intro_5 (k:Nat) : AffineDead (12384*k+7986) (12192*k+7862) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))))

private theorem intro_6 (k:Nat) : AffineDead (3096*k+1995) (21480*k+13847) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))))

private theorem intro_7 (k:Nat) : AffineDead (13836*k+8919) (10740*k+6922) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))))))

private theorem intro_8 (k:Nat) : AffineDead (12672*k+8175) (11904*k+7679) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))))))

private theorem intro_9 (k:Nat) : AffineDead (18624*k+12015) (5952*k+3838) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))))))))

private theorem intro_10 (k:Nat) : AffineDead (13824*k+8922) (10752*k+6938) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))))))))

private theorem intro_11 (k:Nat) : AffineDead (3456*k+2229) (21120*k+13625) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))))))))))

private theorem intro_12 (k:Nat) : AffineDead (14016*k+9042) (10560*k+6811) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))))))))))

private theorem intro_13 (k:Nat) : AffineDead (3504*k+2259) (21072*k+13588) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))))))))))))

private theorem intro_14 (k:Nat) : AffineDead (19296*k+12448) (5280*k+3404) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))))))))))))

private theorem intro_15 (k:Nat) : AffineDead (18432*k+11901) (6144*k+3965) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))))))))))))))

private theorem intro_16 (k:Nat) : AffineDead (21504*k+13884) (3072*k+1981) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))))))))))))))

private theorem intro_17 (k:Nat) : AffineDead (23040*k+14875) (1536*k+989) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))))))))))))))))

private theorem intro_18 (k:Nat) : AffineDead (23808*k+15370) (768*k+493) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))))))))))))))))

private theorem intro_19 (k:Nat) : AffineDead (5952*k+3841) (18624*k+12016) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))))))))))))))))))

private theorem intro_20 (k:Nat) : AffineDead (24192*k+15617) (384*k+245) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))))))))))))))))))

private theorem intro_21 (k:Nat) : AffineDead (24384*k+15740) (192*k+121) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩)))))))))))))))))))))

private theorem intro_22 (k:Nat) : AffineDead (24480*k+15801) (96*k+59) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,rfl,rfl⟩))))))))))))))))))))))

private theorem intro_23 (k:Nat) : AffineDead (24528*k+15831) (48*k+28) := by
  unfold AffineDead
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨k,rfl,rfl⟩)))))))))))))))))))))))

private theorem pred_0 (k a d:Nat)
  (hm:CounterMove a d (12288*k+7934) (12288*k+7933)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 18432*k+11901 := by omega
      have hd : d = 6144*k+3965 := by omega
      rw [ha,hd]
      exact intro_15 k
  | equal =>
      omega
  | far h1 h2 =>
      have ha : a = 3072*k+1982 := by omega
      have hd : d = 21504*k+13879 := by omega
      rw [ha,hd]
      exact intro_1 k
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_1 (k a d:Nat)
  (hm:CounterMove a d (3072*k+1982) (21504*k+13879)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 13824*k+8922 := by omega
      have hd : d = 10752*k+6938 := by omega
      rw [ha,hd]
      exact intro_10 k
  | equal =>
      omega
  | far h1 h2 =>
      have ha : a = 768*k+494 := by omega
      have hd : d = 23808*k+15361 := by omega
      rw [ha,hd]
      exact intro_2 k
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_2 (k a d:Nat)
  (hm:CounterMove a d (768*k+494) (23808*k+15361)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 12672*k+8175 := by omega
      have hd : d = 11904*k+7679 := by omega
      rw [ha,hd]
      exact intro_8 k
  | equal =>
      omega
  | far h1 h2 =>
      have ha : a = 192*k+122 := by omega
      have hd : d = 24384*k+15727 := by omega
      rw [ha,hd]
      exact intro_3 k
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_3 (k a d:Nat)
  (hm:CounterMove a d (192*k+122) (24384*k+15727)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 12384*k+7986 := by omega
      have hd : d = 12192*k+7862 := by omega
      rw [ha,hd]
      exact intro_5 k
  | equal =>
      omega
  | far h1 h2 =>
      have ha : a = 48*k+29 := by omega
      have hd : d = 24528*k+15814 := by omega
      rw [ha,hd]
      exact intro_4 k
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_4 (k a d:Nat)
  (hm:CounterMove a d (48*k+29) (24528*k+15814)) :
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

private theorem pred_5 (k a d:Nat)
  (hm:CounterMove a d (12384*k+7986) (12192*k+7862)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      omega
  | equal =>
      omega
  | far h1 h2 =>
      have ha : a = 3096*k+1995 := by omega
      have hd : d = 21480*k+13847 := by omega
      rw [ha,hd]
      exact intro_6 k
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_6 (k a d:Nat)
  (hm:CounterMove a d (3096*k+1995) (21480*k+13847)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 13836*k+8919 := by omega
      have hd : d = 10740*k+6922 := by omega
      rw [ha,hd]
      exact intro_7 k
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_7 (k a d:Nat)
  (hm:CounterMove a d (13836*k+8919) (10740*k+6922)) :
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
  (hm:CounterMove a d (12672*k+8175) (11904*k+7679)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 18624*k+12015 := by omega
      have hd : d = 5952*k+3838 := by omega
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
  (hm:CounterMove a d (18624*k+12015) (5952*k+3838)) :
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

private theorem pred_10 (k a d:Nat)
  (hm:CounterMove a d (13824*k+8922) (10752*k+6938)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      omega
  | equal =>
      omega
  | far h1 h2 =>
      have ha : a = 3456*k+2229 := by omega
      have hd : d = 21120*k+13625 := by omega
      rw [ha,hd]
      exact intro_11 k
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_11 (k a d:Nat)
  (hm:CounterMove a d (3456*k+2229) (21120*k+13625)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 14016*k+9042 := by omega
      have hd : d = 10560*k+6811 := by omega
      rw [ha,hd]
      exact intro_12 k
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_12 (k a d:Nat)
  (hm:CounterMove a d (14016*k+9042) (10560*k+6811)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 19296*k+12448 := by omega
      have hd : d = 5280*k+3404 := by omega
      rw [ha,hd]
      exact intro_14 k
  | equal =>
      omega
  | far h1 h2 =>
      have ha : a = 3504*k+2259 := by omega
      have hd : d = 21072*k+13588 := by omega
      rw [ha,hd]
      exact intro_13 k
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_13 (k a d:Nat)
  (hm:CounterMove a d (3504*k+2259) (21072*k+13588)) :
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

private theorem pred_14 (k a d:Nat)
  (hm:CounterMove a d (19296*k+12448) (5280*k+3404)) :
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

private theorem pred_15 (k a d:Nat)
  (hm:CounterMove a d (18432*k+11901) (6144*k+3965)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 21504*k+13884 := by omega
      have hd : d = 3072*k+1981 := by omega
      rw [ha,hd]
      exact intro_16 k
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_16 (k a d:Nat)
  (hm:CounterMove a d (21504*k+13884) (3072*k+1981)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 23040*k+14875 := by omega
      have hd : d = 1536*k+989 := by omega
      rw [ha,hd]
      exact intro_17 k
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_17 (k a d:Nat)
  (hm:CounterMove a d (23040*k+14875) (1536*k+989)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 23808*k+15370 := by omega
      have hd : d = 768*k+493 := by omega
      rw [ha,hd]
      exact intro_18 k
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_18 (k a d:Nat)
  (hm:CounterMove a d (23808*k+15370) (768*k+493)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 24192*k+15617 := by omega
      have hd : d = 384*k+245 := by omega
      rw [ha,hd]
      exact intro_20 k
  | equal =>
      omega
  | far h1 h2 =>
      have ha : a = 5952*k+3841 := by omega
      have hd : d = 18624*k+12016 := by omega
      rw [ha,hd]
      exact intro_19 k
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_19 (k a d:Nat)
  (hm:CounterMove a d (5952*k+3841) (18624*k+12016)) :
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

private theorem pred_20 (k a d:Nat)
  (hm:CounterMove a d (24192*k+15617) (384*k+245)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 24384*k+15740 := by omega
      have hd : d = 192*k+121 := by omega
      rw [ha,hd]
      exact intro_21 k
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_21 (k a d:Nat)
  (hm:CounterMove a d (24384*k+15740) (192*k+121)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 24480*k+15801 := by omega
      have hd : d = 96*k+59 := by omega
      rw [ha,hd]
      exact intro_22 k
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_22 (k a d:Nat)
  (hm:CounterMove a d (24480*k+15801) (96*k+59)) :
  AffineDead a d := by
  cases hm with
  | high h =>
      have ha : a = 24528*k+15831 := by omega
      have hd : d = 48*k+28 := by omega
      rw [ha,hd]
      exact intro_23 k
  | equal =>
      omega
  | far h1 h2 =>
      omega
  | middleEven h1 h2 hp =>
      omega
  | middleOdd h1 h2 hp =>
      omega

private theorem pred_23 (k a d:Nat)
  (hm:CounterMove a d (24528*k+15831) (48*k+28)) :
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
  rcases h with ⟨k0,ha0,hd0⟩ | ⟨k1,ha1,hd1⟩ | ⟨k2,ha2,hd2⟩ | ⟨k3,ha3,hd3⟩ | ⟨k4,ha4,hd4⟩ | ⟨k5,ha5,hd5⟩ | ⟨k6,ha6,hd6⟩ | ⟨k7,ha7,hd7⟩ | ⟨k8,ha8,hd8⟩ | ⟨k9,ha9,hd9⟩ | ⟨k10,ha10,hd10⟩ | ⟨k11,ha11,hd11⟩ | ⟨k12,ha12,hd12⟩ | ⟨k13,ha13,hd13⟩ | ⟨k14,ha14,hd14⟩ | ⟨k15,ha15,hd15⟩ | ⟨k16,ha16,hd16⟩ | ⟨k17,ha17,hd17⟩ | ⟨k18,ha18,hd18⟩ | ⟨k19,ha19,hd19⟩ | ⟨k20,ha20,hd20⟩ | ⟨k21,ha21,hd21⟩ | ⟨k22,ha22,hd22⟩ | ⟨k23,ha23,hd23⟩
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
  · omega
  · omega
  · omega
  · omega

private theorem backward_closed {a d A D : Nat}
  (hm : CounterMove a d A D) (hbad : AffineDead A D) :
  AffineDead a d := by
  unfold AffineDead at hbad
  rcases hbad with ⟨k0,ha0,hd0⟩ | ⟨k1,ha1,hd1⟩ | ⟨k2,ha2,hd2⟩ | ⟨k3,ha3,hd3⟩ | ⟨k4,ha4,hd4⟩ | ⟨k5,ha5,hd5⟩ | ⟨k6,ha6,hd6⟩ | ⟨k7,ha7,hd7⟩ | ⟨k8,ha8,hd8⟩ | ⟨k9,ha9,hd9⟩ | ⟨k10,ha10,hd10⟩ | ⟨k11,ha11,hd11⟩ | ⟨k12,ha12,hd12⟩ | ⟨k13,ha13,hd13⟩ | ⟨k14,ha14,hd14⟩ | ⟨k15,ha15,hd15⟩ | ⟨k16,ha16,hd16⟩ | ⟨k17,ha17,hd17⟩ | ⟨k18,ha18,hd18⟩ | ⟨k19,ha19,hd19⟩ | ⟨k20,ha20,hd20⟩ | ⟨k21,ha21,hd21⟩ | ⟨k22,ha22,hd22⟩ | ⟨k23,ha23,hd23⟩
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
  · exact pred_10 k10 a d (by simpa [ha10,hd10] using hm)
  · exact pred_11 k11 a d (by simpa [ha11,hd11] using hm)
  · exact pred_12 k12 a d (by simpa [ha12,hd12] using hm)
  · exact pred_13 k13 a d (by simpa [ha13,hd13] using hm)
  · exact pred_14 k14 a d (by simpa [ha14,hd14] using hm)
  · exact pred_15 k15 a d (by simpa [ha15,hd15] using hm)
  · exact pred_16 k16 a d (by simpa [ha16,hd16] using hm)
  · exact pred_17 k17 a d (by simpa [ha17,hd17] using hm)
  · exact pred_18 k18 a d (by simpa [ha18,hd18] using hm)
  · exact pred_19 k19 a d (by simpa [ha19,hd19] using hm)
  · exact pred_20 k20 a d (by simpa [ha20,hd20] using hm)
  · exact pred_21 k21 a d (by simpa [ha21,hd21] using hm)
  · exact pred_22 k22 a d (by simpa [ha22,hd22] using hm)
  · exact pred_23 k23 a d (by simpa [ha23,hd23] using hm)

private theorem no_reach {n a d:Nat}
  (hr:CounterReach 1 1 n a d) : ¬AffineDead a d := by
  induction hr with
  | nil => exact no_seed
  | step hr hm ih =>
      intro hbad
      exact ih (backward_closed hm hbad)

/-- New unconditional all-time ray outside the mod384 excluded set. -/
theorem gate7933_mod12288_never (k n : Nat) :
  ¬ CounterReach 1 1 n (12288*k+7934) (12288*k+7933) := by
  intro hr
  exact no_reach hr (intro_0 k)

#print axioms gate7933_mod12288_never
end BB6.Agent31F321Ray7933
