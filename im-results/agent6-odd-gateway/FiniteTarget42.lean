import MassRestriction
namespace BB6Agent6

theorem blank_unreachable_after_mass_cutoff (target : Nat × Nat)
    (K : Nat) (hk : target.1+target.2 < 3+K)
    (hsmall : ∀ n, n < K → runT n (2,1) ≠ some target) :
    ∀ n, runT n (2,1) ≠ some target := by
  intro n ht
  by_cases hn : n < K
  · exact (hsmall n hn) ht
  · have hr := runT_mass n (2,1) target ht
    simp only [Prod.fst, Prod.snd] at hr
    omega

theorem blank_at_16 : runT 16 (2,1) = some (12,19) := by
  exact runT_step 15 (2,1) (3,27) (12,19)
    blank_at_15 (by simp [T,G])

theorem blank_at_17 : runT 17 (2,1) = some (15,17) := by
  exact runT_step 16 (2,1) (12,19) (15,17)
    blank_at_16 (by simp [T,G])

theorem blank_at_18 : runT 18 (2,1) = some (4,31) := by
  exact runT_step 17 (2,1) (15,17) (4,31)
    blank_at_17 (by simp [T,G])

theorem blank_at_19 : runT 19 (2,1) = some (7,29) := by
  exact runT_step 18 (2,1) (4,31) (7,29)
    blank_at_18 (by simp [T,G])

theorem blank_at_20 : runT 20 (2,1) = some (20,17) := by
  exact runT_step 19 (2,1) (7,29) (20,17)
    blank_at_19 (by simp [T,G])

theorem blank_at_21 : runT 21 (2,1) = some (23,15) := by
  exact runT_step 20 (2,1) (20,17) (23,15)
    blank_at_20 (by simp [T,G])

theorem blank_at_22 : runT 22 (2,1) = some (24,17) := by
  exact runT_step 21 (2,1) (23,15) (24,17)
    blank_at_21 (by simp [T,G])

theorem blank_at_23 : runT 23 (2,1) = some (27,15) := by
  exact runT_step 22 (2,1) (24,17) (27,15)
    blank_at_22 (by simp [T,G])

theorem blank_at_24 : runT 24 (2,1) = some (32,13) := by
  exact runT_step 23 (2,1) (27,15) (32,13)
    blank_at_23 (by simp [T,G])

theorem blank_at_25 : runT 25 (2,1) = some (35,11) := by
  exact runT_step 24 (2,1) (32,13) (35,11)
    blank_at_24 (by simp [T,G])

theorem blank_at_26 : runT 26 (2,1) = some (12,39) := by
  exact runT_step 25 (2,1) (35,11) (12,39)
    blank_at_25 (by simp [T,G])

theorem blank_at_27 : runT 27 (2,1) = some (15,37) := by
  exact runT_step 26 (2,1) (12,39) (15,37)
    blank_at_26 (by simp [T,G])

theorem blank_at_28 : runT 28 (2,1) = some (36,17) := by
  exact runT_step 27 (2,1) (15,37) (36,17)
    blank_at_27 (by simp [T,G])

theorem blank_at_29 : runT 29 (2,1) = some (39,15) := by
  exact runT_step 28 (2,1) (36,17) (39,15)
    blank_at_28 (by simp [T,G])

theorem blank_at_30 : runT 30 (2,1) = some (56,1) := by
  exact runT_step 29 (2,1) (39,15) (56,1)
    blank_at_29 (by simp [T,G])

theorem blank_at_31 : runT 31 (2,1) = some (58,0) := by
  exact runT_step 30 (2,1) (56,1) (58,0)
    blank_at_30 (by simp [T,G])

theorem blank_at_32 : runT 32 (2,1) = some (2,59) := by
  exact runT_step 31 (2,1) (58,0) (2,59)
    blank_at_31 (by simp [T,G])

theorem blank_at_33 : runT 33 (2,1) = some (5,57) := by
  exact runT_step 32 (2,1) (2,59) (5,57)
    blank_at_32 (by simp [T,G])

theorem blank_at_34 : runT 34 (2,1) = some (16,47) := by
  exact runT_step 33 (2,1) (5,57) (16,47)
    blank_at_33 (by simp [T,G])

theorem blank_at_35 : runT 35 (2,1) = some (19,45) := by
  exact runT_step 34 (2,1) (16,47) (19,45)
    blank_at_34 (by simp [T,G])

theorem blank_at_36 : runT 36 (2,1) = some (44,21) := by
  exact runT_step 35 (2,1) (19,45) (44,21)
    blank_at_35 (by simp [T,G])

theorem blank_at_37 : runT 37 (2,1) = some (47,19) := by
  exact runT_step 36 (2,1) (44,21) (47,19)
    blank_at_36 (by simp [T,G])

theorem blank_at_38 : runT 38 (2,1) = some (64,5) := by
  exact runT_step 37 (2,1) (47,19) (64,5)
    blank_at_37 (by simp [T,G])

theorem blank_at_39 : runT 39 (2,1) = some (67,3) := by
  exact runT_step 38 (2,1) (64,5) (67,3)
    blank_at_38 (by simp [T,G])

theorem blank_at_40 : runT 40 (2,1) = some (32,45) := by
  exact runT_step 39 (2,1) (67,3) (32,45)
    blank_at_39 (by simp [T,G])

theorem blank_at_41 : runT 41 (2,1) = some (35,43) := by
  exact runT_step 40 (2,1) (32,45) (35,43)
    blank_at_40 (by simp [T,G])

theorem blank_ne_target_42 (n : Nat) : runT n (2,1) ≠ some (2,42) := by
  apply blank_unreachable_after_mass_cutoff (2,42) 42 (by omega)
  intro j hj heq
  rcases j with _ | j
  · simp [blank_at_0] at heq
  rcases j with _ | j
  · simp [blank_at_1] at heq
  rcases j with _ | j
  · simp [blank_at_2] at heq
  rcases j with _ | j
  · simp [blank_at_3] at heq
  rcases j with _ | j
  · simp [blank_at_4] at heq
  rcases j with _ | j
  · simp [blank_at_5] at heq
  rcases j with _ | j
  · simp [blank_at_6] at heq
  rcases j with _ | j
  · simp [blank_at_7] at heq
  rcases j with _ | j
  · simp [blank_at_8] at heq
  rcases j with _ | j
  · simp [blank_at_9] at heq
  rcases j with _ | j
  · simp [blank_at_10] at heq
  rcases j with _ | j
  · simp [blank_at_11] at heq
  rcases j with _ | j
  · simp [blank_at_12] at heq
  rcases j with _ | j
  · simp [blank_at_13] at heq
  rcases j with _ | j
  · simp [blank_at_14] at heq
  rcases j with _ | j
  · simp [blank_at_15] at heq
  rcases j with _ | j
  · simp [blank_at_16] at heq
  rcases j with _ | j
  · simp [blank_at_17] at heq
  rcases j with _ | j
  · simp [blank_at_18] at heq
  rcases j with _ | j
  · simp [blank_at_19] at heq
  rcases j with _ | j
  · simp [blank_at_20] at heq
  rcases j with _ | j
  · simp [blank_at_21] at heq
  rcases j with _ | j
  · simp [blank_at_22] at heq
  rcases j with _ | j
  · simp [blank_at_23] at heq
  rcases j with _ | j
  · simp [blank_at_24] at heq
  rcases j with _ | j
  · simp [blank_at_25] at heq
  rcases j with _ | j
  · simp [blank_at_26] at heq
  rcases j with _ | j
  · simp [blank_at_27] at heq
  rcases j with _ | j
  · simp [blank_at_28] at heq
  rcases j with _ | j
  · simp [blank_at_29] at heq
  rcases j with _ | j
  · simp [blank_at_30] at heq
  rcases j with _ | j
  · simp [blank_at_31] at heq
  rcases j with _ | j
  · simp [blank_at_32] at heq
  rcases j with _ | j
  · simp [blank_at_33] at heq
  rcases j with _ | j
  · simp [blank_at_34] at heq
  rcases j with _ | j
  · simp [blank_at_35] at heq
  rcases j with _ | j
  · simp [blank_at_36] at heq
  rcases j with _ | j
  · simp [blank_at_37] at heq
  rcases j with _ | j
  · simp [blank_at_38] at heq
  rcases j with _ | j
  · simp [blank_at_39] at heq
  rcases j with _ | j
  · simp [blank_at_40] at heq
  rcases j with _ | j
  · simp [blank_at_41] at heq
  omega

#print axioms BB6Agent6.blank_ne_target_42
end BB6Agent6
