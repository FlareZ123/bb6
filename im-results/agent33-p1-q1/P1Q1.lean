import P1InverseFixed
import ConeKernel
import P1TwoSector
import Std
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace BB6.Agent33Q1
open BB6.Agent4Cone
open BB6.Agent47P1
open BB6.Agent45TwoRoot
open BB6.P1Reduction

private theorem no_fourteen_power_in_fixed_band (x : Nat)
    (hl : 28 * 2^16 < x+12) (hu : x+12 < 56 * 2^16) :
    ∀ j : Nat, x+12 ≠ 14*2^j := by
  intro j he
  by_cases hj : j ≤ 17
  · have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hj
    have hpow : 2^17 = 2*2^16 := by decide
    omega
  · have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show 18 ≤ j by omega)
    have hpow : 2^18 = 4*2^16 := by decide
    omega

private theorem block_L0_1_1_0_1_0_0_0_ : Blocked 266992 3402953 := by
  have h0 : inverseAt 266992 3402953 0 = some (66747, 3536449) := by
    simp [inverseAt]
  have h1 : inverseAt 266992 3402953 1 = some (950859, 1768223) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3536449 ∧ 3536449%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 266992 3402953 2 = some (1392915, 884110) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1768223 ∧ 1768223%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (3402953+266992/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 266992 3402953 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(66747,3536449) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(950859,1768223) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1392915,884110) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 266992 3402953 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(66747,3536449) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 133490 := by omega
      have hy : c+4 = 3536453 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(950859,1768223) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1901714 := by omega
      have hy : c+4 = 1768227 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1392915,884110) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2785826 := by omega
      have hy : c+4 = 884114 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_1_0_1_0_0_ : Blocked 533996 3135951 := by
  have h0 : inverseAt 533996 3135951 0 = some (133498, 3402949) := by
    simp [inverseAt]
  have h1 : inverseAt 533996 3135951 1 = some (984235, 1701473) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3402949 ∧ 3402949%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 533996 3135951 2 = some (1409603, 850735) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1701473 ∧ 1701473%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h3 : inverseAt 533996 3135951 3 = some (1622287, 425366) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 850735 ∧ 850735%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (3135951+533996/2+3)%2^(3+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 533996 3135951 k 1 3 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(133498,3402949) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(984235,1701473) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1409603,850735) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(1622287,425366) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 533996 3135951 k c 3 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(133498,3402949) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 266992 := by omega
      have hy : c+4 = 3402953 := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_1_0_0_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(984235,1701473) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1968466 := by omega
      have hy : c+4 = 1701477 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1409603,850735) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2819202 := by omega
      have hy : c+4 = 850739 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(1622287,425366) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3244570 := by omega
      have hy : c+4 = 425370 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_1_0_0_0_ : Blocked 301040 3368911 := by
  have h0 : inverseAt 301040 3368911 0 = some (75259, 3519431) := by
    simp [inverseAt]
  have h1 : inverseAt 301040 3368911 1 = some (955117, 1759714) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3519431 ∧ 3519431%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (3368911+301040/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 301040 3368911 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(75259,3519431) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(955117,1759714) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 301040 3368911 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(75259,3519431) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 150514 := by omega
      have hy : c+4 = 3519435 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(955117,1759714) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1910230 := by omega
      have hy : c+4 = 1759718 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_1_0_1_0_ : Blocked 1068004 2601945 := by
  have h0 : inverseAt 1068004 2601945 0 = some (267000, 3135947) := by
    simp [inverseAt]
  have h1 : inverseAt 1068004 2601945 1 = some (1050987, 1567972) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3135947 ∧ 3135947%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2601945+1068004/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1068004 2601945 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(267000,3135947) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1050987,1567972) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1068004 2601945 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(267000,3135947) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 533996 := by omega
      have hy : c+4 = 3135951 := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_1_0_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1050987,1567972) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2101970 := by omega
      have hy : c+4 = 1567976 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_1_0_0_ : Blocked 602092 3067861 := by
  have h0 : inverseAt 602092 3067861 0 = some (150522, 3368907) := by
    simp [inverseAt]
  have h1 : inverseAt 602092 3067861 1 = some (992749, 1684452) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3368907 ∧ 3368907%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (3067861+602092/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 602092 3067861 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(150522,3368907) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(992749,1684452) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 602092 3067861 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(150522,3368907) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 301040 := by omega
      have hy : c+4 = 3368911 := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_0_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(992749,1684452) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1985494 := by omega
      have hy : c+4 = 1684456 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_1_0_1_ : Blocked 2136020 1533931 := by
  have h0 : inverseAt 2136020 1533931 0 = some (534004, 2601941) := by
    simp [inverseAt]
  have h1 : inverseAt 2136020 1533931 1 = some (1184489, 1300969) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2601941 ∧ 2601941%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 2136020 1533931 2 = some (1509731, 650483) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1300969 ∧ 1300969%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h3 : inverseAt 2136020 1533931 3 = some (1672352, 325240) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 650483 ∧ 650483%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1533931+2136020/2+3)%2^(3+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2136020 1533931 k 1 3 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(534004,2601941) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1184489,1300969) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1509731,650483) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(1672352,325240) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2136020 1533931 k c 3 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(534004,2601941) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1068004 := by omega
      have hy : c+4 = 2601945 := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_1_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1184489,1300969) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2368974 := by omega
      have hy : c+4 = 1300973 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1509731,650483) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3019458 := by omega
      have hy : c+4 = 650487 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(1672352,325240) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3344700 := by omega
      have hy : c+4 = 325244 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 3344700 (by decide) (by decide)

private theorem block_L0_1_3_0_0_ : Blocked 838632 2831317 := by
  have h0 : inverseAt 838632 2831317 0 = some (209657, 3250633) := by
    simp [inverseAt]
  have h1 : inverseAt 838632 2831317 1 = some (1022315, 1625315) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3250633 ∧ 3250633%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 838632 2831317 2 = some (1428644, 812656) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1625315 ∧ 1625315%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2831317+838632/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 838632 2831317 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(209657,3250633) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1022315,1625315) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1428644,812656) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 838632 2831317 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(209657,3250633) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 419310 := by omega
      have hy : c+4 = 3250637 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1022315,1625315) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2044626 := by omega
      have hy : c+4 = 1625319 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1428644,812656) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2857284 := by omega
      have hy : c+4 = 812660 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2857284 (by decide) (by decide)

private theorem block_L0_1_3_0_1_ : Blocked 2254288 1415659 := by
  have h0 : inverseAt 2254288 1415659 0 = some (563571, 2542803) := by
    simp [inverseAt]
  have h1 : inverseAt 2254288 1415659 1 = some (1199272, 1271400) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2542803 ∧ 2542803%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1415659+2254288/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2254288 1415659 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(563571,2542803) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1199272,1271400) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2254288 1415659 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(563571,2542803) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1127138 := by omega
      have hy : c+4 = 2542807 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1199272,1271400) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2398540 := by omega
      have hy : c+4 = 1271404 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2398540 (by decide) (by decide)

private theorem block_L0_4_1_0_1_ : Blocked 2173648 1496297 := by
  have h0 : inverseAt 2173648 1496297 0 = some (543411, 2583121) := by
    simp [inverseAt]
  have h1 : inverseAt 2173648 1496297 1 = some (1189191, 1291559) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2583121 ∧ 2583121%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 2173648 1496297 2 = some (1512081, 645778) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1291559 ∧ 1291559%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1496297+2173648/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2173648 1496297 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(543411,2583121) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1189191,1291559) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1512081,645778) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2173648 1496297 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(543411,2583121) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1086818 := by omega
      have hy : c+4 = 2583125 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1189191,1291559) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2378378 := by omega
      have hy : c+4 = 1291563 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1512081,645778) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3024158 := by omega
      have hy : c+4 = 645782 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_4_1_1_0_ : Blocked 1256160 2413785 := by
  have h0 : inverseAt 1256160 2413785 0 = some (314039, 3041865) := by
    simp [inverseAt]
  have h1 : inverseAt 1256160 2413785 1 = some (1074505, 1520931) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3041865 ∧ 3041865%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 1256160 2413785 2 = some (1454738, 760464) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1520931 ∧ 1520931%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2413785+1256160/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1256160 2413785 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(314039,3041865) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1074505,1520931) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1454738,760464) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1256160 2413785 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(314039,3041865) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 628074 := by omega
      have hy : c+4 = 3041869 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1074505,1520931) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2149006 := by omega
      have hy : c+4 = 1520935 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1454738,760464) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2909472 := by omega
      have hy : c+4 = 760468 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2909472 (by decide) (by decide)

private theorem block_L0_1_1_0_ : Blocked 1204196 2465759 := by
  have h0 : inverseAt 1204196 2465759 0 = some (301048, 3067857) := by
    simp [inverseAt]
  have h1 : inverseAt 1204196 2465759 1 = some (1068012, 1533927) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3067857 ∧ 3067857%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 1204196 2465759 2 = some (1451494, 766962) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1533927 ∧ 1533927%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2465759+1204196/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1204196 2465759 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(301048,3067857) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1068012,1533927) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1451494,766962) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1204196 2465759 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(301048,3067857) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 602092 := by omega
      have hy : c+4 = 3067861 := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1068012,1533927) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2136020 := by omega
      have hy : c+4 = 1533931 := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1451494,766962) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2902984 := by omega
      have hy : c+4 = 766966 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2902984 (by decide) (by decide)

private theorem block_L0_1_3_0_ : Blocked 1677276 1992675 := by
  have h0 : inverseAt 1677276 1992675 0 = some (419318, 2831313) := by
    simp [inverseAt]
  have h1 : inverseAt 1677276 1992675 1 = some (1127146, 1415655) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2831313 ∧ 2831313%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 1677276 1992675 2 = some (1481060, 707826) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1415655 ∧ 1415655%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1992675+1677276/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1677276 1992675 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(419318,2831313) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1127146,1415655) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1481060,707826) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1677276 1992675 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(419318,2831313) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 838632 := by omega
      have hy : c+4 = 2831317 := by omega
      rw [hx,hy]
      exact block_L0_1_3_0_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1127146,1415655) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2254288 := by omega
      have hy : c+4 = 1415659 := by omega
      rw [hx,hy]
      exact block_L0_1_3_0_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1481060,707826) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2962116 := by omega
      have hy : c+4 = 707830 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2962116 (by decide) (by decide)

private theorem block_L0_4_0_0_ : Blocked 874472 2795479 := by
  have h0 : inverseAt 874472 2795479 0 = some (218617, 3232715) := by
    simp [inverseAt]
  have h1 : inverseAt 874472 2795479 1 = some (1026796, 1616356) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3232715 ∧ 3232715%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2795479+874472/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 874472 2795479 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(218617,3232715) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1026796,1616356) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 874472 2795479 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(218617,3232715) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 437230 := by omega
      have hy : c+4 = 3232719 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1026796,1616356) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2053588 := by omega
      have hy : c+4 = 1616360 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2053588 (by decide) (by decide)

private theorem block_L0_4_1_0_ : Blocked 1354720 2315229 := by
  have h0 : inverseAt 1354720 2315229 0 = some (338679, 2992589) := by
    simp [inverseAt]
  have h1 : inverseAt 1354720 2315229 1 = some (1086826, 1496293) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2992589 ∧ 2992589%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 1354720 2315229 2 = some (1460899, 748145) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1496293 ∧ 1496293%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h3 : inverseAt 1354720 2315229 3 = some (1647935, 374071) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 748145 ∧ 748145%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h4 : inverseAt 1354720 2315229 4 = some (1741453, 187034) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ 374071 ∧ 374071%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2315229+1354720/2+3)%2^(4+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1354720 2315229 k 1 4 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(338679,2992589) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1086826,1496293) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1460899,748145) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(1647935,374071) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=(1741453,187034) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1354720 2315229 k c 4 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(338679,2992589) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 677354 := by omega
      have hy : c+4 = 2992593 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1086826,1496293) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2173648 := by omega
      have hy : c+4 = 1496297 := by omega
      rw [hx,hy]
      exact block_L0_4_1_0_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1460899,748145) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2921794 := by omega
      have hy : c+4 = 748149 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(1647935,374071) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3295866 := by omega
      have hy : c+4 = 374075 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h4] at hval
      have hp : (k,c)=(1741453,187034) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3482902 := by omega
      have hy : c+4 = 187038 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_4_1_1_ : Blocked 2512332 1157615 := by
  have h0 : inverseAt 2512332 1157615 0 = some (628082, 2413781) := by
    simp [inverseAt]
  have h1 : inverseAt 2512332 1157615 1 = some (1231527, 1206889) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2413781 ∧ 2413781%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 2512332 1157615 2 = some (1533249, 603443) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1206889 ∧ 1206889%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h3 : inverseAt 2512332 1157615 3 = some (1684110, 301720) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 603443 ∧ 603443%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1157615+2512332/2+3)%2^(3+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2512332 1157615 k 1 3 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(628082,2413781) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1231527,1206889) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1533249,603443) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(1684110,301720) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2512332 1157615 k c 3 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(628082,2413781) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1256160 := by omega
      have hy : c+4 = 2413785 := by omega
      rw [hx,hy]
      exact block_L0_4_1_1_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1231527,1206889) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2463050 := by omega
      have hy : c+4 = 1206893 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1533249,603443) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3066494 := by omega
      have hy : c+4 = 603447 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(1684110,301720) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3368216 := by omega
      have hy : c+4 = 301724 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 3368216 (by decide) (by decide)

private theorem block_L0_1_1_ : Blocked 2408404 1261553 := by
  have h0 : inverseAt 2408404 1261553 0 = some (602100, 2465755) := by
    simp [inverseAt]
  have h1 : inverseAt 2408404 1261553 1 = some (1218539, 1232876) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2465755 ∧ 2465755%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1261553+2408404/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2408404 1261553 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(602100,2465755) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1218539,1232876) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2408404 1261553 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(602100,2465755) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1204196 := by omega
      have hy : c+4 = 2465759 := by omega
      rw [hx,hy]
      exact block_L0_1_1_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1218539,1232876) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2437074 := by omega
      have hy : c+4 = 1232880 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_3_ : Blocked 3354564 315389 := by
  have h0 : inverseAt 3354564 315389 0 = some (838640, 1992671) := by
    simp [inverseAt]
  have h1 : inverseAt 3354564 315389 1 = some (1336808, 996334) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1992671 ∧ 1992671%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (315389+3354564/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3354564 315389 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(838640,1992671) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1336808,996334) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3354564 315389 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(838640,1992671) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1677276 := by omega
      have hy : c+4 = 1992675 := by omega
      rw [hx,hy]
      exact block_L0_1_3_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1336808,996334) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2673612 := by omega
      have hy : c+4 = 996338 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2673612 (by decide) (by decide)

private theorem block_L0_1_4_ : Blocked 3512256 157695 := by
  have h0 : inverseAt 3512256 157695 0 = some (878063, 1913823) := by
    simp [inverseAt]
  have h1 : inverseAt 3512256 157695 1 = some (1356519, 956910) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1913823 ∧ 1913823%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (157695+3512256/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3512256 157695 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(878063,1913823) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1356519,956910) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3512256 157695 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(878063,1913823) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1756122 := by omega
      have hy : c+4 = 1913827 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1356519,956910) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2713034 := by omega
      have hy : c+4 = 956914 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_4_0_ : Blocked 1748956 1920997 := by
  have h0 : inverseAt 1748956 1920997 0 = some (437238, 2795475) := by
    simp [inverseAt]
  have h1 : inverseAt 1748956 1920997 1 = some (1136107, 1397736) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2795475 ∧ 2795475%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1920997+1748956/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1748956 1920997 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(437238,2795475) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1136107,1397736) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1748956 1920997 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(437238,2795475) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 874472 := by omega
      have hy : c+4 = 2795479 := by omega
      rw [hx,hy]
      exact block_L0_4_0_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1136107,1397736) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2272210 := by omega
      have hy : c+4 = 1397740 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_4_1_ : Blocked 2709452 960499 := by
  have h0 : inverseAt 2709452 960499 0 = some (677362, 2315225) := by
    simp [inverseAt]
  have h1 : inverseAt 2709452 960499 1 = some (1256168, 1157611) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2315225 ∧ 2315225%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 2709452 960499 2 = some (1545571, 578804) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1157611 ∧ 1157611%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (960499+2709452/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2709452 960499 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(677362,2315225) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1256168,1157611) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1545571,578804) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2709452 960499 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(677362,2315225) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1354720 := by omega
      have hy : c+4 = 2315229 := by omega
      rw [hx,hy]
      exact block_L0_4_1_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1256168,1157611) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2512332 := by omega
      have hy : c+4 = 1157615 := by omega
      rw [hx,hy]
      exact block_L0_4_1_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1545571,578804) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3091138 := by omega
      have hy : c+4 = 578808 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_1_ : Blocked 2293720 1376241 := by
  have h0 : inverseAt 2293720 1376241 0 = some (573429, 2523101) := by
    simp [inverseAt]
  have h1 : inverseAt 2293720 1376241 1 = some (1204204, 1261549) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2523101 ∧ 2523101%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 2293720 1376241 2 = some (1519591, 630773) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1261549 ∧ 1261549%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h3 : inverseAt 2293720 1376241 3 = some (1677284, 315385) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 630773 ∧ 630773%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h4 : inverseAt 2293720 1376241 4 = some (1756130, 157691) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ 315385 ∧ 315385%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h5 : inverseAt 2293720 1376241 5 = some (1795553, 78844) := by
    rw [inverseAt, h4]
    have hc : 3 ≤ 157691 ∧ 157691%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1376241+2293720/2+3)%2^(5+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2293720 1376241 k 1 5 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(573429,2523101) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1204204,1261549) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1519591,630773) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(1677284,315385) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=(1756130,157691) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h5] at hval
      have hp : (k,1)=(1795553,78844) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2293720 1376241 k c 5 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(573429,2523101) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1146854 := by omega
      have hy : c+4 = 2523105 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1204204,1261549) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2408404 := by omega
      have hy : c+4 = 1261553 := by omega
      rw [hx,hy]
      exact block_L0_1_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1519591,630773) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3039178 := by omega
      have hy : c+4 = 630777 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(1677284,315385) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3354564 := by omega
      have hy : c+4 = 315389 := by omega
      rw [hx,hy]
      exact block_L0_1_3_
    · subst t
      rw [h4] at hval
      have hp : (k,c)=(1756130,157691) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3512256 := by omega
      have hy : c+4 = 157695 := by omega
      rw [hx,hy]
      exact block_L0_1_4_
    · subst t
      rw [h5] at hval
      have hp : (k,c)=(1795553,78844) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3591102 := by omega
      have hy : c+4 = 78848 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_3_ : Blocked 3325896 344061 := by
  have h0 : inverseAt 3325896 344061 0 = some (831473, 2007009) := by
    simp [inverseAt]
  have h1 : inverseAt 3325896 344061 1 = some (1333225, 1003503) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2007009 ∧ 2007009%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 3325896 344061 2 = some (1584101, 501750) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1003503 ∧ 1003503%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (344061+3325896/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3325896 344061 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(831473,2007009) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1333225,1003503) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1584101,501750) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3325896 344061 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(831473,2007009) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1662942 := by omega
      have hy : c+4 = 2007013 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1333225,1003503) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2666446 := by omega
      have hy : c+4 = 1003507 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1584101,501750) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3168198 := by omega
      have hy : c+4 = 501754 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L0_4_ : Blocked 3497924 172031 := by
  have h0 : inverseAt 3497924 172031 0 = some (874480, 1920993) := by
    simp [inverseAt]
  have h1 : inverseAt 3497924 172031 1 = some (1354728, 960495) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1920993 ∧ 1920993%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 3497924 172031 2 = some (1594852, 480246) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 960495 ∧ 960495%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (172031+3497924/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3497924 172031 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(874480,1920993) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1354728,960495) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1594852,480246) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3497924 172031 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(874480,1920993) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1748956 := by omega
      have hy : c+4 = 1920997 := by omega
      rw [hx,hy]
      exact block_L0_4_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1354728,960495) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2709452 := by omega
      have hy : c+4 = 960499 := by omega
      rw [hx,hy]
      exact block_L0_4_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1594852,480246) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3189700 := by omega
      have hy : c+4 = 480250 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 3189700 (by decide) (by decide)

private theorem block_L0_ : Blocked 1834976 1834989 := by
  have h0 : inverseAt 1834976 1834989 0 = some (458743, 2752477) := by
    simp [inverseAt]
  have h1 : inverseAt 1834976 1834989 1 = some (1146862, 1376237) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2752477 ∧ 2752477%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 1834976 1834989 2 = some (1490921, 688117) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1376237 ∧ 1376237%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h3 : inverseAt 1834976 1834989 3 = some (1662950, 344057) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 688117 ∧ 688117%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h4 : inverseAt 1834976 1834989 4 = some (1748964, 172027) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ 344057 ∧ 344057%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h5 : inverseAt 1834976 1834989 5 = some (1791971, 86012) := by
    rw [inverseAt, h4]
    have hc : 3 ≤ 172027 ∧ 172027%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1834989+1834976/2+3)%2^(5+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1834976 1834989 k 1 5 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(458743,2752477) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1146862,1376237) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1490921,688117) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(1662950,344057) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=(1748964,172027) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h5] at hval
      have hp : (k,1)=(1791971,86012) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1834976 1834989 k c 5 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(458743,2752477) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 917482 := by omega
      have hy : c+4 = 2752481 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1146862,1376237) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2293720 := by omega
      have hy : c+4 = 1376241 := by omega
      rw [hx,hy]
      exact block_L0_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1490921,688117) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2981838 := by omega
      have hy : c+4 = 688121 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(1662950,344057) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3325896 := by omega
      have hy : c+4 = 344061 := by omega
      rw [hx,hy]
      exact block_L0_3_
    · subst t
      rw [h4] at hval
      have hp : (k,c)=(1748964,172027) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3497924 := by omega
      have hy : c+4 = 172031 := by omega
      rw [hx,hy]
      exact block_L0_4_
    · subst t
      rw [h5] at hval
      have hp : (k,c)=(1791971,86012) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3583938 := by omega
      have hy : c+4 = 86016 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

theorem feeder0_not_reached : ¬BB6.Agent1.Reach 1834976 1834989 :=
  blocked_no_reach _ _ block_L0_

private theorem block_L1_0_0_0_1_1_1_0_ : Blocked 1206880 2463063 := by
  have h0 : inverseAt 1206880 2463063 0 = some (301719, 3066503) := by
    simp [inverseAt]
  have h1 : inverseAt 1206880 2463063 1 = some (1068345, 1533250) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3066503 ∧ 3066503%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2463063+1206880/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1206880 2463063 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(301719,3066503) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1068345,1533250) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1206880 2463063 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(301719,3066503) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 603434 := by omega
      have hy : c+4 = 3066507 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1068345,1533250) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2136686 := by omega
      have hy : c+4 = 1533254 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_0_1_2_0_0_ : Blocked 748136 2921807 := by
  have h0 : inverseAt 748136 2921807 0 = some (187033, 3295875) := by
    simp [inverseAt]
  have h1 : inverseAt 748136 2921807 1 = some (1011002, 1647936) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3295875 ∧ 3295875%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2921807+748136/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 748136 2921807 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(187033,3295875) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1011002,1647936) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 748136 2921807 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(187033,3295875) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 374062 := by omega
      have hy : c+4 = 3295879 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1011002,1647936) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2022000 := by omega
      have hy : c+4 = 1647940 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2022000 (by decide) (by decide)

private theorem block_L1_0_0_0_1_1_1_ : Blocked 2413772 1256173 := by
  have h0 : inverseAt 2413772 1256173 0 = some (603442, 2463059) := by
    simp [inverseAt]
  have h1 : inverseAt 2413772 1256173 1 = some (1219207, 1231528) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2463059 ∧ 2463059%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1256173+2413772/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2413772 1256173 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(603442,2463059) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1219207,1231528) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2413772 1256173 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(603442,2463059) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1206880 := by omega
      have hy : c+4 = 2463063 := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_1_1_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1219207,1231528) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2438410 := by omega
      have hy : c+4 = 1231532 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_0_1_1_2_ : Blocked 3041856 628087 := by
  have h0 : inverseAt 3041856 628087 0 = some (760463, 2149015) := by
    simp [inverseAt]
  have h1 : inverseAt 3041856 628087 1 = some (1297717, 1074506) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2149015 ∧ 2149015%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (628087+3041856/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3041856 628087 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(760463,2149015) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1297717,1074506) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3041856 628087 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(760463,2149015) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1520922 := by omega
      have hy : c+4 = 2149019 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1297717,1074506) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2595430 := by omega
      have hy : c+4 = 1074510 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_0_1_2_0_ : Blocked 1496284 2173661 := by
  have h0 : inverseAt 1496284 2173661 0 = some (374070, 2921803) := by
    simp [inverseAt]
  have h1 : inverseAt 1496284 2173661 1 = some (1104521, 1460900) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2921803 ∧ 2921803%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2173661+1496284/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1496284 2173661 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(374070,2921803) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1104521,1460900) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1496284 2173661 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(374070,2921803) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 748136 := by omega
      have hy : c+4 = 2921807 := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_2_0_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1104521,1460900) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2209038 := by omega
      have hy : c+4 = 1460904 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_0_1_2_1_ : Blocked 2583112 1086831 := by
  have h0 : inverseAt 2583112 1086831 0 = some (645777, 2378387) := by
    simp [inverseAt]
  have h1 : inverseAt 2583112 1086831 1 = some (1240374, 1189192) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2378387 ∧ 2378387%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1086831+2583112/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2583112 1086831 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(645777,2378387) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1240374,1189192) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2583112 1086831 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(645777,2378387) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1291550 := by omega
      have hy : c+4 = 2378391 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1240374,1189192) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2480744 := by omega
      have hy : c+4 = 1189196 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2480744 (by decide) (by decide)

private theorem block_L1_0_0_0_1_1_ : Blocked 2315216 1354733 := by
  have h0 : inverseAt 2315216 1354733 0 = some (578803, 2512341) := by
    simp [inverseAt]
  have h1 : inverseAt 2315216 1354733 1 = some (1206888, 1256169) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2512341 ∧ 2512341%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 2315216 1354733 2 = some (1520930, 628083) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1256169 ∧ 1256169%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h3 : inverseAt 2315216 1354733 3 = some (1677951, 314040) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 628083 ∧ 628083%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1354733+2315216/2+3)%2^(3+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2315216 1354733 k 1 3 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(578803,2512341) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1206888,1256169) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1520930,628083) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(1677951,314040) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2315216 1354733 k c 3 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(578803,2512341) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1157602 := by omega
      have hy : c+4 = 2512345 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1206888,1256169) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2413772 := by omega
      have hy : c+4 = 1256173 := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_1_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1520930,628083) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3041856 := by omega
      have hy : c+4 = 628087 := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_1_2_
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(1677951,314040) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3355898 := by omega
      have hy : c+4 = 314044 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_0_1_2_ : Blocked 2992580 677367 := by
  have h0 : inverseAt 2992580 677367 0 = some (748144, 2173657) := by
    simp [inverseAt]
  have h1 : inverseAt 2992580 677367 1 = some (1291558, 1086827) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2173657 ∧ 2173657%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 2992580 677367 2 = some (1563265, 543412) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1086827 ∧ 1086827%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (677367+2992580/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2992580 677367 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(748144,2173657) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1291558,1086827) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1563265,543412) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2992580 677367 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(748144,2173657) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1496284 := by omega
      have hy : c+4 = 2173661 := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_2_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1291558,1086827) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2583112 := by omega
      have hy : c+4 = 1086831 := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_2_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1563265,543412) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3126526 := by omega
      have hy : c+4 = 543416 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_0_1_ : Blocked 1920984 1748969 := by
  have h0 : inverseAt 1920984 1748969 0 = some (480245, 2709461) := by
    simp [inverseAt]
  have h1 : inverseAt 1920984 1748969 1 = some (1157610, 1354729) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2709461 ∧ 2709461%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 1920984 1748969 2 = some (1496292, 677363) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1354729 ∧ 1354729%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h3 : inverseAt 1920984 1748969 3 = some (1665633, 338680) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 677363 ∧ 677363%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1748969+1920984/2+3)%2^(3+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1920984 1748969 k 1 3 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(480245,2709461) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1157610,1354729) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1496292,677363) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(1665633,338680) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1920984 1748969 k c 3 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(480245,2709461) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 960486 := by omega
      have hy : c+4 = 2709465 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1157610,1354729) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2315216 := by omega
      have hy : c+4 = 1354733 := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1496292,677363) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2992580 := by omega
      have hy : c+4 = 677367 := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_2_
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(1665633,338680) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3331262 := by omega
      have hy : c+4 = 338684 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_1_0_0_0_ : Blocked 315376 3354577 := by
  have h0 : inverseAt 315376 3354577 0 = some (78843, 3512265) := by
    simp [inverseAt]
  have h1 : inverseAt 315376 3354577 1 = some (956909, 1756131) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3512265 ∧ 3512265%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 315376 3354577 2 = some (1395942, 878064) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1756131 ∧ 1756131%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (3354577+315376/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 315376 3354577 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(78843,3512265) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(956909,1756131) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1395942,878064) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 315376 3354577 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(78843,3512265) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 157682 := by omega
      have hy : c+4 = 3512269 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(956909,1756131) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1913814 := by omega
      have hy : c+4 = 1756135 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1395942,878064) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2791880 := by omega
      have hy : c+4 = 878068 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2791880 (by decide) (by decide)

private theorem block_L1_1_0_0_2_ : Blocked 2831304 838645 := by
  have h0 : inverseAt 2831304 838645 0 = some (707825, 2254297) := by
    simp [inverseAt]
  have h1 : inverseAt 2831304 838645 1 = some (1271399, 1127147) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2254297 ∧ 2254297%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 2831304 838645 2 = some (1553186, 563572) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1127147 ∧ 1127147%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (838645+2831304/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2831304 838645 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(707825,2254297) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1271399,1127147) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1553186,563572) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2831304 838645 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(707825,2254297) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1415646 := by omega
      have hy : c+4 = 2254301 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1271399,1127147) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2542794 := by omega
      have hy : c+4 = 1127151 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1553186,563572) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3106368 := by omega
      have hy : c+4 = 563576 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 3106368 (by decide) (by decide)

private theorem block_L1_1_0_0_3_ : Blocked 3250624 419323 := by
  have h0 : inverseAt 3250624 419323 0 = some (812655, 2044635) := by
    simp [inverseAt]
  have h1 : inverseAt 3250624 419323 1 = some (1323814, 1022316) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2044635 ∧ 2044635%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (419323+3250624/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3250624 419323 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(812655,2044635) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1323814,1022316) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3250624 419323 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(812655,2044635) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1625306 := by omega
      have hy : c+4 = 2044639 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1323814,1022316) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2647624 := by omega
      have hy : c+4 = 1022320 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2647624 (by decide) (by decide)

private theorem block_L1_1_2_1_0_ : Blocked 1300960 2368987 := by
  have h0 : inverseAt 1300960 2368987 0 = some (325239, 3019467) := by
    simp [inverseAt]
  have h1 : inverseAt 1300960 2368987 1 = some (1080106, 1509732) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3019467 ∧ 3019467%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2368987+1300960/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1300960 2368987 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(325239,3019467) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1080106,1509732) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1300960 2368987 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(325239,3019467) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 650474 := by omega
      have hy : c+4 = 3019471 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1080106,1509732) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2160208 := by omega
      have hy : c+4 = 1509736 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2160208 (by decide) (by decide)

private theorem block_L1_1_2_3_0_ : Blocked 1701464 1968479 := by
  have h0 : inverseAt 1701464 1968479 0 = some (425365, 2819211) := by
    simp [inverseAt]
  have h1 : inverseAt 1701464 1968479 1 = some (1130168, 1409604) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2819211 ∧ 2819211%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1968479+1701464/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1701464 1968479 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(425365,2819211) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1130168,1409604) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1701464 1968479 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(425365,2819211) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 850726 := by omega
      have hy : c+4 = 2819215 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1130168,1409604) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2260332 := by omega
      have hy : c+4 = 1409608 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2260332 (by decide) (by decide)

private theorem block_L1_0_0_0_ : Blocked 344048 3325909 := by
  have h0 : inverseAt 344048 3325909 0 = some (86011, 3497933) := by
    simp [inverseAt]
  have h1 : inverseAt 344048 3325909 1 = some (960494, 1748965) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3497933 ∧ 3497933%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 344048 3325909 2 = some (1397735, 874481) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1748965 ∧ 1748965%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h3 : inverseAt 344048 3325909 3 = some (1616355, 437239) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 874481 ∧ 874481%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h4 : inverseAt 344048 3325909 4 = some (1725665, 218618) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ 437239 ∧ 437239%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (3325909+344048/2+3)%2^(4+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 344048 3325909 k 1 4 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(86011,3497933) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(960494,1748965) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1397735,874481) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(1616355,437239) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=(1725665,218618) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 344048 3325909 k c 4 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(86011,3497933) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 172018 := by omega
      have hy : c+4 = 3497937 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(960494,1748965) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1920984 := by omega
      have hy : c+4 = 1748969 := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1397735,874481) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2795466 := by omega
      have hy : c+4 = 874485 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(1616355,437239) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3232706 := by omega
      have hy : c+4 = 437243 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h4] at hval
      have hp : (k,c)=(1725665,218618) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3451326 := by omega
      have hy : c+4 = 218622 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_0_1_ : Blocked 2007000 1662955 := by
  have h0 : inverseAt 2007000 1662955 0 = some (501749, 2666455) := by
    simp [inverseAt]
  have h1 : inverseAt 2007000 1662955 1 = some (1168363, 1333226) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2666455 ∧ 2666455%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1662955+2007000/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2007000 1662955 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(501749,2666455) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1168363,1333226) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2007000 1662955 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(501749,2666455) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1003494 := by omega
      have hy : c+4 = 2666459 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1168363,1333226) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2336722 := by omega
      have hy : c+4 = 1333230 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_1_0_0_ : Blocked 630764 3039191 := by
  have h0 : inverseAt 630764 3039191 0 = some (157690, 3354573) := by
    simp [inverseAt]
  have h1 : inverseAt 630764 3039191 1 = some (996333, 1677285) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3354573 ∧ 3354573%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 630764 3039191 2 = some (1415654, 838641) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1677285 ∧ 1677285%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h3 : inverseAt 630764 3039191 3 = some (1625314, 419319) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 838641 ∧ 838641%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h4 : inverseAt 630764 3039191 4 = some (1730144, 209658) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ 419319 ∧ 419319%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (3039191+630764/2+3)%2^(4+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 630764 3039191 k 1 4 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(157690,3354573) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(996333,1677285) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1415654,838641) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(1625314,419319) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=(1730144,209658) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 630764 3039191 k c 4 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(157690,3354573) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 315376 := by omega
      have hy : c+4 = 3354577 := by omega
      rw [hx,hy]
      exact block_L1_1_0_0_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(996333,1677285) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1992662 := by omega
      have hy : c+4 = 1677289 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1415654,838641) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2831304 := by omega
      have hy : c+4 = 838645 := by omega
      rw [hx,hy]
      exact block_L1_1_0_0_2_
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(1625314,419319) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3250624 := by omega
      have hy : c+4 = 419323 := by omega
      rw [hx,hy]
      exact block_L1_1_0_0_3_
    · subst t
      rw [h4] at hval
      have hp : (k,c)=(1730144,209658) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3460284 := by omega
      have hy : c+4 = 209662 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 3460284 (by decide) (by decide)

private theorem block_L1_1_2_1_ : Blocked 2601932 1068017 := by
  have h0 : inverseAt 2601932 1068017 0 = some (650482, 2368983) := by
    simp [inverseAt]
  have h1 : inverseAt 2601932 1068017 1 = some (1242728, 1184490) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2368983 ∧ 2368983%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1068017+2601932/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2601932 1068017 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(650482,2368983) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1242728,1184490) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2601932 1068017 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(650482,2368983) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1300960 := by omega
      have hy : c+4 = 2368987 := by omega
      rw [hx,hy]
      exact block_L1_1_2_1_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1242728,1184490) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2485452 := by omega
      have hy : c+4 = 1184494 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2485452 (by decide) (by decide)

private theorem block_L1_1_2_3_ : Blocked 3402940 267005 := by
  have h0 : inverseAt 3402940 267005 0 = some (850734, 1968475) := by
    simp [inverseAt]
  have h1 : inverseAt 3402940 267005 1 = some (1342853, 984236) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1968475 ∧ 1968475%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (267005+3402940/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3402940 267005 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(850734,1968475) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1342853,984236) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3402940 267005 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(850734,1968475) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1701464 := by omega
      have hy : c+4 = 1968479 := by omega
      rw [hx,hy]
      exact block_L1_1_2_3_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1342853,984236) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2685702 := by omega
      have hy : c+4 = 984240 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_1_2_4_ : Blocked 3536440 133503 := by
  have h0 : inverseAt 3536440 133503 0 = some (884109, 1901723) := by
    simp [inverseAt]
  have h1 : inverseAt 3536440 133503 1 = some (1359540, 950860) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 1901723 ∧ 1901723%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (133503+3536440/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3536440 133503 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(884109,1901723) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1359540,950860) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3536440 133503 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(884109,1901723) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1768214 := by omega
      have hy : c+4 = 1901727 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1359540,950860) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2719076 := by omega
      have hy : c+4 = 950864 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2719076 (by decide) (by decide)

private theorem block_L1_0_0_ : Blocked 688108 2981851 := by
  have h0 : inverseAt 688108 2981851 0 = some (172026, 3325905) := by
    simp [inverseAt]
  have h1 : inverseAt 688108 2981851 1 = some (1003502, 1662951) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3325905 ∧ 3325905%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 688108 2981851 2 = some (1419240, 831474) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1662951 ∧ 1662951%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2981851+688108/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 688108 2981851 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(172026,3325905) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1003502,1662951) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1419240,831474) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 688108 2981851 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(172026,3325905) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 344048 := by omega
      have hy : c+4 = 3325909 := by omega
      rw [hx,hy]
      exact block_L1_0_0_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1003502,1662951) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2007000 := by omega
      have hy : c+4 = 1662955 := by omega
      rw [hx,hy]
      exact block_L1_0_0_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1419240,831474) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2838476 := by omega
      have hy : c+4 = 831478 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2838476 (by decide) (by decide)

private theorem block_L1_1_0_ : Blocked 1261540 2408417 := by
  have h0 : inverseAt 1261540 2408417 0 = some (315384, 3039187) := by
    simp [inverseAt]
  have h1 : inverseAt 1261540 2408417 1 = some (1075181, 1519592) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 3039187 ∧ 3039187%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2408417+1261540/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1261540 2408417 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(315384,3039187) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1075181,1519592) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1261540 2408417 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(315384,3039187) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 630764 := by omega
      have hy : c+4 = 3039191 := by omega
      rw [hx,hy]
      exact block_L1_1_0_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1075181,1519592) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2150358 := by omega
      have hy : c+4 = 1519596 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_1_2_ : Blocked 3067848 602105 := by
  have h0 : inverseAt 3067848 602105 0 = some (766961, 2136029) := by
    simp [inverseAt]
  have h1 : inverseAt 3067848 602105 1 = some (1300968, 1068013) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2136029 ∧ 2136029%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 3067848 602105 2 = some (1567971, 534005) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1068013 ∧ 1068013%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h3 : inverseAt 3067848 602105 3 = some (1701472, 267001) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 534005 ∧ 534005%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h4 : inverseAt 3067848 602105 4 = some (1768222, 133499) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ 267001 ∧ 267001%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h5 : inverseAt 3067848 602105 5 = some (1801597, 66748) := by
    rw [inverseAt, h4]
    have hc : 3 ≤ 133499 ∧ 133499%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (602105+3067848/2+3)%2^(5+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3067848 602105 k 1 5 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(766961,2136029) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1300968,1068013) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1567971,534005) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(1701472,267001) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=(1768222,133499) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h5] at hval
      have hp : (k,1)=(1801597,66748) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 3067848 602105 k c 5 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(766961,2136029) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1533918 := by omega
      have hy : c+4 = 2136033 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1300968,1068013) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2601932 := by omega
      have hy : c+4 = 1068017 := by omega
      rw [hx,hy]
      exact block_L1_1_2_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1567971,534005) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3135938 := by omega
      have hy : c+4 = 534009 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(1701472,267001) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3402940 := by omega
      have hy : c+4 = 267005 := by omega
      rw [hx,hy]
      exact block_L1_1_2_3_
    · subst t
      rw [h4] at hval
      have hp : (k,c)=(1768222,133499) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3536440 := by omega
      have hy : c+4 = 133503 := by omega
      rw [hx,hy]
      exact block_L1_1_2_4_
    · subst t
      rw [h5] at hval
      have hp : (k,c)=(1801597,66748) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3603190 := by omega
      have hy : c+4 = 66752 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)

private theorem block_L1_0_ : Blocked 1376228 2293733 := by
  have h0 : inverseAt 1376228 2293733 0 = some (344056, 2981847) := by
    simp [inverseAt]
  have h1 : inverseAt 1376228 2293733 1 = some (1089518, 1490922) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2981847 ∧ 2981847%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (2293733+1376228/2+3)%2^(1+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1376228 2293733 k 1 1 hk hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(344056,2981847) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1089518,1490922) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 1376228 2293733 k c 1 h hn
    have hcases : t=0 ∨ t=1 := by omega
    rcases hcases with h0 | h1
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(344056,2981847) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 688108 := by omega
      have hy : c+4 = 2981851 := by omega
      rw [hx,hy]
      exact block_L1_0_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1089518,1490922) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2179032 := by omega
      have hy : c+4 = 1490926 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 2179032 (by decide) (by decide)

private theorem block_L1_1_ : Blocked 2523092 1146867 := by
  have h0 : inverseAt 2523092 1146867 0 = some (630772, 2408413) := by
    simp [inverseAt]
  have h1 : inverseAt 2523092 1146867 1 = some (1232875, 1204205) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2408413 ∧ 2408413%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 2523092 1146867 2 = some (1533926, 602101) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1204205 ∧ 1204205%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h3 : inverseAt 2523092 1146867 3 = some (1684451, 301049) := by
    rw [inverseAt, h2]
    have hc : 3 ≤ 602101 ∧ 602101%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h4 : inverseAt 2523092 1146867 4 = some (1759713, 150523) := by
    rw [inverseAt, h3]
    have hc : 3 ≤ 301049 ∧ 301049%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h5 : inverseAt 2523092 1146867 5 = some (1797344, 75260) := by
    rw [inverseAt, h4]
    have hc : 3 ≤ 150523 ∧ 150523%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (1146867+2523092/2+3)%2^(5+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2523092 1146867 k 1 5 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(630772,2408413) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1232875,1204205) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1533926,602101) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h3] at hval
      have hp : (k,1)=(1684451,301049) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h4] at hval
      have hp : (k,1)=(1759713,150523) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h5] at hval
      have hp : (k,1)=(1797344,75260) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2523092 1146867 k c 5 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(630772,2408413) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1261540 := by omega
      have hy : c+4 = 2408417 := by omega
      rw [hx,hy]
      exact block_L1_1_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1232875,1204205) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2465746 := by omega
      have hy : c+4 = 1204209 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1533926,602101) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3067848 := by omega
      have hy : c+4 = 602105 := by omega
      rw [hx,hy]
      exact block_L1_1_2_
    · subst t
      rw [h3] at hval
      have hp : (k,c)=(1684451,301049) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3368898 := by omega
      have hy : c+4 = 301053 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h4] at hval
      have hp : (k,c)=(1759713,150523) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3519422 := by omega
      have hy : c+4 = 150527 := by omega
      rw [hx,hy]
      exact Blocked.modLeaf _ _ (by omega) (by omega) (by omega) (by omega)
    · subst t
      rw [h5] at hval
      have hp : (k,c)=(1797344,75260) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3594684 := by omega
      have hy : c+4 = 75264 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 3594684 (by decide) (by decide)

private theorem block_L1_ : Blocked 2752468 917495 := by
  have h0 : inverseAt 2752468 917495 0 = some (688116, 2293729) := by
    simp [inverseAt]
  have h1 : inverseAt 2752468 917495 1 = some (1261548, 1146863) := by
    rw [inverseAt, h0]
    have hc : 3 ≤ 2293729 ∧ 2293729%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have h2 : inverseAt 2752468 917495 2 = some (1548264, 573430) := by
    rw [inverseAt, h1]
    have hc : 3 ≤ 1146863 ∧ 1146863%2=1 := by omega
    simp only [hc, true_and, ite_true, Option.some.injEq, Prod.mk.injEq]
  have hn : (917495+2752468/2+3)%2^(2+1) ≠ 0 := by decide
  apply Blocked.feeder
  · omega
  · omega
  · omega
  · intro k hk
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2752468 917495 k 1 2 hk hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,1)=(688116,2293729) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h1] at hval
      have hp : (k,1)=(1261548,1146863) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
    · subst t
      rw [h2] at hval
      have hp : (k,1)=(1548264,573430) := (Option.some.inj hval).symm
      have hc := (Prod.mk.inj hp).2
      omega
  · intro k c h hc
    obtain ⟨t,ht,hval⟩ := inverse_at_depth_le_of_nonzero_mod 2752468 917495 k c 2 h hn
    have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with h0 | h1 | h2
    · subst t
      rw [h0] at hval
      have hp : (k,c)=(688116,2293729) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 1376228 := by omega
      have hy : c+4 = 2293733 := by omega
      rw [hx,hy]
      exact block_L1_0_
    · subst t
      rw [h1] at hval
      have hp : (k,c)=(1261548,1146863) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 2523092 := by omega
      have hy : c+4 = 1146867 := by omega
      rw [hx,hy]
      exact block_L1_1_
    · subst t
      rw [h2] at hval
      have hp : (k,c)=(1548264,573430) := (Option.some.inj hval).symm
      obtain ⟨hk,hcval⟩ := Prod.mk.inj hp
      have hx : 2*k-4 = 3096524 := by omega
      have hy : c+4 = 573434 := by omega
      rw [hx,hy]
      apply Blocked.powerLeaf
      · omega
      · omega
      · omega
      · exact no_fourteen_power_in_fixed_band 3096524 (by decide) (by decide)

theorem feeder1_not_reached : ¬BB6.Agent1.Reach 2752468 917495 :=
  blocked_no_reach _ _ block_L1_

theorem blank_no_critical_18 :
    ¬BB6.Agent1.Reach 2 (14*2^18-2*18-10) := by
  intro hr
  have hh : BB6.Agent1.Reach 2
      (14*2^(16*1+2)-2*(16*1+2)-10) := by simpa using hr
  rcases (two_sector_critical_iff_feeders 1 (by decide)).mp hh with h0 | h1
  · have heq : 4*u2 1-4=1834976 ∧ 4*u2 1+9=1834989 := by decide
    rcases heq with ⟨heq1,heq2⟩
    rw [heq1,heq2] at h0
    exact feeder0_not_reached h0
  · have heq : 6*u2 1-2=2752468 ∧ 2*u2 1+5=917495 := by decide
    rcases heq with ⟨heq1,heq2⟩
    rw [heq1,heq2] at h1
    exact feeder1_not_reached h1

#print axioms blank_no_critical_18
end BB6.Agent33Q1
