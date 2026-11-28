import Raw14037RootBridge

namespace Raw14037MidRecurrence
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer
set_option maxRecDepth 350000
set_option maxHeartbeats 0

def marks : Nat → List Sym
  | 0 => []
  | n+1 => [S 5, S 5, S 4] ++ marks n

def K (m : Nat) : BState :=
  ⟨4,true,
    [S 2,S 4,S 4] ++ marks m ++ U 5 (67+6*m) ++ U 6 (159-6*m) ++ [S 4],
    [S 5,S 4,S 2]⟩

theorem step_0 : execute M37 3663 (K 0) = some (10075, K 1) := by decide +kernel
theorem step_1 : execute M37 4095 (K 1) = some (11263, K 2) := by decide +kernel
theorem step_2 : execute M37 4527 (K 2) = some (12451, K 3) := by decide +kernel
theorem step_3 : execute M37 4959 (K 3) = some (13639, K 4) := by decide +kernel
theorem step_4 : execute M37 5391 (K 4) = some (14827, K 5) := by decide +kernel
theorem step_5 : execute M37 5823 (K 5) = some (16015, K 6) := by decide +kernel
theorem step_6 : execute M37 6255 (K 6) = some (17203, K 7) := by decide +kernel
theorem step_7 : execute M37 6687 (K 7) = some (18391, K 8) := by decide +kernel
theorem step_8 : execute M37 7119 (K 8) = some (19579, K 9) := by decide +kernel
theorem step_9 : execute M37 7551 (K 9) = some (20767, K 10) := by decide +kernel
theorem step_10 : execute M37 7983 (K 10) = some (21955, K 11) := by decide +kernel
theorem step_11 : execute M37 8415 (K 11) = some (23143, K 12) := by decide +kernel
theorem step_12 : execute M37 8847 (K 12) = some (24331, K 13) := by decide +kernel
theorem step_13 : execute M37 9279 (K 13) = some (25519, K 14) := by decide +kernel
theorem step_14 : execute M37 9711 (K 14) = some (26707, K 15) := by decide +kernel
theorem step_15 : execute M37 10143 (K 15) = some (27895, K 16) := by decide +kernel
theorem step_16 : execute M37 10575 (K 16) = some (29083, K 17) := by decide +kernel
theorem step_17 : execute M37 11007 (K 17) = some (30271, K 18) := by decide +kernel
theorem step_18 : execute M37 11439 (K 18) = some (31459, K 19) := by decide +kernel
theorem step_19 : execute M37 11871 (K 19) = some (32647, K 20) := by decide +kernel
theorem step_20 : execute M37 12303 (K 20) = some (33835, K 21) := by decide +kernel
theorem step_21 : execute M37 12735 (K 21) = some (35023, K 22) := by decide +kernel
theorem step_22 : execute M37 13167 (K 22) = some (36211, K 23) := by decide +kernel
theorem step_23 : execute M37 13599 (K 23) = some (37399, K 24) := by decide +kernel
theorem step_24 : execute M37 14031 (K 24) = some (38587, K 25) := by decide +kernel
theorem step_25 : execute M37 14463 (K 25) = some (39775, K 26) := by decide +kernel

theorem jump :
    execute M37 235638 (K 0) = some (648050, K 26) := by
  decide +kernel

theorem jump_run :
    run M37 648050 (K 0).prim = some (K 26).prim := by
  exact execute_sound M37 235638 648050 (K 0) (K 26) jump

#print axioms step_0
#print axioms step_1
#print axioms step_2
#print axioms step_3
#print axioms step_4
#print axioms step_5
#print axioms step_6
#print axioms step_7
#print axioms step_8
#print axioms step_9
#print axioms step_10
#print axioms step_11
#print axioms step_12
#print axioms step_13
#print axioms step_14
#print axioms step_15
#print axioms step_16
#print axioms step_17
#print axioms step_18
#print axioms step_19
#print axioms step_20
#print axioms step_21
#print axioms step_22
#print axioms step_23
#print axioms step_24
#print axioms step_25
#print axioms jump
#print axioms jump_run
end Raw14037MidRecurrence
