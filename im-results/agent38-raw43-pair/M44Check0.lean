import M44DataBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 10000
namespace BB6.Agent38M44
theorem checked0_0 : ([0,1,2,3,4,5,6] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_1 : ([7,8] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_2 : ([9] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_3 : ([10] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_4 : ([11] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_5 : ([12,13,14,15,16,17,18,19] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_6 : ([20] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_7 : ([21,22,23] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_8 : ([24] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_9 : ([25] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_10 : ([26,27,28] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_11 : ([29,30,31,32,33,34] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_12 : ([35,36,37,38,39] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_13 : ([40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111] : List Nat).all (checkRow cert 0) = true := by decide
theorem checked0_14 : ([112,113] : List Nat).all (checkRow cert 0) = true := by decide
theorem closed0 : checkQ cert 0 = true := by
  change ((([0,1,2,3,4,5,6] : List Nat) ++ ([7,8] : List Nat) ++ ([9] : List Nat) ++ ([10] : List Nat) ++ ([11] : List Nat) ++ ([12,13,14,15,16,17,18,19] : List Nat) ++ ([20] : List Nat) ++ ([21,22,23] : List Nat) ++ ([24] : List Nat) ++ ([25] : List Nat) ++ ([26,27,28] : List Nat) ++ ([29,30,31,32,33,34] : List Nat) ++ ([35,36,37,38,39] : List Nat) ++ ([40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111] : List Nat) ++ ([112,113] : List Nat)).all (checkRow cert 0)) = true
  simp only [List.all_append,checked0_0,checked0_1,checked0_2,checked0_3,checked0_4,checked0_5,checked0_6,checked0_7,checked0_8,checked0_9,checked0_10,checked0_11,checked0_12,checked0_13,checked0_14,Bool.and_self]
end BB6.Agent38M44
