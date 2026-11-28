import M44DataBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 10000
namespace BB6.Agent38M44
theorem checked1_0 : ([0,1,2,3,4,5,6] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_1 : ([7] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_2 : ([8] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_3 : ([9] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_4 : ([10] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_5 : ([11] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_6 : ([12,13,14,15,16,17,18,19] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_7 : ([20] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_8 : ([21,22,23] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_9 : ([24] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_10 : ([25] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_11 : ([26,27,28,29,30,31] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_12 : ([32,33,34,35,36,37,38] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_13 : ([39,40,41,42,43,44] : List Nat).all (checkRow cert 1) = true := by decide
theorem checked1_14 : ([45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113] : List Nat).all (checkRow cert 1) = true := by decide
theorem closed1 : checkQ cert 1 = true := by
  change ((([0,1,2,3,4,5,6] : List Nat) ++ ([7] : List Nat) ++ ([8] : List Nat) ++ ([9] : List Nat) ++ ([10] : List Nat) ++ ([11] : List Nat) ++ ([12,13,14,15,16,17,18,19] : List Nat) ++ ([20] : List Nat) ++ ([21,22,23] : List Nat) ++ ([24] : List Nat) ++ ([25] : List Nat) ++ ([26,27,28,29,30,31] : List Nat) ++ ([32,33,34,35,36,37,38] : List Nat) ++ ([39,40,41,42,43,44] : List Nat) ++ ([45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113] : List Nat)).all (checkRow cert 1)) = true
  simp only [List.all_append,checked1_0,checked1_1,checked1_2,checked1_3,checked1_4,checked1_5,checked1_6,checked1_7,checked1_8,checked1_9,checked1_10,checked1_11,checked1_12,checked1_13,checked1_14,Bool.and_self]
end BB6.Agent38M44
