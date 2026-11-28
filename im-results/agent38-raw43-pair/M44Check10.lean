import M44DataBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 10000
namespace BB6.Agent38M44
theorem checked10_0 : ([0,1,2] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_1 : ([3,4,5,6] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_2 : ([7] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_3 : ([8] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_4 : ([9] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_5 : ([10] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_6 : ([11] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_7 : ([12,13] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_8 : ([14] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_9 : ([15,16] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_10 : ([17] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_11 : ([18] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_12 : ([19] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_13 : ([20] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_14 : ([21,22] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_15 : ([23] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_16 : ([24] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_17 : ([25] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_18 : ([26] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_19 : ([27,28,29] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_20 : ([30] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_21 : ([31,32,33,34,35] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_22 : ([36] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_23 : ([37] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_24 : ([38] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_25 : ([39] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_26 : ([40] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_27 : ([41] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_28 : ([42,43,44,45,46] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_29 : ([47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_30 : ([96,97,98,99,100,101,102] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_31 : ([103,104,105,106,107,108,109,110] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_32 : ([111,112] : List Nat).all (checkRow cert 10) = true := by decide
theorem checked10_33 : ([113] : List Nat).all (checkRow cert 10) = true := by decide
theorem closed10 : checkQ cert 10 = true := by
  change ((([0,1,2] : List Nat) ++ ([3,4,5,6] : List Nat) ++ ([7] : List Nat) ++ ([8] : List Nat) ++ ([9] : List Nat) ++ ([10] : List Nat) ++ ([11] : List Nat) ++ ([12,13] : List Nat) ++ ([14] : List Nat) ++ ([15,16] : List Nat) ++ ([17] : List Nat) ++ ([18] : List Nat) ++ ([19] : List Nat) ++ ([20] : List Nat) ++ ([21,22] : List Nat) ++ ([23] : List Nat) ++ ([24] : List Nat) ++ ([25] : List Nat) ++ ([26] : List Nat) ++ ([27,28,29] : List Nat) ++ ([30] : List Nat) ++ ([31,32,33,34,35] : List Nat) ++ ([36] : List Nat) ++ ([37] : List Nat) ++ ([38] : List Nat) ++ ([39] : List Nat) ++ ([40] : List Nat) ++ ([41] : List Nat) ++ ([42,43,44,45,46] : List Nat) ++ ([47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95] : List Nat) ++ ([96,97,98,99,100,101,102] : List Nat) ++ ([103,104,105,106,107,108,109,110] : List Nat) ++ ([111,112] : List Nat) ++ ([113] : List Nat)).all (checkRow cert 10)) = true
  simp only [List.all_append,checked10_0,checked10_1,checked10_2,checked10_3,checked10_4,checked10_5,checked10_6,checked10_7,checked10_8,checked10_9,checked10_10,checked10_11,checked10_12,checked10_13,checked10_14,checked10_15,checked10_16,checked10_17,checked10_18,checked10_19,checked10_20,checked10_21,checked10_22,checked10_23,checked10_24,checked10_25,checked10_26,checked10_27,checked10_28,checked10_29,checked10_30,checked10_31,checked10_32,checked10_33,Bool.and_self]
end BB6.Agent38M44
