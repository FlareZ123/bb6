import M44DataBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 10000
namespace BB6.Agent38M44
theorem checked3_0 : ([0,1,2,3,4,5,6,7,8,9,10,11] : List Nat).all (checkRow cert 3) = true := by decide
theorem checked3_1 : ([12,13,14,15,16,17,18,19,20] : List Nat).all (checkRow cert 3) = true := by decide
theorem checked3_2 : ([21,22,23,24,25,26,27,28,29,30,31] : List Nat).all (checkRow cert 3) = true := by decide
theorem checked3_3 : ([32,33,34,35,36,37,38,39,40,41,42,43,44] : List Nat).all (checkRow cert 3) = true := by decide
theorem checked3_4 : ([45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113] : List Nat).all (checkRow cert 3) = true := by decide
theorem closed3 : checkQ cert 3 = true := by
  change ((([0,1,2,3,4,5,6,7,8,9,10,11] : List Nat) ++ ([12,13,14,15,16,17,18,19,20] : List Nat) ++ ([21,22,23,24,25,26,27,28,29,30,31] : List Nat) ++ ([32,33,34,35,36,37,38,39,40,41,42,43,44] : List Nat) ++ ([45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113] : List Nat)).all (checkRow cert 3)) = true
  simp only [List.all_append,checked3_0,checked3_1,checked3_2,checked3_3,checked3_4,Bool.and_self]
end BB6.Agent38M44
