import D100Delayed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7D100Delayed
open BB6Coverage BB6Coverage.Agent31Pump
theorem entry : run0 table 7 ⟨0,[],[]⟩ = some (A 1 0 2) := by rfl
theorem epoch000 : run0 table 14 (A 1 0 2) = some (A 2 0 3) := by
  have h := epoch 0 0 0 2 0 3 8 1 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch001 : run0 table 14 (A 2 0 3) = some (A 3 1 3) := by
  have h := epoch 0 1 0 3 1 3 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch002 : run0 table 20 (A 3 1 3) = some (A 6 1 2) := by
  have h := epoch 0 2 1 3 1 2 10 5 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch003 : run0 table 45 (A 6 1 2) = some (A 10 1 1) := by
  have h := epoch 1 2 1 2 1 1 10 5 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch004 : run0 table 131 (A 10 1 1) = some (A 16 0 2) := by
  have h := epoch 3 0 1 1 0 2 12 3 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch005 : run0 table 259 (A 16 0 2) = some (A 22 0 3) := by
  have h := epoch 5 0 0 2 0 3 8 1 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch006 : run0 table 441 (A 22 0 3) = some (A 30 0 4) := by
  have h := epoch 7 0 0 3 0 4 8 1 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch007 : run0 table 677 (A 30 0 4) = some (A 41 0 4) := by
  have h := epoch 9 2 0 4 0 4 11 4 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch008 : run0 table 1275 (A 41 0 4) = some (A 55 1 4) := by
  have h := epoch 13 1 0 4 1 4 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch009 : run0 table 2306 (A 55 1 4) = some (A 76 0 4) := by
  have h := epoch 18 0 1 4 0 4 12 3 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch010 : run0 table 4239 (A 76 0 4) = some (A 102 0 5) := by
  have h := epoch 25 0 0 4 0 5 8 1 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch011 : run0 table 7181 (A 102 0 5) = some (A 137 0 5) := by
  have h := epoch 33 2 0 5 0 5 11 4 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch012 : run0 table 13019 (A 137 0 5) = some (A 183 1 5) := by
  have h := epoch 45 1 0 5 1 5 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch013 : run0 table 22760 (A 183 1 5) = some (A 246 1 4) := by
  have h := epoch 60 2 1 5 1 4 10 5 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch014 : run0 table 40925 (A 246 1 4) = some (A 330 1 3) := by
  have h := epoch 81 2 1 4 1 3 10 5 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch015 : run0 table 73377 (A 330 1 3) = some (A 442 1 2) := by
  have h := epoch 109 2 1 3 1 2 10 5 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch016 : run0 table 132467 (A 442 1 2) = some (A 592 0 2) := by
  have h := epoch 147 0 1 2 0 2 12 3 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch017 : run0 table 236611 (A 592 0 2) = some (A 790 0 3) := by
  have h := epoch 197 0 0 2 0 3 8 1 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch018 : run0 table 420025 (A 790 0 3) = some (A 1054 0 4) := by
  have h := epoch 263 0 0 3 0 4 8 1 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch019 : run0 table 745889 (A 1054 0 4) = some (A 1406 0 5) := by
  have h := epoch 351 0 0 4 0 5 8 1 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch020 : run0 table 1323050 (A 1406 0 5) = some (A 1875 1 5) := by
  have h := epoch 468 1 0 5 1 5 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch021 : run0 table 2348132 (A 1875 1 5) = some (A 2502 1 4) := by
  have h := epoch 624 2 1 5 1 4 10 5 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch022 : run0 table 4179181 (A 2502 1 4) = some (A 3338 1 3) := by
  have h := epoch 833 2 1 4 1 3 10 5 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch023 : run0 table 7440406 (A 3338 1 3) = some (A 4451 2 3) := by
  have h := epoch 1112 1 1 3 2 3 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch024 : run0 table 13223925 (A 4451 2 3) = some (A 5935 3 3) := by
  have h := epoch 1483 1 2 3 3 3 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch025 : run0 table 23512512 (A 5935 3 3) = some (A 7919 0 2) := by
  have h := epoch 1978 0 3 3 0 2 15 6 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch026 : run0 table 41836081 (A 7919 0 2) = some (A 10559 1 2) := by
  have h := epoch 2639 1 0 2 1 2 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch027 : run0 table 74367041 (A 10559 1 2) = some (A 14079 2 2) := by
  have h := epoch 3519 1 1 2 2 2 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch028 : run0 table 132178358 (A 14079 2 2) = some (A 18776 0 2) := by
  have h := epoch 4692 2 2 2 0 2 14 7 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch029 : run0 table 235094300 (A 18776 0 2) = some (A 25035 1 2) := by
  have h := epoch 6258 1 0 2 1 2 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch030 : run0 table 417892572 (A 25035 1 2) = some (A 33382 1 1) := by
  have h := epoch 8344 2 1 2 1 1 10 5 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch031 : run0 table 743072207 (A 33382 1 1) = some (A 44512 0 2) := by
  have h := epoch 11127 0 1 1 0 2 12 3 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch032 : run0 table 1321101331 (A 44512 0 2) = some (A 59350 0 3) := by
  have h := epoch 14837 0 0 2 0 3 8 1 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch033 : run0 table 2348578425 (A 59350 0 3) = some (A 79134 0 4) := by
  have h := epoch 19783 0 0 3 0 4 8 1 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch034 : run0 table 4174977957 (A 79134 0 4) = some (A 105513 0 4) := by
  have h := epoch 26377 2 0 4 0 4 11 4 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch035 : run0 table 7422241650 (A 105513 0 4) = some (A 140685 0 4) := by
  have h := epoch 35170 2 0 4 0 4 11 4 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch036 : run0 table 13195174422 (A 140685 0 4) = some (A 187581 0 4) := by
  have h := epoch 46894 2 0 4 0 4 11 4 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch037 : run0 table 23458192070 (A 187581 0 4) = some (A 250109 0 4) := by
  have h := epoch 62526 2 0 4 0 4 11 4 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch038 : run0 table 41703924991 (A 250109 0 4) = some (A 333479 1 4) := by
  have h := epoch 83369 1 0 4 1 4 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch039 : run0 table 74140051721 (A 333479 1 4) = some (A 444639 2 4) := by
  have h := epoch 111159 1 1 4 2 4 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch040 : run0 table 131803597718 (A 444639 2 4) = some (A 592856 0 3) := by
  have h := epoch 148212 2 2 4 0 3 14 7 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch041 : run0 table 234320998300 (A 592856 0 3) = some (A 790475 1 3) := by
  have h := epoch 197618 1 0 3 1 3 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch042 : run0 table 416570048829 (A 790475 1 3) = some (A 1053967 2 3) := by
  have h := epoch 263491 1 1 3 2 3 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch043 : run0 table 740569561242 (A 1053967 2 3) = some (A 1405293 1 2) := by
  have h := epoch 351322 0 2 3 1 2 11 4 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch044 : run0 table 1316568889590 (A 1405293 1 2) = some (A 1873726 1 1) := by
  have h := epoch 468430 2 1 2 1 1 10 5 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch045 : run0 table 2340575450695 (A 1873726 1 1) = some (A 2498304 0 2) := by
  have h := epoch 624575 0 1 1 0 2 12 3 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch046 : run0 table 4161021080327 (A 2498304 0 2) = some (A 3331073 0 2) := by
  have h := epoch 832767 2 0 2 0 2 11 4 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch047 : run0 table 7397377101491 (A 3331073 0 2) = some (A 4441431 1 2) := by
  have h := epoch 1110357 1 0 2 1 2 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch048 : run0 table 13150883248520 (A 4441431 1 2) = some (A 5921910 1 1) := by
  have h := epoch 1480476 2 1 2 1 1 10 5 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch049 : run0 table 23379359183197 (A 5921910 1 1) = some (A 7895882 1 0) := by
  have h := epoch 1973969 2 1 1 1 0 10 5 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch050 : run0 table 41563330656854 (A 7895882 1 0) = some (A 10527843 2 0) := by
  have h := epoch 2631960 1 1 0 2 0 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch051 : run0 table 73890343386746 (A 10527843 2 0) = some (A 14037128 0 2) := by
  have h := epoch 3509280 2 2 0 0 2 14 7 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch052 : run0 table 131360693128396 (A 14037128 0 2) = some (A 18716171 1 2) := by
  have h := epoch 4679042 1 0 2 1 2 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch053 : run0 table 233530106560125 (A 18716171 1 2) = some (A 24954895 2 2) := by
  have h := epoch 6238723 1 1 2 2 2 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch054 : run0 table 415164647748506 (A 24954895 2 2) = some (A 33273197 1 1) := by
  have h := epoch 8318298 0 2 2 1 1 11 4 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch055 : run0 table 738070547735599 (A 33273197 1 1) = some (A 44364263 2 1) := by
  have h := epoch 11091065 1 1 1 2 1 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch056 : run0 table 1312125383691081 (A 44364263 2 1) = some (A 59152351 3 1) := by
  have h := epoch 14788087 1 2 1 3 1 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch057 : run0 table 2332667381646576 (A 59152351 3 1) = some (A 78869807 0 2) := by
  have h := epoch 19717450 0 3 1 0 2 15 6 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch058 : run0 table 4146964593334129 (A 78869807 0 2) = some (A 105159743 1 2) := by
  have h := epoch 26289935 1 0 2 1 2 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch059 : run0 table 7372381417469761 (A 105159743 1 2) = some (A 140212991 2 2) := by
  have h := epoch 35053247 1 1 2 2 2 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
theorem epoch060 : run0 table 13106455744225025 (A 140212991 2 2) = some (A 186950655 3 2) := by
  have h := epoch 46737663 1 2 2 3 2 7 2 (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h
def final : Z0 := ⟨4,[],true::rep W 124633772 ++ Z 2⟩
theorem last : run0 table 23300365372837554 (A 186950655 3 2) = some final := by
  have h := lastEpoch 62316884 (Z 2)
  simpa only [A,final,scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul,show U 3 = [true,true,true] by rfl,List.cons_append,List.nil_append] using h
theorem reached : run0 table 53257978073992275 ⟨0,[],[]⟩ = some final := by
  have h0 := entry
  have h1 := join0 h0 epoch000
  have h2 := join0 h1 epoch001
  have h3 := join0 h2 epoch002
  have h4 := join0 h3 epoch003
  have h5 := join0 h4 epoch004
  have h6 := join0 h5 epoch005
  have h7 := join0 h6 epoch006
  have h8 := join0 h7 epoch007
  have h9 := join0 h8 epoch008
  have h10 := join0 h9 epoch009
  have h11 := join0 h10 epoch010
  have h12 := join0 h11 epoch011
  have h13 := join0 h12 epoch012
  have h14 := join0 h13 epoch013
  have h15 := join0 h14 epoch014
  have h16 := join0 h15 epoch015
  have h17 := join0 h16 epoch016
  have h18 := join0 h17 epoch017
  have h19 := join0 h18 epoch018
  have h20 := join0 h19 epoch019
  have h21 := join0 h20 epoch020
  have h22 := join0 h21 epoch021
  have h23 := join0 h22 epoch022
  have h24 := join0 h23 epoch023
  have h25 := join0 h24 epoch024
  have h26 := join0 h25 epoch025
  have h27 := join0 h26 epoch026
  have h28 := join0 h27 epoch027
  have h29 := join0 h28 epoch028
  have h30 := join0 h29 epoch029
  have h31 := join0 h30 epoch030
  have h32 := join0 h31 epoch031
  have h33 := join0 h32 epoch032
  have h34 := join0 h33 epoch033
  have h35 := join0 h34 epoch034
  have h36 := join0 h35 epoch035
  have h37 := join0 h36 epoch036
  have h38 := join0 h37 epoch037
  have h39 := join0 h38 epoch038
  have h40 := join0 h39 epoch039
  have h41 := join0 h40 epoch040
  have h42 := join0 h41 epoch041
  have h43 := join0 h42 epoch042
  have h44 := join0 h43 epoch043
  have h45 := join0 h44 epoch044
  have h46 := join0 h45 epoch045
  have h47 := join0 h46 epoch046
  have h48 := join0 h47 epoch047
  have h49 := join0 h48 epoch048
  have h50 := join0 h49 epoch049
  have h51 := join0 h50 epoch050
  have h52 := join0 h51 epoch051
  have h53 := join0 h52 epoch052
  have h54 := join0 h53 epoch053
  have h55 := join0 h54 epoch054
  have h56 := join0 h55 epoch055
  have h57 := join0 h56 epoch056
  have h58 := join0 h57 epoch057
  have h59 := join0 h58 epoch058
  have h60 := join0 h59 epoch059
  have h61 := join0 h60 epoch060
  simpa only [Nat.reduceAdd] using join0 h61 last
theorem hole : table (4,false) = none := rfl
#print axioms reached
#print axioms hole
end BB6.Agent7D100Delayed
