import W7Text

open BB6Row146Conjugacy
namespace W7

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem certA : checkText blankA (N (c 508932094)) (include_str "A.jsonl")=true := by native_decide
theorem certN : checkText (N (a 22 [1])) (N (a 38626190 [262144])) (include_str "N.jsonl")=true := by native_decide
theorem certQ : checkText (Q (a 14 [1])) (Q (a 38101896 [262144])) (include_str "Q.jsonl")=true := by native_decide
theorem certDentry : checkText blankD (D (c 70691118354036414594808423388)
    (c 10456559309013950571) (c 939468133961604901)) (include_str "Dentry.jsonl")=true := by native_decide
theorem certD : checkText (D (a 100 [1,0,0]) (a 130 [0,1,0]) (a 30 [0,0,1]))
    (D (a 454337500 [1048576,0,0]) (a 10 [0,1,0]) (a 6 [0,0,1])) (include_str "D.jsonl")=true := by native_decide
theorem certE : checkText (D (a 349479900 [1048576]) (c 5759218639205926131) (c 13))
    (Q (a 23036877419765819664 [8589934592])) (include_str "E.jsonl")=true := by native_decide

theorem closedEvidence : Evidence :=
  ⟨checkText_sound _ _ _ certA,checkText_sound _ _ _ certN,checkText_sound _ _ _ certQ,
   checkText_sound _ _ _ certDentry,checkText_sound _ _ _ certD,checkText_sound _ _ _ certE⟩

theorem historical146_never : ∀ n, run row146 n (blank .A)≠none := blankA_never closedEvidence
theorem historical411_never : ∀ n, run row411 n (blank .A)≠none := row411_never closedEvidence

#print axioms historical146_never
#print axioms historical411_never
end W7
