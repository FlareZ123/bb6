import ExactMemo

open BB6.Agent13ExactMemo

set_option maxHeartbeats 0 in
#eval ([0,2,3,6,8,10,15,16,22,27,47,82,91,159,163,170,271,328] : List Nat).filter
  (fun m => exactDecision 1 (2^(2*m+3)-(3*m+4)))
