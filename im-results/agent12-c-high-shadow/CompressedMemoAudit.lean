import CompressedMemo
import PurePowerSource

namespace BB6.Agent12CompressedMemoAudit
open BB6.Agent12CompressedMemo BB6.Agent12PurePower

def pureAudit (r s : Nat) : Nat × Nat × Nat × Nat × Bool × Bool :=
  let j := familyJ r s
  let m := familyM r
  let y := familyK r s
  (r,s,m,(j+3).log2,oldHighSurvives j m,compressedExcluded 24 256 (2*j+3) y)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
#eval ((List.range 6).flatMap fun i => (List.range 3).map fun s => pureAudit (i+3) s)

end BB6.Agent12CompressedMemoAudit
