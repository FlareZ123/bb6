import FastFullBoolean
import BroadTwoConeHaltingCriterion
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 8192

namespace BB6.Agent2ConeNoveltyCheck

/-- Source-equivalent Boolean of the earlier complete pre-phase high sieve
    is evaluated at the two canonical high-stop parameters whose
    source-inverse gaps have been newly proved. -/
#eval BB6.Agent27FastBool.fastPriorHighAllowedBool 1 5
#eval BB6.Agent27FastBool.fastPriorHighAllowedBool 56 6

/-- Agent27's entire previous exact full-phase high gate: its outcomes
    determine whether the new source-certified image holes are also
    strict relative to that published full-phase criterion. -/
#eval BB6.Agent27FastBool.fastHighAllowedFullBool 1 5
#eval BB6.Agent27FastBool.fastHighAllowedFullBool 56 6

end BB6.Agent2ConeNoveltyCheck
