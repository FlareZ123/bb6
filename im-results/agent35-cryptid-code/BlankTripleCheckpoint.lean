import Lean.Elab.Tactic.Omega
import BlankSixCheckpoint
import CryptidTriplePairs

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- The next actual blank-origin E boundary is consumed by the uniformly
    verified alternating-pairs plus three-ones macro. -/
theorem blank1091552640110031 :
    run 1091552640110031 blank =
      init (List.replicate 70731519 true ++
        (oppairs 4 ++ [false])) := by
  have ht : 1091552640110031 =
      153499683790798 +
        (12*8841439*8841439+49*8841439+58+6*2) := by decide
  rw [ht, run_add, blank153499683790798]
  have hp : packetSixBlank =
    false :: (pairs 2 ++ ([true,true,true] ++ ([] : List Bool))) := by decide
  rw [hp]
  have h := full_E_triple_pairs 8841439 2 ([] : List Bool)
  have hnum : 8*8841439+9 = 70731519+2 := by omega
  rw [hnum] at h
  have hf := finish_packet_init 70731519 (oppairs 4 ++ [false])
  simpa only [Nat.reduceMul, Nat.reduceAdd, List.append_nil] using h.trans hf

#print axioms blank1091552640110031
end CryptidBoundary
