import Lean.Elab.Tactic.Omega
import BlankFurther

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

namespace CryptidBoundary

/-- Extend the authentic blank trajectory through a B return. The right
    tape begins with (01)^4 0 1^4 at the preceding physical checkpoint. -/
theorem blank141146256421739780247 :
    BB6.BoundaryPadding.ObsEq
      (run 141146256421739780247 blank)
      (init (List.replicate 25434628784 true ++
        (oppairs 3 ++ false :: List.replicate 4 true))) := by
  have h0 := blank19848692333528818046
  have hp : oppairs 4 ++ false :: List.replicate 4 true =
      false :: true :: (oppairs 3 ++ false :: List.replicate 4 true) := by decide
  rw [hp] at h0
  have hn : 9537985793 = 9537985791+2 := by decide
  rw [hn] at h0
  rw [finish_packet_init 9537985791
    (false :: true :: (oppairs 3 ++ false :: List.replicate 4 true))] at h0
  have ht : 141146256421739780247 =
    19848692333528818046 + (12*3179328597*3179328597+49*3179328597+40) := by decide
  rw [ht, run_add]
  have h := BB6.BoundaryPadding.source_congr
    (12*3179328597*3179328597+49*3179328597+40) h0
  rw [full_B_one 3179328597 (oppairs 3 ++ false :: List.replicate 4 true)] at h
  simpa only [Nat.reduceMul,Nat.reduceAdd] using h

/-- An E triple-pairs return, still from the original blank start. -/
theorem blank1003706711874695788461 :
    BB6.BoundaryPadding.ObsEq
      (run 1003706711874695788461 blank)
      (⟨[],false,List.replicate 67825676761 true ++
        (oppairs 5 ++ false :: [true]),5⟩ : Cfg) := by
  have h0 := blank141146256421739780247
  have hp : oppairs 3 ++ false :: List.replicate 4 true =
    false :: (pairs 3 ++ ([true,true,true] ++ [true])) := by decide
  rw [hp] at h0
  have hn : 25434628784 = 3*8478209594+2 := by decide
  rw [hn] at h0
  have ht : 1003706711874695788461 =
    141146256421739780247 +
      (12*8478209594*8478209594+49*8478209594+58+6*3) := by decide
  rw [ht, run_add]
  have h := BB6.BoundaryPadding.source_congr
    (12*8478209594*8478209594+49*8478209594+58+6*3) h0
  rw [full_E_triple_pairs 8478209594 3 [true]] at h
  simpa only [Nat.reduceMul,Nat.reduceAdd] using h

#print axioms blank141146256421739780247
#print axioms blank1003706711874695788461

end CryptidBoundary
