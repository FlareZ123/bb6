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


/-- A further E-pairs return across a physically implicit trailing zero.
    The padding step is justified by the unbounded source congruence theorem. -/
theorem blank7137469949709248558298 :
    BB6.BoundaryPadding.ObsEq
      (run 7137469949709248558298 blank)
      (⟨[],false,List.replicate 180868471357 true ++
        (false :: List.replicate 18 true),5⟩ : Cfg) := by
  have h0 := blank1003706711874695788461
  have hn : 67825676761 = 67825676759+2 := by decide
  rw [hn] at h0
  rw [finish_packet_init 67825676759 (oppairs 5 ++ false :: [true])] at h0
  have hs : (oppairs 5 ++ false :: [true]) ++ [false] = false :: pairs 6 := by decide
  have hr :
    (List.replicate 67825676759 true ++ (oppairs 5 ++ false :: [true])) ++ [false] =
      List.replicate 67825676759 true ++ false :: pairs 6 := by
    rw [List.append_assoc, hs]
  have hpad := BB6.BoundaryPadding.source_init_pad 0 1
    (List.replicate 67825676759 true ++ (oppairs 5 ++ false :: [true]))
  change BB6.BoundaryPadding.ObsEq
    (init (List.replicate 67825676759 true ++ (oppairs 5 ++ false :: [true])))
    (init ((List.replicate 67825676759 true ++ (oppairs 5 ++ false :: [true])) ++ [false])) at hpad
  rw [hr] at hpad
  have h1 := BB6.Padding.cfgEq_trans h0 hpad
  have hk : 67825676759 = 3*22608558919+2 := by decide
  rw [hk] at h1
  have ht : 7137469949709248558298 =
    1003706711874695788461 +
      (12*22608558919*22608558919+49*22608558919+50+4*6) := by decide
  rw [ht, run_add]
  have h := BB6.BoundaryPadding.source_congr
    (12*22608558919*22608558919+49*22608558919+50+4*6) h1
  have he := BB6.BoundaryPadding.full_E_pairs_implicit_blank 22608558919 6
  have hh := BB6.Padding.cfgEq_trans h he
  change BB6.BoundaryPadding.ObsEq _ _ at hh
  simpa only [Nat.reduceMul,Nat.reduceAdd] using hh


/-- This exact original-blank checkpoint matches the previously conditional
    A-word projection, without relying on that projection's trace script. -/
theorem blank50755341858758075791267 :
    BB6.BoundaryPadding.ObsEq
      (run 50755341858758075791267 blank)
      (⟨[],false,List.replicate 482315923617 true ++
        (oppairs 2 ++ false :: List.replicate 15 true),5⟩ : Cfg) := by
  have h0 := blank7137469949709248558298
  have hp : List.replicate 18 true =
      [true,true,true] ++ List.replicate 15 true := by decide
  rw [hp] at h0
  have hn : 180868471357 = 180868471355+2 := by decide
  rw [hn] at h0
  rw [finish_packet_init 180868471355
    (false :: ([true,true,true] ++ List.replicate 15 true))] at h0
  have hk : 180868471355 = 3*60289490451+2 := by decide
  rw [hk] at h0
  have ht : 50755341858758075791267 =
    7137469949709248558298 +
      (12*60289490451*60289490451+49*60289490451+58) := by decide
  rw [ht, run_add]
  have h := BB6.BoundaryPadding.source_congr
    (12*60289490451*60289490451+49*60289490451+58) h0
  rw [full_E_triple_pairs 60289490451 0 (List.replicate 15 true)] at h
  simpa only [Nat.reduceMul,Nat.reduceAdd] using h

#print axioms blank141146256421739780247
#print axioms blank1003706711874695788461
#print axioms blank7137469949709248558298
#print axioms blank50755341858758075791267

end CryptidBoundary
