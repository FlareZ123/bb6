import Lean.Elab.Tactic.Omega
import BlankAfterPadding
import CryptidTriplePairs

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- The source-certified 2.79-quintillion checkpoint already has a
    two-pair/three-one right prefix, with four further ones afterwards. -/
theorem blank2791_eq_Etriple :
    BB6.BoundaryPadding.ObsEq
      (run 2791222372148762301 blank)
      (init (List.replicate 3576744671 true ++
        false :: (pairs 2 ++
          ([true,true,true] ++ List.replicate 4 true)))) := by
  have h := blank2791222372148762301
  have hp : packetThree ++ List.replicate 7 true =
    false :: (pairs 2 ++
      ([true,true,true] ++ List.replicate 4 true)) := by decide
  rw [hp] at h
  have hn : 3576744673 = 3576744671+2 := by decide
  rw [hn] at h
  rw [finish_packet_init 3576744671
    (false :: (pairs 2 ++
      ([true,true,true] ++ List.replicate 4 true)))] at h
  exact h

/-- Further source-verified genuine blank execution beyond
    19,848,692,333,528,818,046 primitive six-state machine steps. -/
theorem blank19848692333528818046 :
    BB6.BoundaryPadding.ObsEq
      (run 19848692333528818046 blank)
      (⟨[],false,List.replicate 9537985793 true ++
        (oppairs 4 ++ false :: List.replicate 4 true),5⟩ : Cfg) := by
  have ht : 19848692333528818046 =
    2791222372148762301 +
      (12*1192248223*1192248223+49*1192248223+58+6*2) := by decide
  rw [ht, run_add]
  have h := BB6.BoundaryPadding.source_congr
    (12*1192248223*1192248223+49*1192248223+58+6*2)
    blank2791_eq_Etriple
  have he := full_E_triple_pairs 1192248223 2 (List.replicate 4 true)
  rw [he] at h
  simpa only [Nat.reduceMul,Nat.reduceAdd] using h

#print axioms blank2791_eq_Etriple
#print axioms blank19848692333528818046
end CryptidBoundary
