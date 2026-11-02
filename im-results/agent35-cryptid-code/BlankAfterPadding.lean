import Lean.Elab.Tactic.Omega
import BlankBContin
import CryptidThree

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- A genuine blank-origin section at 392 quadrillion has, in its
    observationally correct infinite tape, exactly ten trailing 1s. -/
theorem blank392_eq_Ethree :
    BB6.BoundaryPadding.ObsEq
      (run 392515651843862508 blank)
      (init (List.replicate 1341279251 true ++
        false :: ([true,true,true] ++ List.replicate 7 true))) := by
  have h := blank392515651843862508
  have hp : List.replicate 10 true =
      [true,true,true] ++ List.replicate 7 true := by decide
  rw [hp] at h
  have he := finish_packet_init 1341279251
    (false :: ([true,true,true] ++ List.replicate 7 true))
  have hn : 1341279253 = 1341279251+2 := by decide
  rw [hn] at h
  rw [he] at h
  exact h

/-- Physically accurate original blank tape after >2.79 quintillion
    raw primitive steps. The finite configuration encoding may have a
    different count of redundant terminal blank cells. -/
theorem blank2791222372148762301 :
    BB6.BoundaryPadding.ObsEq
      (run 2791222372148762301 blank)
      (⟨[],false,List.replicate 3576744673 true ++
        (CryptidBoundary.packetThree ++ List.replicate 7 true),5⟩ : Cfg) := by
  have ht : 2791222372148762301 =
    392515651843862508 +
       (12*447093083*447093083+49*447093083+58) := by decide
  rw [ht, run_add]
  have h := BB6.BoundaryPadding.source_congr
    (12*447093083*447093083+49*447093083+58)
    blank392_eq_Ethree
  have he := full_E_three 447093083 (List.replicate 7 true)
  rw [he] at h
  simpa only [Nat.reduceMul, Nat.reduceAdd] using h

#print axioms blank392_eq_Ethree
#print axioms blank2791222372148762301
end CryptidBoundary
