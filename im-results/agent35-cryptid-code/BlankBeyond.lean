import Lean.Elab.Tactic.Omega
import ASixBlankTrace

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- Actual blank tape: first unary B return after the proven 166M trace. -/
theorem blank1187331039 :
    run 1187331039 blank = init (List.replicate 73759 true) := by
  have ht : 1187331039 = 166999736 + (12*9219*9219+49*9219+40) := by decide
  rw [ht, run_add, blank166999736]
  simpa [init] using full_B_nil 9219

/-- Exact blank A return, across a further 7.2 billion primitive steps. -/
theorem blank8442192549 :
    run 8442192549 blank = init (List.replicate 196697 true) := by
  have ht : 8442192549 = 1187331039 + (12*24586*24586+49*24586+44) := by decide
  rw [ht, run_add, blank1187331039]
  simpa [init] using full_A_nil 24586

/-- The second actual E encounter produces another six-one trailing packet. -/
theorem blank60030635984 :
    run 60030635984 blank =
      init (List.replicate 524523 true ++ false :: List.replicate 6 true) := by
  have ht : 60030635984 = 8442192549 + (12*65565*65565+49*65565+50) := by decide
  rw [ht, run_add, blank8442192549]
  simpa only [Nat.reduceMul,Nat.reduceAdd] using full_E_nil 65565

/-- Genuine B branch consumes the explicit zero, joining the six-one packet. -/
theorem blank426871706605 :
    run 426871706605 blank = init (List.replicate 1398741 true) := by
  have ht : 426871706605 =
    60030635984 + (12*174841*174841+49*174841+40) := by decide
  rw [ht, run_add, blank60030635984]
  have hb := full_B 174841 (List.replicate 6 true)
  simpa [init, List.replicate_append_replicate] using hb

/-- A fourth large blank unary return, fully certified. -/
theorem blank3035529732856 :
    run 3035529732856 blank = init (List.replicate 3729983 true) := by
  have ht : 3035529732856 =
    426871706605 + (12*466247*466247+49*466247+40) := by decide
  rw [ht, run_add, blank426871706605]
  simpa [init] using full_B_nil 466247

/-- Third source-certified E encounter, at >21 trillion primitive steps. -/
theorem blank21585935003077 :
    run 21585935003077 blank =
      init (List.replicate 9946619 true ++ false :: List.replicate 6 true) := by
  have ht : 21585935003077 =
    3035529732856 + (12*1243327*1243327+49*1243327+50) := by decide
  rw [ht, run_add, blank3035529732856]
  simpa only [Nat.reduceMul,Nat.reduceAdd] using full_E_nil 1243327

#print axioms blank1187331039
#print axioms blank8442192549
#print axioms blank60030635984
#print axioms blank426871706605
#print axioms blank3035529732856
#print axioms blank21585935003077
end CryptidBoundary
