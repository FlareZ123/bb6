import Lean.Elab.Tactic.Omega
import ASixBlankTrace

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- Convert a raw F-on-zero configuration with a full unary tape
    back to the canonical fixed F section without expanding the list. -/
theorem finish_unary (n : Nat) :
    (⟨[],false,List.replicate (n+2) true,5⟩ : Cfg) =
      init (List.replicate n true) := by
  unfold init
  rw [show n+2=2+n by omega]
  rw [←List.replicate_append_replicate]
  rfl

theorem full_B_nil_to_init (k : Nat) :
    run (12*k*k+49*k+40) (init (List.replicate (3*k) true)) =
      init (List.replicate (8*k+7) true) := by
  have h := full_B_nil k
  have he : 8*k+9=(8*k+7)+2 := by omega
  rw [he] at h
  exact h.trans (finish_unary _)

theorem full_A_nil_to_init (k : Nat) :
    run (12*k*k+49*k+44) (init (List.replicate (3*k+1) true)) =
      init (List.replicate (8*k+9) true) := by
  have h := full_A_nil k
  have he : 8*k+11=(8*k+9)+2 := by omega
  rw [he] at h
  exact h.trans (finish_unary _)

theorem full_B_six (k : Nat) :
    run (12*k*k+49*k+40)
      (init (List.replicate (3*k) true ++ false :: List.replicate 6 true)) =
      init (List.replicate (8*k+13) true) := by
  have h := full_B k (List.replicate 6 true)
  have hr : List.replicate (8*k+9) true ++ List.replicate 6 true =
      List.replicate (8*k+15) true := by
    rw [List.replicate_append_replicate]
    congr 1
  rw [hr] at h
  have he : 8*k+15=(8*k+13)+2 := by omega
  rw [he] at h
  exact h.trans (finish_unary _)

/-- Actual blank tape: first unary B return after the proven 166M trace. -/
theorem blank1187331039 :
    run 1187331039 blank = init (List.replicate 73759 true) := by
  have ht : 1187331039 = 166999736 + (12*9219*9219+49*9219+40) := by decide
  rw [ht, run_add, blank166999736]
  simpa only [Nat.reduceMul, Nat.reduceAdd] using full_B_nil_to_init 9219

/-- Exact blank A return, across a further 7.2 billion primitive steps. -/
theorem blank8442192549 :
    run 8442192549 blank = init (List.replicate 196697 true) := by
  have ht : 8442192549 = 1187331039 + (12*24586*24586+49*24586+44) := by decide
  rw [ht, run_add, blank1187331039]
  simpa only [Nat.reduceMul, Nat.reduceAdd] using full_A_nil_to_init 24586

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
  simpa only [Nat.reduceMul, Nat.reduceAdd] using full_B_six 174841

/-- A fourth large blank unary return, fully certified. -/
theorem blank3035529732856 :
    run 3035529732856 blank = init (List.replicate 3729983 true) := by
  have ht : 3035529732856 =
    426871706605 + (12*466247*466247+49*466247+40) := by decide
  rw [ht, run_add, blank426871706605]
  simpa only [Nat.reduceMul, Nat.reduceAdd] using full_B_nil_to_init 466247

/-- Third source-certified E encounter, at >21 trillion primitive steps. -/
theorem blank21585935003077 :
    run 21585935003077 blank =
      init (List.replicate 9946619 true ++ false :: List.replicate 6 true) := by
  have ht : 21585935003077 =
    3035529732856 + (12*1243327*1243327+49*1243327+50) := by decide
  rw [ht, run_add, blank3035529732856]
  simpa only [Nat.reduceMul,Nat.reduceAdd] using full_E_nil 1243327

#print axioms full_B_nil_to_init
#print axioms full_A_nil_to_init
#print axioms full_B_six
#print axioms blank1187331039
#print axioms blank8442192549
#print axioms blank60030635984
#print axioms blank426871706605
#print axioms blank3035529732856
#print axioms blank21585935003077
end CryptidBoundary
