import S4PrefixNinthR171050
import S4PrefixNinthR171052
import S4PrefixNinthR171051
import S4PrefixNinthR171049
import Lean.Elab.Tactic.Omega

namespace S4PrefixNinth
open S4PrefixCausal S4PrefixEighthCycle S4Prefix5457 S4Toggle S4PrefixSeven

set_option maxRecDepth 500000
set_option maxHeartbeats 0

def cycle9Phase1 : List Nat := cycle8PeriodicStart ++ [171052]
def cycle9Phase2 : List Nat := cycle8PeriodicStart ++ [171051]
def cycle9Phase3 : List Nat := cycle8PeriodicStart ++ [171049]

theorem block9_start :
    prefixRunFast 20480 cycle9Start = cycle9Phase1 := by
  simpa [cycle9Start, cycle9Phase1, r171050] using
    block20480_ninth 171050

theorem block9_phase1 :
    prefixRunFast 20480 cycle9Phase1 = cycle9Phase2 := by
  simpa [cycle9Phase1, cycle9Phase2, r171052] using
    block20480_ninth 171052

theorem block9_phase2 :
    prefixRunFast 20480 cycle9Phase2 = cycle9Phase3 := by
  simpa [cycle9Phase2, cycle9Phase3, r171051] using
    block20480_ninth 171051

theorem block9_phase3 :
    prefixRunFast 20480 cycle9Phase3 = cycle9Start := by
  simpa [cycle9Phase3, cycle9Start, r171049] using
    block20480_ninth 171049

/-- The nine-digit prefix returns after four eighth-prefix blocks. -/
theorem cycle9_period81920 :
    prefixRunFast 81920 cycle9Start = cycle9Start := by
  calc
    prefixRunFast 81920 cycle9Start =
        prefixRunFast (61440 + 20480) cycle9Start := by rfl
    _ = prefixRunFast 20480 (prefixRunFast 61440 cycle9Start) :=
      prefixRunFast_add 61440 20480 cycle9Start
    _ = prefixRunFast 20480
          (prefixRunFast (40960 + 20480) cycle9Start) := by
      rfl
    _ = prefixRunFast 20480
          (prefixRunFast 20480 (prefixRunFast 40960 cycle9Start)) := by
      rw [prefixRunFast_add 40960 20480 cycle9Start]
    _ = prefixRunFast 20480
          (prefixRunFast 20480
            (prefixRunFast (20480 + 20480) cycle9Start)) := by
      rfl
    _ = prefixRunFast 20480
          (prefixRunFast 20480
            (prefixRunFast 20480 (prefixRunFast 20480 cycle9Start))) := by
      rw [prefixRunFast_add 20480 20480 cycle9Start]
    _ = cycle9Start := by
      rw [block9_start, block9_phase1, block9_phase2, block9_phase3]

theorem prefixRunFast_period81920 (n : Nat) :
    prefixRunFast (n+81920) cycle9Start =
      prefixRunFast n cycle9Start := by
  rw [Nat.add_comm n 81920]
  rw [prefixRunFast_add 81920 n cycle9Start]
  rw [cycle9_period81920]

private theorem prefixRunFast_add_mul (r k : Nat) :
    prefixRunFast (r + 81920*k) cycle9Start =
      prefixRunFast r cycle9Start := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc]
      rw [prefixRunFast_period81920]
      exact ih

theorem prefixRunFast_mod81920 (n : Nat) :
    prefixRunFast n cycle9Start =
      prefixRunFast (n % 81920) cycle9Start := by
  have h : n % 81920 + 81920 * (n / 81920) = n := by omega
  calc
    prefixRunFast n cycle9Start =
        prefixRunFast (n % 81920 + 81920 * (n / 81920)) cycle9Start := by
      exact congrArg (fun x => prefixRunFast x cycle9Start) h.symm
    _ = prefixRunFast (n % 81920) cycle9Start :=
      prefixRunFast_add_mul (n % 81920) (n / 81920)

/-- Every successful original-root state after return 5457 has a
first-nine-digit prefix determined periodically modulo 81,920. -/
theorem root_nine_prefix_mod81920 (n : Nat) (U : List Nat)
    (h : prun (5457+n) seed = some U) :
    U.take 9 = prefixRunFast (n % 81920) cycle9Start := by
  calc
    U.take 9 = prefixRun n cycle9Start :=
      root_nine_prefix_from_5457 n U h
    _ = prefixRunFast n cycle9Start := by
      symm
      exact prefixRunFast_eq n cycle9Start
    _ = prefixRunFast (n % 81920) cycle9Start :=
      prefixRunFast_mod81920 n

#print axioms cycle9_period81920
#print axioms root_nine_prefix_mod81920

end S4PrefixNinth
