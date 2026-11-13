import NoFatalGuard
import BB429SourceE1Return
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429RootNoFatalPrefix

open BB429OddExcursion BB429NoFatalGuard BB429SourceE1Return

/-- The genuine blank zipper origin for the original #429 source table. -/
def rootBlank : Zipper := z 0 [] false []

/-- The exact Junc(11,0,98) endpoint word, using the source's canonical
    `ones` and `pairs01` constructors. This is definitionally the word
    used by `BB429FinishScanEDelta.junc 11 0 98`. -/
def rootEndpoint : Zipper :=
  z 0 (true :: (pairs01 11 ++ ones 5)) true
    (true :: (pairs01 0 ++ ones 98 ++ [false,true]))

/-- Record every C/0 instruction start, with its primitive time, head
    displacement from the blank root, and immediate right-neighbor bit. -/
def cZeroEventTrace : Nat → Nat → Int → Zipper → List (Nat × Int × Bool)
  | 0, t, delta, c =>
      if c.state == 2 && !c.current then
        [(t, delta, c.right.getD 0 false)]
      else []
  | n+1, t, delta, c =>
      let here :=
        if c.state == 2 && !c.current then
          [(t, delta, c.right.getD 0 false)]
        else []
      match BB429OddExcursion.action c.state c.current with
      | none => here
      | some (_, _, rightward) =>
          match BB429OddExcursion.one c with
          | none => here
          | some d =>
              here ++ cZeroEventTrace n (t+1)
                (delta + (if rightward then 1 else -1)) d

/-- The original blank-root zipper run reaches Junc(11,0,98) after
    9,243 primitive transitions without ever executing fatal C/01.
    The proof is a kernel-reducing finite computation, not a simulation
    report or a prepared-state argument. -/
theorem root_prefix_no_fatal_source :
    runNoFatal 9243 rootBlank = some rootEndpoint := by
  decide

/-- Every primitive prefix, including both endpoints, exists in the
    original zipper semantics and avoids the fatal C/01 gateway. -/
theorem root_prefix_all_prefixes_nonfatal (t : Nat) (ht : t ≤ 9243) :
    ∃ p, BB429OddExcursion.run t rootBlank = some p ∧
      fatalCZero p = false :=
  runNoFatal_prefix 9243 t rootBlank rootEndpoint
    root_prefix_no_fatal_source ht

/-- Exact census of all C/0 instruction starts on the 9,243-step
    blank-root prefix. Every event has a blank immediate right neighbor. -/
theorem root_czero_event_trace :
    cZeroEventTrace 9243 0 0 rootBlank =
      [(2,2,false),(13,5,false),(64,8,false),(111,11,false),
       (275,15,false),(366,18,false),(882,22,false),(981,25,false),
       (1820,28,false),(2682,32,false),(2913,35,false),(5430,38,false),
       (8548,42,false),(8953,45,false)] := by
  decide

#print axioms root_prefix_no_fatal_source
#print axioms root_prefix_all_prefixes_nonfatal
#print axioms root_czero_event_trace

end BB429RootNoFatalPrefix
