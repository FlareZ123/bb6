import ChampionRootBridge
import S1Encoder
import M1EvenResidueTwoFiniteBridge
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent8M1EvenResidueTwoBaseInputCheck

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8M1EvenResidueTwo

/-- Smallest nontrivial source instance: L=3, n=2, m=1, a=1, b=0. -/
def baseInput : Config := s1Config 3 2 1 1 0 0 0

/-- The 12-step counted left sweep lands at the exact finite-bridge start
window on all sixteen cells from -11 through 4. -/
def baseSweepMatches : Bool :=
  match run tm2 12 baseInput with
  | none => false
  | some c =>
      decide (c.state = 3 ∧ c.head = -4) &&
      (List.range 16).all (fun k =>
        let y : Int := (k : Int) - 11
        c.tape (c.head+y) =
          decide (y ∈ m1EvenResidueTwoBridgeStart.marked))

theorem base_source_sweep_matches : baseSweepMatches = true := by
  decide

#print axioms base_source_sweep_matches

end BB6Coverage.Agent8M1EvenResidueTwoBaseInputCheck
