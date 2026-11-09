import CZeroHeadFrontier
import CZeroContextToE1
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429CZeroContextToE1Max
open BB429OddExcursion BB429CZeroEvenReturn BB429CZeroHeadFrontier
open BB429CZeroContextToE1 BB429W4HeadMax

/-- The C/0 10-prefix entry moves two cells left overall; its initial
    D/0 step gives exactly one cell of rightward head overshoot. -/
theorem C0_to_E1_6_max (n : Nat) (tail : List Bool) :
    runWithMax 6 (z 2 (true::false::(ones n ++ tail)) false []) =
      some (z 4 (ones n ++ tail) true [true,false,true],-2,1) := by rfl

/-- Every E/1 marked sweep step travels one cell left, without overshoot. -/
theorem E1_sweep_max (n : Nat) (tail suffix : List Bool) :
    runWithMax n (z 4 (ones n ++ tail) true suffix) =
      some (z 4 tail true (ones n ++ suffix),-((n:Nat):Int),0) := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
      have hfirst : runWithMax 1 (z 4 (ones (n+1) ++ tail) true suffix) =
          some (z 4 (ones n ++ tail) true (true::suffix),-1,0) := by rfl
      have hwords : ones n ++ (true::suffix) = ones (n+1) ++ suffix := by
        simp [ones,List.replicate_succ',List.append_assoc]
      rw [show n+1=1+n by omega,runWithMax_add,
        show 1+n=n+1 by omega,hfirst]
      simp only [Option.bind_some]
      rw [ih (true::suffix),hwords]
      simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
      constructor
      · trivial
      constructor <;> simp <;> omega

/-- The 10 1^(2k+4) C/0 family exits at E/1 after 2k+10
    instructions, at displacement -(2k+6) and maximum +1. -/
theorem C0_to_E1_context_max (k : Nat) (tail : List Bool) :
    runWithMax (2*k+10) (z 2 (true::false::(ones (2*k+4) ++ tail)) false []) =
      some (z 4 tail true (ones (2*k+4) ++ [true,false,true]),
        -(((2*k+6:Nat):Int)),1) := by
  rw [show 2*k+10=6+(2*k+4) by omega,
    runWithMax_add,C0_to_E1_6_max]
  simp only [Option.bind_some]
  rw [E1_sweep_max]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  constructor <;> simp <;> omega

/-- Exact primitive-trace maximum through both C/0 records to the E/1
    boundary. Maximum +4; final displacement -(2k+3); arbitrary tape. -/
theorem even_C0_to_E1_context_max (k : Nat) (tail : List Bool) :
    runWithMax (6*k+21) (z 2 (ones (2*k+2) ++ (false::tail)) false []) =
      some (z 4 tail true (ones (2*k+4) ++ [true,false,true]),
        -(((2*k+3:Nat):Int)),4) := by
  rw [show 6*k+21=(4*k+11)+(2*k+10) by omega,
    runWithMax_add,even_C0_context_max]
  simp only [Option.bind_some]
  rw [C0_to_E1_context_max]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  constructor <;> simp <;> omega

#print axioms C0_to_E1_context_max
#print axioms even_C0_to_E1_context_max
end BB429CZeroContextToE1Max
