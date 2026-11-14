import BlankSixteenthRejoin
import SeventeenthSecondHalf
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

/-- Compose the two independently checked 1,328-section halves.  Use
    Option.bind_some explicitly: rewriting or reflexivity on the reducible
    run function can otherwise unfold the full 1,328-step evaluator. -/
theorem terminal2656_run_exact :
    DRegular.run 2656 BB6.Agent2SeventeenthArithmetic.seed17 =
      some BB6.Agent2SeventeenthArithmetic.terminal2656 := by
  have hlen : 2656 = 1328 + 1328 := rfl
  have hmid := BB6.Agent2SeventeenthArithmetic.middle17_exact
  have hmid_bind :=
    congrArg (fun o : Option DRegular.L => o.bind (DRegular.run 1328)) hmid
  calc
    DRegular.run 2656 BB6.Agent2SeventeenthArithmetic.seed17 =
        DRegular.run (1328 + 1328) BB6.Agent2SeventeenthArithmetic.seed17 :=
      congrArg (fun n => DRegular.run n BB6.Agent2SeventeenthArithmetic.seed17) hlen
    _ = (DRegular.run 1328 BB6.Agent2SeventeenthArithmetic.seed17).bind
          (DRegular.run 1328) :=
      BB6.DRegularFast.run_add 1328 1328 BB6.Agent2SeventeenthArithmetic.seed17
    _ = (some BB6.Agent2SeventeenthArithmetic.middle17).bind
          (DRegular.run 1328) := hmid_bind
    _ = DRegular.run 1328 BB6.Agent2SeventeenthArithmetic.middle17 :=
      Option.bind_some _ _
    _ = some BB6.Agent2SeventeenthArithmetic.terminal2656 :=
      BB6.Agent2SeventeenthArithmetic.terminal2656_half_exact

#print axioms terminal2656_run_exact

end BB6.Agent2SeventeenthRoot
