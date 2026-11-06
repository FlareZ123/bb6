import EPositiveFirstChain

namespace BB6.Agent36PositiveFirst
open CryptidBoundary BB6.Agent36PositiveDoubleZero

set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-- The complete original E boundary is free of physically blank-left F/0
    visits until its exact source-certified return, uniformly in m,q,r and
    every untouched right suffix. -/
theorem ePositiveBoundaryNoPhysical (m q r : Nat) (ys : List Bool) :
    NoPhysical (input m q r ys) (2*m+4*q+4*r+29) := by
  let sn : Cfg :=
    scanStart (q+2) (core m)
      ([true,true,false] ++ (pairs r ++ (false::ys)))
  let sa : Cfg :=
    ⟨oppairs (q+2) ++ core m,false,
      [true,true,false] ++ (pairs r ++ (false::ys)),0⟩
  have hstart : run 2 (input m q r ys) = sn := by
    dsimp [sn]
    simp [input, scanStart, run, step, goL, goR, core, pairs]
  have hscan : run (2*(q+2)) sn = sa := by
    dsimp [sn,sa]
    rw [scan_run]
    rfl
  have h0 : NoPhysical (input m q r ys) 2 :=
    eTwoNoPhysical m q r ys
  have h1 : NoPhysical sn (2*(q+2)) :=
    scanNoPhysical (q+2) (core m)
      ([true,true,false] ++ (pairs r ++ (false::ys)))
  have h2 : NoPhysical sa (20+2*q+4*r+(2*m+3)) :=
    aPositiveFirst m q r ys
  have htail : NoPhysical sn
      (2*(q+2)+(20+2*q+4*r+(2*m+3))) :=
    join sn sa (2*(q+2)) (20+2*q+4*r+(2*m+3))
      h1 hscan h2
  have hall : NoPhysical (input m q r ys)
      (2+(2*(q+2)+(20+2*q+4*r+(2*m+3)))) :=
    join (input m q r ys) sn 2
      (2*(q+2)+(20+2*q+4*r+(2*m+3)))
      h0 hstart htail
  have htime :
      2+(2*(q+2)+(20+2*q+4*r+(2*m+3))) =
        2*m+4*q+4*r+29 := by omega
  simpa only [htime] using hall

/-- Complete quantified strict first physical return at the E boundary,
    with the exact original-machine endpoint inherited from the source. -/
theorem ePositiveBoundaryFirst (m q r : Nat) (ys : List Bool) :
    NoPhysical (input m q r ys) (2*m+4*q+4*r+29) ∧
    run (2*m+4*q+4*r+29) (input m q r ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        ([false,true,true,true] ++
        (List.replicate (2*q) true ++
          ([true,false,true,true] ++
            (List.replicate (2*r+4) true ++ ys)))),5⟩ :=
  ⟨ePositiveBoundaryNoPhysical m q r ys, ePositiveReturn m q r ys⟩

#print axioms ePositiveBoundaryNoPhysical
#print axioms ePositiveBoundaryFirst
end BB6.Agent36PositiveFirst
