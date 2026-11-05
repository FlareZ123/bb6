import EPositiveCore0
namespace BB6.Agent36PositiveDoubleZero
open CryptidBoundary
open BB6.Agent36EZeroPairs0
set_option maxHeartbeats 14000000
set_option maxRecDepth 8192
theorem aPositiveTurn (m q r : Nat) (ys : List Bool) :
    run (20+2*q+4*r)
      (⟨oppairs (q+2) ++ core m,false,
        [true,true,false] ++ (pairs r ++ (false::ys)),0⟩ : Cfg) =
    sweepB m
      ([false,true,true,true] ++
        (List.replicate (2*q) true ++
          ([true,false,true,true] ++
             (List.replicate (2*r+4) true ++ ys)))) := by
  have ht : 20+2*q+4*r =
      7+(2*r+(3+(2*r+(2+(4+(2*q+4)))))) := by omega
  rw [ht,run_add,aDoubleSeven]
  change run (2*r+(3+(2*r+(2+(4+(2*q+4))))))
    (⟨[false,true,true] ++ (oppairs (q+2) ++ core m),false,
       pairs r ++ (false::ys),0⟩ : Cfg) = _
  rw [run_add, aTenOppIter]
  change run (3+(2*r+(2+(4+(2*q+4)))))
    (⟨oppairs r ++ ([false,true,true] ++ (oppairs (q+2) ++ core m)),
      false,false::ys,0⟩ : Cfg) = _
  rw [run_add, a_three]
  change run (2*r+(2+(4+(2*q+4))))
    (⟨pairs r ++ ([true,true] ++ (oppairs (q+2) ++ core m)),
      false,[true,true] ++ ys,3⟩ : Cfg) = _
  rw [run_add, d_pair_run]
  change run (2+(4+(2*q+4)))
    (⟨[true,true] ++ (oppairs (q+2) ++ core m),false,
      List.replicate (2*r) true ++ ([true,true] ++ ys),3⟩ : Cfg) = _
  rw [run_add, d_two]
  change run (4+(2*q+4))
    (⟨oppairs (q+2) ++ core m,true,
       [true,true] ++ (List.replicate (2*r) true ++ ([true,true] ++ ys)),3⟩ : Cfg) = _
  rw [fourOnes]
  rw [run_add,dBridge]
  change run (2*q+4)
    (cWalk q (core m)
      ([true,false,true,true] ++ (List.replicate (2*r+4) true ++ ys))) = _
  rw [run_add,cWalk_run]
  change run 4
    (⟨core m,true,List.replicate (2*q) true ++
       ([true,false,true,true] ++ (List.replicate (2*r+4) true ++ ys)),2⟩ : Cfg) = _
  change run 4
    (⟨pairs (m+2) ++ [true,true],true,List.replicate (2*q) true ++
       ([true,false,true,true] ++ (List.replicate (2*r+4) true ++ ys)),2⟩ : Cfg) = _
  rw [cBase]
#print axioms aPositiveTurn
end BB6.Agent36PositiveDoubleZero
