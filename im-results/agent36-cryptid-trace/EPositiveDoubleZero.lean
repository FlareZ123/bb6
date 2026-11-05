import EPositiveCore1
namespace BB6.Agent36PositiveDoubleZero
open CryptidBoundary
set_option maxHeartbeats 14000000
set_option maxRecDepth 8192
/-- Source E boundary with q+1 leading 10 pairs and r trailing 10 pairs. -/
def input (m q r : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::core m,false,
    pairs (q+1) ++ ([true,true,false] ++ (pairs r ++ (false::ys))),4⟩
theorem ePositiveFront (m q r : Nat) (ys : List Bool) :
    run (4*q+4*r+26) (input m q r ys) =
    sweepB m
      ([false,true,true,true] ++
        (List.replicate (2*q) true ++
          ([true,false,true,true] ++
             (List.replicate (2*r+4) true ++ ys)))) := by
  have ht : 4*q+4*r+26 = (2+2*(q+2)) + (20+2*q+4*r) := by omega
  rw [ht,run_add]
  have hh : run (2+2*(q+2)) (input m q r ys) =
      (⟨oppairs (q+2) ++ core m,false,
         [true,true,false] ++ (pairs r ++ (false::ys)),0⟩ : Cfg) := by
    rw [show 2+2*(q+2)=2+(2*(q+2)) by omega,run_add]
    change run (2*(q+2))
      (scanStart (q+2) (core m)
        ([true,true,false] ++ (pairs r ++ (false::ys)))) = _
    rw [scan_run]
    rfl
  rw [hh]
  exact aPositiveTurn m q r ys

theorem ePositiveReturn (m q r : Nat) (ys : List Bool) :
    run (2*m+4*q+4*r+29) (input m q r ys) =
    ⟨[],false,List.replicate (2*m+3) true ++
      ([false,true,true,true] ++
        (List.replicate (2*q) true ++
          ([true,false,true,true] ++
             (List.replicate (2*r+4) true ++ ys)))),5⟩ := by
  have ht : 2*m+4*q+4*r+29=(4*q+4*r+26)+(2*m+3) := by omega
  rw [ht,run_add,ePositiveFront,sweepB_run]

/-- Unbounded original-source F/0 endpoint with arbitrary right suffix. -/
theorem full_E_positive_double_zero (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+64+4*q+4*r)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs (q+1) ++ ([true,true,false] ++
          (pairs r ++ (false::ys)))))) =
    ⟨[],false,List.replicate (8*k+5) true ++
      ([false,true,true,true] ++
        (List.replicate (2*q) true ++
          ([true,false,true,true] ++
             (List.replicate (2*r+4) true ++ ys)))),5⟩ := by
  have ht : 12*k*k+49*k+64+4*q+4*r =
      (12*k*k+41*k+33)+(2*(4*k+1)+4*q+4*r+29) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k+1)+4*q+4*r+29) (input (4*k+1) q r ys) = _
  rw [ePositiveReturn]
  rw [show 2*(4*k+1)+3=8*k+5 by omega]

#print axioms ePositiveFront
#print axioms ePositiveReturn
#print axioms full_E_positive_double_zero
end BB6.Agent36PositiveDoubleZero
