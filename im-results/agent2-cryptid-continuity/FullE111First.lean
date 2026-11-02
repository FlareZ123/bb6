import Lean.Elab.Tactic.Omega
import PrefixNoF

namespace BB6.CryptidFullE111First
open CryptidBoundary
open BB6.Agent2EOneTriple
open BB6.CryptidE111FirstReturn
open BB6.CryptidPrefixFirstReturn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def eTail : List Bool :=
  [true,false,true,true,false,true,true,false,false,true,true,true]

def fStart (k : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+2) true ++ false :: (eTail ++ ys))

def fEnd (k : Nat) (ys : List Bool) : Cfg :=
  ⟨[],false,List.replicate (8*k+3) true ++ (packet ++ ys),5⟩

/-- The full source F-to-F E111 cylinder has an exact *first positive*
    physically blank-left F-on-zero return. Internal F visits with written
    cells to the left of the head are excluded as false return markers. -/
theorem full_E_one_triple_first_return (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+170) (fStart k ys) = fEnd k ys ∧
    ∀ t, 0<t → t<12*k*k+49*k+170 →
      ¬IsPhysicalReturn (run t (fStart k ys)) := by
  constructor
  · simpa [fStart,fEnd,eTail] using full_E_one_triple_return k ys
  · intro t hpos ht hphys
    by_cases hpref : t<12*k*k+41*k+33
    · exact (prefixE_positive_noF k (eTail++ys) t hpos hpref) hphys.1
    · have hend : run (12*k*k+41*k+33) (fStart k ys) = e0 (4*k) ys := by
        change run (12*k*k+41*k+33)
          (init (List.replicate (3*k+2) true ++ false :: (eTail++ys))) =
          e0 (4*k) ys
        rw [prefix_E]
        rfl
      have htstep : t=(12*k*k+41*k+33)+(t-(12*k*k+41*k+33)) := by omega
      have hrest : t-(12*k*k+41*k+33) < 2*(4*k)+137 := by omega
      rw [htstep,run_add,hend] at hphys
      exact (e111_boundary_first_return (4*k) ys).2
        (t-(12*k*k+41*k+33)) hrest hphys

#print axioms full_E_one_triple_first_return
end BB6.CryptidFullE111First
