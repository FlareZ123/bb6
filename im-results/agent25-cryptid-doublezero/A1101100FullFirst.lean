import Lean.Elab.Tactic.Omega
import A1101100TraceNoPhysical
import PrefixNoF

namespace BB6.Agent25First
open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def start (k : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++ false::terminal1101100 ys)

/-- First physical F-on-blank-left return, in the exact original six-state D
    machine, for every unary index k and arbitrary finite suffix ys. -/
theorem full_A_1101100_first_return (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+100) (start k ys) =
      ⟨[],false,List.replicate (8*k+5) true ++ terminal1101100tail ys,5⟩ ∧
    ∀ t, 0<t → t<12*k*k+49*k+100 →
      ¬ IsPhysicalReturn (run t (start k ys)) := by
  constructor
  · exact full_A_1101100 k ys
  · intro t hpos ht hret
    by_cases hpref : t < 12*k*k+41*k+32
    · exact (prefixA_positive_noF k (terminal1101100 ys)
        t hpos hpref) hret.1
    · obtain ⟨u,hu⟩ : ∃ u, t=(12*k*k+41*k+32)+u :=
        ⟨t-(12*k*k+41*k+32),by omega⟩
      have hend : run (12*k*k+41*k+32) (start k ys) =
          aBoundary (4*k+3) (terminal1101100 ys) := by
        exact prefix_A k (terminal1101100 ys)
      have hret' : IsPhysicalReturn
          (run u (aBoundary (4*k+3) (terminal1101100 ys))) := by
        simpa only [hu, run_add, hend] using hret
      have hbound : u < 2*(4*k+3)+62 := by omega
      have hno := a1101100_first_physical_fast (4*k) ys u hbound
      apply hno
      exact ⟨hret'.1, by simp [hret'.2.2]⟩

#print axioms full_A_1101100_first_return
end BB6.Agent25First
