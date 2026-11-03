import Lean.Elab.Tactic.Omega
import A110110TenFirst
import PrefixNoF

namespace BB6.Agent25TenFirst
open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def start (k q : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++
    false::true::true::false::true::true::false::(pairs q ++ false::ys))

/-- Exact first positive physical F-on-zero return for every k, q and
    every arbitrary suffix in the source-original six-state machine. -/
theorem full_A_110110_ten_first_return (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+100+4*q) (start k q ys) =
      ⟨[],false,List.replicate (8*k+5) true ++
        terminal1101100tail (List.replicate (2*q) true ++ ys),5⟩ ∧
    ∀ t, 0<t → t<12*k*k+49*k+100+4*q →
      ¬ IsPhysicalReturn (run t (start k q ys)) := by
  constructor
  · exact full_A_110110_ten k q ys
  · intro t hpos ht hret
    by_cases hpref : t < 12*k*k+41*k+32
    · exact (prefixA_positive_noF k
        (true::true::false::true::true::false::(pairs q ++ false::ys))
        t hpos hpref) hret.1
    · obtain ⟨u,hu⟩ : ∃ u, t=(12*k*k+41*k+32)+u :=
        ⟨t-(12*k*k+41*k+32),by omega⟩
      have hend : run (12*k*k+41*k+32) (start k q ys) =
          tenInput (4*k) q ys := by
        exact prefix_A k
          (true::true::false::true::true::false::(pairs q ++ false::ys))
      have hret' : IsPhysicalReturn
          (run u (tenInput (4*k) q ys)) := by
        simpa only [hu, run_add, hend] using hret
      have hbound : u < 2*(4*k+3)+62+4*q := by omega
      have hno := ten_first_physical (4*k) q ys u hbound
      apply hno
      exact ⟨hret'.1, by simp [hret'.2.2]⟩

#print axioms full_A_110110_ten_first_return
end BB6.Agent25TenFirst
