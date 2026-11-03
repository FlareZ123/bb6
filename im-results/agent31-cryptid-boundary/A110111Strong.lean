import Lean.Elab.Tactic.Omega
import A110111First
import PrefixNoF

namespace BB6.CryptidA110111Strong
open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn

set_option maxHeartbeats 8000000
set_option maxRecDepth 3000

def aStart (k : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++
    false::true::true::false::true::true::true::ys)

/-- Original raw-machine first physical F-on-zero return for all k and all
    finite suffixes, including those not reached by the true blank orbit. -/
theorem full_A_110111_first_return (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+62) (aStart k ys) =
       ⟨[],false,List.replicate (8*k+11) true ++
          (false::true::false::true::false::ys),5⟩ ∧
    ∀ t, 0<t → t<12*k*k+49*k+62 →
       ¬ IsPhysicalReturn (run t (aStart k ys)) := by
  constructor
  · exact full_A_110111 k ys
  · intro t hpos ht hret
    by_cases hpref : t < 12*k*k+41*k+32
    · exact (prefixA_positive_noF k (true::true::false::true::true::true::ys)
        t hpos hpref) hret.1
    · obtain ⟨u,hu⟩ : ∃ u, t=(12*k*k+41*k+32)+u :=
        ⟨t-(12*k*k+41*k+32),by omega⟩
      have hend : run (12*k*k+41*k+32) (aStart k ys) =
          aBoundary (4*k+3) (true::true::false::true::true::true::ys) := by
        exact prefix_A k (true::true::false::true::true::true::ys)
      have hret' : IsPhysicalReturn
          (run u (aBoundary (4*k+3) (true::true::false::true::true::true::ys))) := by
        simpa only [hu, run_add, hend] using hret
      have hbound : u < 2*(4*k+3)+24 := by omega
      have hm : 4*k+3 = 4*k+3 := rfl
      have hno := a110111_first_physical (4*k) ys u (by simpa only using hbound)
      apply hno
      exact ⟨hret'.1, by simp [hret'.2.2]⟩

#print axioms full_A_110111_first_return
end BB6.CryptidA110111Strong
