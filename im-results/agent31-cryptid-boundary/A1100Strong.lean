import Lean.Elab.Tactic.Omega
import A1100First
import PrefixNoF

namespace BB6.CryptidA1100Strong
open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn

set_option maxHeartbeats 8000000
set_option maxRecDepth 3000

def aStart (k : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++ false::true::true::false::false::ys)

/-- An original-source strict first physical return on the exceptional A1100 cylinder.
The remainder ys is an arbitrary binary word. -/
theorem full_A_1100_first_return (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+54) (aStart k ys) =
       ⟨[],false,List.replicate (8*k+7) true ++
          (false::List.replicate 6 true ++ ys),5⟩ ∧
    ∀ t, 0<t → t<12*k*k+49*k+54 →
       ¬ IsPhysicalReturn (run t (aStart k ys)) := by
  constructor
  · exact full_A_1100 k ys
  · intro t hpos ht hret
    by_cases hpref : t < 12*k*k+41*k+32
    · exact (prefixA_positive_noF k (true::true::false::false::ys)
        t hpos hpref) hret.1
    · obtain ⟨u,hu⟩ : ∃ u, t=(12*k*k+41*k+32)+u :=
        ⟨t-(12*k*k+41*k+32),by omega⟩
      have hend : run (12*k*k+41*k+32) (aStart k ys) =
          aBoundary (4*k+3) (true::true::false::false::ys) := by
        exact prefix_A k (true::true::false::false::ys)
      have hret' : IsPhysicalReturn
          (run u (aBoundary (4*k+3) (true::true::false::false::ys))) := by
        simpa only [hu, run_add, hend] using hret
      have hbound : u < 2*(4*k+3)+16 := by omega
      have hm : 4*k+1+2 = 4*k+3 := by omega
      have hno := a1100_first_physical (4*k+1) ys u
         (by simpa only [hm] using hbound)
      rw [hm] at hno
      apply hno
      exact ⟨hret'.1, by simp [hret'.2.2]⟩

#print axioms full_A_1100_first_return
end BB6.CryptidA1100Strong
