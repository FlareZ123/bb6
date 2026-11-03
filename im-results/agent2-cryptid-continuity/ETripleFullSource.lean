import Lean.Elab.Tactic.Omega
import PrefixENoFSource
import ETripleBoundarySource

namespace BB6.CryptidETriplePairsFirstReturn
open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def IsPhysicalReturn (c : Cfg) : Prop :=
  c.st = 5 ∧ c.h = false ∧ c.l = []

/-- Every original I_(3k+4)(0(10)^q111 ys) section reaches F/0 at
    its first positive physically blank-left F/0 return at the
    exact 12k^2+49k+58+6q primitive-step endpoint. -/
theorem full_E_triple_pairs_first_return (k q : Nat) (ys : List Bool) :
    let tmax := 12*k*k+49*k+58+6*q
    let start := init (List.replicate (3*k+2) true ++
      false :: (pairs q ++ ([true,true,true] ++ ys)))
    run tmax start =
      ⟨[],false,List.replicate (8*k+9) true ++
        (oppairs (q+2) ++ false::ys),5⟩ ∧
    ∀ t, 0<t → t<tmax → ¬ IsPhysicalReturn (run t start) := by
  dsimp
  constructor
  · exact full_E_triple_pairs k q ys
  · intro t hpos hlt hphys
    by_cases hp : t<12*k*k+41*k+33
    · exact (prefixE_positive_noF k
        (pairs q ++ ([true,true,true]++ys)) t hpos hp) hphys.1
    · have hprefix :
        run (12*k*k+41*k+33)
          (init (List.replicate (3*k+2) true ++
            false :: (pairs q ++ ([true,true,true]++ys)))) =
          eTriplePairs (4*k+3) q ys := by
        rw [prefix_E]
        rfl
      have ht : t=(12*k*k+41*k+33)+(t-(12*k*k+41*k+33)) := by omega
      have hr : t-(12*k*k+41*k+33)<
          2*(4*k+3)+6*q+19 := by omega
      rw [ht,run_add] at hphys
      simp only [List.cons_append, List.nil_append] at hprefix
      rw [hprefix] at hphys
      exact (eTriplePairs_firstF (4*k+3) q ys).2
        (t-(12*k*k+41*k+33)) hr hphys.1

#print axioms full_E_triple_pairs_first_return
end BB6.CryptidETriplePairsFirstReturn
