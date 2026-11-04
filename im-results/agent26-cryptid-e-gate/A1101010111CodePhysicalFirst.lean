import Lean.Elab.Tactic.Omega
import A1101010111Code
import A1101010111First
import ACodeFirstReturn

namespace BB6.Agent26ACodePhysicalFirst

open CryptidBoundary
open BB6.CryptidACodeFirstReturn
open BB6.CryptidPrefixFirstReturn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def packet (ys : List Bool) : List Bool :=
  [true,true,false,true,false,true,false,true,true,true] ++ ys

def tail (ys : List Bool) : List Bool :=
  [false,true,false,true,false,true,false,true,false] ++ ys

/-- Stronger physical first-return statement for any mixed 10/111 code
    followed by 1101010111: no intermediate state F scanning zero has
    a physically blank left tape, even if encoded as nonempty all-false. -/
theorem full_A_code_1101010111_firstPhysical (k : Nat) (ws ys : List Bool) :
    let m := 4*k+3+CryptidA.wordInc ws
    let elapsed := (12*k*k+41*k+32)+
      (CryptidA.wordCost (4*k+3) ws+(2*m+36))
    let start := init (List.replicate (3*k+1) true ++
      false :: (CryptidA.wordCode ws ++ packet ys))
    run elapsed start =
      ⟨[],false,List.replicate (2*m+5) true ++ tail ys,5⟩ ∧
    ∀ t, 0<t → t<elapsed → ¬ Physical (run t start) := by
  dsimp
  constructor
  · exact BB6.Agent26ACode.full_A_code_1101010111 k ws ys
  · intro t hpos ht hphysical
    by_cases hpre : t < 12*k*k+41*k+32
    · exact (prefixA_positive_noF k
        (CryptidA.wordCode ws ++ packet ys) t hpos hpre) hphysical.1
    · obtain ⟨u,hu⟩ : ∃ u, t=(12*k*k+41*k+32)+u :=
        ⟨t-(12*k*k+41*k+32),by omega⟩
      have hprefix : run (12*k*k+41*k+32)
          (init (List.replicate (3*k+1) true ++
             false :: (CryptidA.wordCode ws ++ packet ys))) =
          aBoundary (4*k+3) (CryptidA.wordCode ws ++ packet ys) := by
        exact prefix_A k (CryptidA.wordCode ws ++ packet ys)
      rw [hu,run_add,hprefix] at hphysical
      by_cases hword : u < CryptidA.wordCost (4*k+3) ws
      · exact (original_word_noF (4*k+3) ws (packet ys)
          u hword) hphysical.1
      · obtain ⟨v,hv⟩ :
          ∃ v, u=CryptidA.wordCost (4*k+3) ws+v :=
          ⟨u-CryptidA.wordCost (4*k+3) ws,by omega⟩
        have hcode : run (CryptidA.wordCost (4*k+3) ws)
          (aBoundary (4*k+3) (CryptidA.wordCode ws ++ packet ys)) =
          aBoundary (4*k+3+CryptidA.wordInc ws) (packet ys) :=
          BB6.Agent35.a_code_return (4*k+3) ws (packet ys)
        rw [hv,run_add,hcode] at hphysical
        have hlocal : v < 2*(4*k+3+CryptidA.wordInc ws)+36 := by omega
        exact a1101010111_first_physical
          (4*k+3+CryptidA.wordInc ws) ys v hlocal hphysical

#print axioms full_A_code_1101010111_firstPhysical

end BB6.Agent26ACodePhysicalFirst
