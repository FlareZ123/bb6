import DoubleOnePairs
import ReturnShift
import CodeHaltFirst
import Lean.Elab.Tactic.Omega

namespace BB6.CryptidBridge

open CryptidBoundary
open BB6.CrossModelBridge
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidACodeFirstReturn

/-- The mixed-token 110(10)^q0 return is the first physical F/0 event,
    not merely an eventual return. This lifts the exact return theorem to
    a strict first-event statement for arbitrary interleaved A-token words
    and arbitrary trailing suffixes. -/
theorem complete_A_word_two_one_pairs_first_event
    (k q : Nat) (ws ys : List Bool) :
    PhysicalPair (run (pairTime k ws q) (pairInput k ws q ys)) ∧
    ∀ t, 0 < t → t < pairTime k ws q →
      ¬ PhysicalPair (run t (pairInput k ws q ys)) := by
  constructor
  · rw [pair_source]
    simp [PhysicalPair]
  · intro t hpos ht
    let P := 12*k*k+41*k+32
    let C := CryptidA.wordCost (4*k+3) ws
    let u := 4*k+1+CryptidA.wordInc ws
    let rest := [true,true,false] ++ (pairs q ++ (false::ys))
    have hprefix :
        run P (pairInput k ws q ys) =
          preA (4*k+3) (CryptidA.wordCode ws ++ rest) := by
      dsimp [pairInput,P,rest]
      rw [CryptidBoundary.prefix_A]
    have hcode :
        run C (preA (4*k+3) (CryptidA.wordCode ws ++ rest)) =
          preA (u+2) rest := by
      rw [preA_embed_ab]
      have hi :
          run C (embed (CryptidA.ab (4*k+3)
            (CryptidA.wordCode ws ++ rest))) =
          embed (CryptidA.ab ((4*k+3)+CryptidA.wordInc ws) rest) := by
        apply transfer_nonF
        · simp [CryptidA.ab]
        · exact CryptidA.consume_code (4*k+3) ws rest
        · simp [CryptidA.ab]
      rw [hi]
      have hu : (4*k+3)+CryptidA.wordInc ws = u+2 := by
        dsimp [u]
        omega
      rw [hu]
    intro hp
    by_cases hbefore : t < P
    · have hno := prefixA_positive_noF k
        (CryptidA.wordCode ws ++ rest) t hpos hbefore
      exact hno hp.1
    · obtain ⟨v,hv⟩ : ∃ v, t=P+v := ⟨t-P, by omega⟩
      rw [hv, CryptidBoundary.run_add, hprefix] at hp
      by_cases hword : v < C
      · have hno := original_word_noF (4*k+3) ws rest v hword
        exact hno hp.1
      · obtain ⟨w,hw⟩ : ∃ w, v=C+w := ⟨v-C, by omega⟩
        rw [hw, CryptidBoundary.run_add, hcode] at hp
        have htail : w < 2*(u+2)+16+4*q := by
          dsimp [pairTime,P,C,u] at ht
          omega
        exact (two_one_pairs_first_physical u q ys w htail) hp

#print axioms complete_A_word_two_one_pairs_first_event

end BB6.CryptidBridge
