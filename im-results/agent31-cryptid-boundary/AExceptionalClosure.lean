import Lean.Elab.Tactic.Omega
import A110111First
import ACodeFirstReturn

namespace BB6.CryptidAGenericClosure
open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn
open BB6.CryptidACodeFirstReturn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/--
Generic certificate transport: any all-m>=3 suffix cylinder with exact
terminal endpoint and no intermediate physical return automatically extends
to all arbitrary finite 10/111 A-code prefixes and all authentic F/0 entries.
This theorem is conditional on explicitly supplied source-machine lemmas.
-/
theorem lift_first_return
    (packet : List Bool → List Bool)
    (tail : List Bool → List Bool)
    (cost outlen : Nat → Nat)
    (hend : ∀ (m : Nat) (ys : List Bool), 3 ≤ m →
      run (cost m) (CryptidBoundary.aBoundary m (packet ys)) =
        ⟨[], false, List.replicate (outlen m) true ++ tail ys, 5⟩)
    (hnoreturn : ∀ (m : Nat) (ys : List Bool) (t : Nat),
      3 ≤ m → t < cost m →
      ¬ Physical (run t (CryptidBoundary.aBoundary m (packet ys))))
    (k : Nat) (ws ys : List Bool) :
    let m := 4*k+3+CryptidA.wordInc ws
    let elapsed := (12*k*k+41*k+32)+
      (CryptidA.wordCost (4*k+3) ws + cost m)
    let start := init (List.replicate (3*k+1) true ++
      false::(CryptidA.wordCode ws ++ packet ys))
    run elapsed start =
      ⟨[], false, List.replicate (outlen m) true ++ tail ys, 5⟩ ∧
    ∀ t, 0<t → t<elapsed → ¬IsPhysicalReturn (run t start) := by
  dsimp
  have hm : 3 ≤ 4*k+3+CryptidA.wordInc ws := by omega
  have hcode : run (CryptidA.wordCost (4*k+3) ws)
      (CryptidBoundary.aBoundary (4*k+3)
        (CryptidA.wordCode ws ++ packet ys)) =
      CryptidBoundary.aBoundary (4*k+3+CryptidA.wordInc ws)
        (packet ys) :=
    BB6.Agent35.a_code_return (4*k+3) ws (packet ys)
  have hprefix : run (12*k*k+41*k+32)
      (init (List.replicate (3*k+1) true ++
        false::(CryptidA.wordCode ws ++ packet ys))) =
      CryptidBoundary.aBoundary (4*k+3)
         (CryptidA.wordCode ws ++ packet ys) :=
    prefix_A k (CryptidA.wordCode ws ++ packet ys)
  constructor
  · rw [run_add,hprefix,run_add,hcode]
    exact hend _ ys hm
  · intro t hpos ht hphysical
    by_cases hbefore : t < 12*k*k+41*k+32
    · exact (prefixA_positive_noF k
        (CryptidA.wordCode ws ++ packet ys) t hpos hbefore)
        hphysical.1
    · obtain ⟨u,hu⟩ :
        ∃ u, t=(12*k*k+41*k+32)+u :=
          ⟨t-(12*k*k+41*k+32),by omega⟩
      rw [hu,run_add,hprefix] at hphysical
      by_cases hbeforeCode : u < CryptidA.wordCost (4*k+3) ws
      · exact (original_word_noF (4*k+3) ws (packet ys)
          u hbeforeCode) hphysical.1
      · obtain ⟨v,hv⟩ :
          ∃ v, u=CryptidA.wordCost (4*k+3) ws+v :=
          ⟨u-CryptidA.wordCost (4*k+3) ws,by omega⟩
        rw [hv,run_add,hcode] at hphysical
        have hbeforeEnd : v < cost (4*k+3+CryptidA.wordInc ws) := by omega
        apply hnoreturn _ ys v hm hbeforeEnd
        exact ⟨hphysical.1, by simp [hphysical.2.2]⟩

#print axioms lift_first_return
end BB6.CryptidAGenericClosure
