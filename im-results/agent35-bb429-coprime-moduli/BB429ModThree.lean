import BB429Rank
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 20000000
set_option maxRecDepth 2048

namespace BB429Three
open BB429

/-- Concrete finite halting prefixes for nine different synthetic residues. -/
theorem witness00 : run 58 (0,60) = some (93,185) := by decide
theorem witness01 : run 63 (0,34) = some (93,185) := by decide
theorem witness02 : run 1 (0,8) = some (3,5) := by decide
theorem witness10 : run 61 (1,42) = some (93,185) := by decide
theorem witness11 : run 0 (1,1) = some (1,1) := by decide
theorem witness12 : run 1 (1,14) = some (5,9) := by decide
theorem witness20 : run 0 (2,3) = some (2,3) := by decide
theorem witness21 : run 61 (2,40) = some (93,185) := by decide
theorem witness22 : run 1 (2,20) = some (7,13) := by decide

theorem no_move93 : next (93,185) = none := by decide
theorem no_move3 : next (3,5) = none := by decide
theorem no_move1 : next (1,1) = none := by decide
theorem no_move5 : next (5,9) = none := by decide
theorem no_move2 : next (2,3) = none := by decide
theorem no_move7 : next (7,13) = none := by decide

/-- Every counter-residue pair modulo three has a concrete synthetic halting
    input for the unchanged complete #429 accelerated map. -/
theorem every_mod3_class_has_halting_start (u w : Nat) :
    ∃ U W n a b, U%3=u%3 ∧ W%3=w%3 ∧
      run n (U,W) = some (a,b) ∧ next (a,b) = none := by
  have hu : u%3=0 ∨ u%3=1 ∨ u%3=2 := by omega
  have hw : w%3=0 ∨ w%3=1 ∨ w%3=2 := by omega
  rcases hu with h0|h1|h2
  · rcases hw with h00|h01|h02
    · exact ⟨0,60,58,93,185,by omega,by omega,witness00,no_move93⟩
    · exact ⟨0,34,63,93,185,by omega,by omega,witness01,no_move93⟩
    · exact ⟨0,8,1,3,5,by omega,by omega,witness02,no_move3⟩
  · rcases hw with h10|h11|h12
    · exact ⟨1,42,61,93,185,by omega,by omega,witness10,no_move93⟩
    · exact ⟨1,1,0,1,1,by omega,by omega,witness11,no_move1⟩
    · exact ⟨1,14,1,5,9,by omega,by omega,witness12,no_move5⟩
  · rcases hw with h20|h21|h22
    · exact ⟨2,3,0,2,3,by omega,by omega,witness20,no_move2⟩
    · exact ⟨2,40,61,93,185,by omega,by omega,witness21,no_move93⟩
    · exact ⟨2,20,1,7,13,by omega,by omega,witness22,no_move7⟩

/-- A nonempty forward-closed property of the complete #429 map that is
    saturated by both residues modulo three necessarily includes a halt. -/
theorem no_nonempty_mod3_haltfree_invariant
    (u w : Nat) (P : Nat × Nat → Prop)
    (hmod : ∀ x y, x.1%3=y.1%3 → x.2%3=y.2%3 → P x → P y)
    (hinit : P (u,w))
    (hstep : ∀ x y, P x → next x = some y → P y)
    (hhalt : ∀ x, P x → next x ≠ none) : False := by
  obtain ⟨U,W,n,a,b,hu,hw,hr,hn⟩ := every_mod3_class_has_halting_start u w
  have hseed : P (U,W) := hmod (u,w) (U,W) hu.symm hw.symm hinit
  have hrun : ∀ (m : Nat) (s t : Nat × Nat), P s →
      run m s = some t → P t := by
    intro m
    induction m with
    | zero =>
        intro s t hs ht
        simp [run] at ht
        simpa [ht] using hs
    | succ m ih =>
        intro s t hs ht
        simp only [run] at ht
        cases hp : run m s with
        | none => simp [hp] at ht
        | some p =>
            simp only [hp, Option.bind_some] at ht
            exact hstep p t (ih s p hs hp) ht
  exact hhalt (a,b) (hrun n (U,W) (a,b) hseed hr) hn

#print axioms every_mod3_class_has_halting_start
#print axioms no_nonempty_mod3_haltfree_invariant
#print axioms witness00
#print axioms witness01
#print axioms witness10

end BB429Three
