import Lean
set_option maxHeartbeats 0
namespace BB6.Agent9Anti5

/-- Every strictly interior slope of modulus five has four-cycle dynamics. -/
theorem slope5_orbit (b x : Nat→Int) (L : Nat)
    (hinit : 1≤b 0 ∧ b 0≤4)
    (hx : ∀ j<L, x j=0∨x j=1)
    (hs : ∀ j<L, 2*b (j+1)=b j+5*x j) :
    (∀ j≤L, 1≤b j ∧ b j≤4) ∧
    (∀ j, j+3≤L →
       b (j+2)=5-b j ∧ x (j+2)=1-x j ∧
       b j=4-x j-2*x (j+1)) := by
  have hinside : ∀ j≤L, 1≤b j ∧ b j≤4 := by
    intro j hj
    induction j with
    | zero => exact hinit
    | succ j ih =>
      have hh := ih (by omega)
      have hs' := hs j (by omega)
      have hx' := hx j (by omega)
      rcases hx' with h0|h1
      · rw [h0] at hs'; omega
      · rw [h1] at hs'; omega
  refine ⟨hinside,?_⟩
  intro j hj
  have h0 := hinside j (by omega)
  have h1 := hinside (j+1) (by omega)
  have h2 := hinside (j+2) (by omega)
  have hs0 := hs j (by omega)
  have hs1 := hs (j+1) (by omega)
  rw [show j+1+1=j+2 by omega] at hs1
  have hx0 := hx j (by omega)
  have hx1 := hx (j+1) (by omega)
  have hbflip : b (j+2)=5-b j ∧ b j=4-x j-2*x (j+1) := by
    rcases hx0 with hx00|hx01 <;> rcases hx1 with hx10|hx11 <;> omega
  have hx2 : x (j+2)=1-x j := by
    have hs2 := hs (j+2) (by omega)
    have h3b := hinside (j+3) (by omega)
    have hx' := hx (j+2) (by omega)
    rcases hx' with hx'|hx' <;> omega
  exact ⟨hbflip.1,hx2,hbflip.2⟩
end BB6.Agent9Anti5
