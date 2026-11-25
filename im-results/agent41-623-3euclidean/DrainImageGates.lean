import DrainImageDecoder

namespace BB6.Agent41DrainImageDecoder

/-- Both parity-compatible image shifts are absent. -/
def blocked (y : Nat) : Prop :=
  if y%2=0 then inverse (y-2)=none ∧ inverse (y-3)=none
  else inverse (y-5)=none ∧ inverse y=none

instance (y : Nat) : Decidable (blocked y) := by
  unfold blocked
  split <;> infer_instance

/-- In every length-band gap, each triple of consecutive candidate rows
contains a row missing both parity-compatible shifted images. -/
theorem blocked_band {E : Nat → Nat} (he : ExcessLaws E)
    (k j : Nat) (hk : 2≤k) (hj : 1≤j) (hj' : j≤k+3) :
    let y := 9*tau k+2*j+(if k%2=0 then 2 else 0)
    blocked y ∨ blocked (y+2) ∨ blocked (y+4) := by
  dsimp
  have hp := tau_parity k
  have hg0 := band_gap he k j hj (by omega)
  have hg1 := band_gap he k (j+1) (by omega) (by omega)
  have hg2 := band_gap he k (j+2) (by omega) (by omega)
  have ht := tau_mono (show 2≤k by omega)
  have ht' : tau 2=4 := by decide
  rw [ht'] at ht
  by_cases h : k%2=0
  · rw [if_pos h]
    let y := 9*tau k+2*j+2
    change blocked y ∨ blocked (y+2) ∨ blocked (y+4)
    have hy : y%2=0 := by dsimp [y]; omega
    have h0 : y-2=9*tau k+2*j := by dsimp [y]; omega
    have h1 : y+2-2=9*tau k+2*(j+1) := by dsimp [y]; omega
    have h2 : y+4-2=9*tau k+2*(j+2) := by dsimp [y]; omega
    have hn := inverse_no_three he (y-3)
    have hn1 : y-3+2=y+2-3 := by dsimp [y]; omega
    have hn2 : y-3+4=y+4-3 := by dsimp [y]; omega
    rw [hn1,hn2] at hn
    have hy1 : (y+2)%2=0 := by omega
    have hy2 : (y+4)%2=0 := by omega
    unfold blocked
    simp only [if_pos hy, if_pos hy1, if_pos hy2, h0,h1,h2,hg0,hg1,hg2,true_and]
    exact hn
  · rw [if_neg h]
    let y := 9*tau k+2*j
    change blocked y ∨ blocked (y+2) ∨ blocked (y+4)
    have hy : y%2≠0 := by dsimp [y]; omega
    have hy1 : (y+2)%2≠0 := by omega
    have hy2 : (y+4)%2≠0 := by omega
    have h0 : y=9*tau k+2*j := rfl
    have h1 : y+2=9*tau k+2*(j+1) := by dsimp [y]; omega
    have h2 : y+4=9*tau k+2*(j+2) := by dsimp [y]; omega
    have hn := inverse_no_three he (y-5)
    have hn1 : y-5+2=y+2-5 := by dsimp [y]; omega
    have hn2 : y-5+4=y+4-5 := by dsimp [y]; omega
    rw [hn1,hn2] at hn
    have g0 : inverse y=none := by rw [h0]; exact hg0
    have g1 : inverse (y+2)=none := by rw [h1]; exact hg1
    have g2 : inverse (y+4)=none := by rw [h2]; exact hg2
    rcases hn with hn|hn|hn
    · exact Or.inl (by unfold blocked; rw [if_neg hy]; exact ⟨hn,g0⟩)
    · exact Or.inr (Or.inl (by unfold blocked; rw [if_neg hy1]; exact ⟨hn,g1⟩))
    · exact Or.inr (Or.inr (by unfold blocked; rw [if_neg hy2]; exact ⟨hn,g2⟩))

#print axioms blocked_band
end BB6.Agent41DrainImageDecoder
