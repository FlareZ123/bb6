import CSourceBridge32
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CCert

/-- Eight computationally absent classes in the original M32 quotient.
    This entire theorem is certified only once the original 40-block
    source certificate is compiled, so do not import a development shim. -/
def eightCells (x y : Nat) : Prop :=
    (x%32=27 ∧ y%32=28) ∨ (x%32=19 ∧ y%32=16) ∨
    (x%32=3 ∧ y%32=20) ∨ (x%32=11 ∧ y%32=0) ∨
    (x%32=3 ∧ y%32=16) ∨ (x%32=11 ∧ y%32=12) ∨
    (x%32=19 ∧ y%32=4) ∨ (x%32=27 ∧ y%32=0)

private theorem q_choices (x z : Nat) (hz : z<32) (hm : x%32=z) :
    q x=z ∨ q x=z+32 := by
  by_cases hx : x<8
  · have he : x=z := by omega
    left
    subst x
    have hsmall : z<8 := by omega
    simp [q,base,modulus,hsmall]
  · by_cases hlarge : 8≤z
    · left
      have he : q x=q z := q_congr_big x z (by omega) hlarge (by omega)
      rw [he]
      change (if z<8 then z else 8+(z-8)%32)=z
      rw [if_neg (by omega : ¬ z<8)]
      omega
    · right
      have he : q x=q (z+32) :=
        q_congr_big x (z+32) (by omega) (by omega) (by omega)
      rw [he]
      change (if z+32<8 then z+32 else 8+(z+32-8)%32)=z+32
      rw [if_neg (by omega : ¬z+32<8)]
      omega

private theorem q_large (x z : Nat) (hz : 8≤z) (hzmax : z<32)
    (hm : x%32=z%32) : q x=z := by
  have hx : 8≤x := by
    by_cases hsmall : x<8
    · have ha : x%32=x := Nat.mod_eq_of_lt (by omega)
      have hb : z%32=z := Nat.mod_eq_of_lt hzmax
      rw [ha,hb] at hm
      omega
    · omega
  have he : q x=q z := q_congr_big x z hx hz hm
  rw [he]
  change (if z<8 then z else 8+(z-8)%32)=z
  rw [if_neg (by omega : ¬z<8)]
  omega

private theorem quotient_eight (x y : Nat) (h : eightCells x y) :
  ((q x=27 ∧ q y=28) ∨ (q x=19 ∧ q y=16) ∨
   ((q x=3 ∨ q x=35) ∧ q y=20) ∨
   (q x=11 ∧ (q y=0 ∨ q y=32)) ∨
   ((q x=3 ∨ q x=35) ∧ q y=16) ∨
   (q x=11 ∧ q y=12) ∨
   (q x=19 ∧ (q y=4 ∨ q y=36)) ∨
   (q x=27 ∧ (q y=0 ∨ q y=32))) := by
  unfold eightCells at h
  rcases h with h | h | h | h | h | h | h | h
  all_goals obtain ⟨hx,hy⟩ := h
  · have hqx := q_large x 27 (by decide) (by decide) (by omega)
    have hqy := q_large y 28 (by decide) (by decide) (by omega)
    omega
  · have hqx := q_large x 19 (by decide) (by decide) (by omega)
    have hqy := q_large y 16 (by decide) (by decide) (by omega)
    omega
  · have hqx := q_choices x 3 (by decide) hx
    have hqy := q_large y 20 (by decide) (by decide) (by omega)
    rcases hqx with hqx|hqx <;> omega
  · have hqx := q_large x 11 (by decide) (by decide) (by omega)
    have hqy := q_choices y 0 (by decide) hy
    rcases hqy with hqy|hqy <;> omega
  · have hqx := q_choices x 3 (by decide) hx
    have hqy := q_large y 16 (by decide) (by decide) (by omega)
    rcases hqx with hqx|hqx <;> omega
  · have hqx := q_large x 11 (by decide) (by decide) (by omega)
    have hqy := q_large y 12 (by decide) (by decide) (by omega)
    omega
  · have hqx := q_large x 19 (by decide) (by decide) (by omega)
    have hqy := q_choices y 4 (by decide) hy
    rcases hqy with hqy|hqy <;> omega
  · have hqx := q_large x 27 (by decide) (by decide) (by omega)
    have hqy := q_choices y 0 (by decide) hy
    rcases hqy with hqy|hqy <;> omega

private theorem eight_absent (x y : Nat) (h : eightCells x y) :
    seen (q x) (q y) (q 0) = false := by
  have hv := quotient_eight x y h
  rcases hv with h | h | h | h | h | h | h | h
  · rcases h with ⟨hx,hy⟩
    rw [hx,hy]
    decide
  · rcases h with ⟨hx,hy⟩
    rw [hx,hy]
    decide
  · rcases h with ⟨hx,hy⟩
    rcases hx with hx|hx
    all_goals rw [hx,hy] <;> decide
  · rcases h with ⟨hx,hy⟩
    rcases hy with hy|hy
    all_goals rw [hx,hy] <;> decide
  · rcases h with ⟨hx,hy⟩
    rcases hx with hx|hx
    all_goals rw [hx,hy] <;> decide
  · rcases h with ⟨hx,hy⟩
    rw [hx,hy]
    decide
  · rcases h with ⟨hx,hy⟩
    rcases hy with hy|hy
    all_goals rw [hx,hy] <;> decide
  · rcases h with ⟨hx,hy⟩
    rcases hy with hy|hy
    all_goals rw [hx,hy] <;> decide

/-- Universal original-accelerator nonreachability of eight independent
    32-adic counter cylinders for every blank-orbit time. This uses
    the original 40-block kernel-checked M32 quotient certificate. -/
theorem original_eight_unreachable (x y : Nat) (h : eightCells x y) :
    ¬ BB6CLine.Reach (x,y,0) := by
  intro hr
  have hs := reachable_seen (source_reachable_embeds32 hr)
  have he := eight_absent x y h
  rw [he] at hs
  cases hs

#print axioms original_eight_unreachable
end CCert
