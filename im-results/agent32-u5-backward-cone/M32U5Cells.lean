import CSourceBridge32
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CCert

/-- The two residue families produced by the exceptional Side predecessor
    in the U5 (22,45) backward cone. -/
def u5ForbiddenCells (x y : Nat) : Prop :=
  x % 32 = 31 ∧ (y % 32 = 5 ∨ y % 32 = 21)

private theorem q_large_u5 (x z : Nat) (hz : 8 ≤ z) (hzmax : z < 32)
    (hm : x % 32 = z % 32) : q x = z := by
  have hx : 8 ≤ x := by
    by_cases hsmall : x < 8
    · have ha : x % 32 = x := Nat.mod_eq_of_lt (by omega)
      have hb : z % 32 = z := Nat.mod_eq_of_lt (by omega)
      rw [ha, hb] at hm
      omega
    · omega
  have he : q x = q z := q_congr_big x z hx hz hm
  rw [he]
  change (if z < 8 then z else 8 + (z - 8) % 32) = z
  rw [if_neg (by omega : ¬ z < 8)]
  omega

private theorem q_choices5_u5 (y : Nat) (hy : y % 32 = 5) :
    q y = 5 ∨ q y = 37 := by
  by_cases hy8 : y < 8
  · have he : y = 5 := by omega
    subst y
    left
    decide
  · right
    have he : q y = q 37 :=
      q_congr_big y 37 (by omega) (by decide) (by omega)
    rw [he]
    decide

private theorem u5_absent_31_5 : seen 31 5 0 = false := by decide
private theorem u5_absent_31_21 : seen 31 21 0 = false := by decide
private theorem u5_absent_31_37 : seen 31 37 0 = false := by decide

/-- The M32 source certificate excludes both residue families needed by
    the U5 backward cone. The low representative y=5 and its high lift
    q(y)=37 are both absent, as is y=21. -/
theorem u5_forbidden_absent (x y : Nat) (h : u5ForbiddenCells x y) :
    seen (q x) (q y) (q 0) = false := by
  rcases h with ⟨hx, hy⟩
  have hqx := q_large_u5 x 31 (by decide) (by decide) hx
  rcases hy with hy | hy
  · rcases q_choices5_u5 y hy with hqy | hqy
    · rw [hqx, hqy]
      decide
    · rw [hqx, hqy]
      decide
  · have hqy := q_large_u5 y 21 (by decide) (by decide) hy
    rw [hqx, hqy]
    decide

/-- Original-CLine blank-orbit nonreachability of the two exceptional
    U5 predecessor families, using the already kernel-checked M32 graph. -/
theorem original_u5_forbidden_unreachable (x y : Nat)
    (h : u5ForbiddenCells x y) :
    ¬ BB6CLine.Reach (x, y, 0) := by
  intro hr
  have hs := reachable_seen (source_reachable_embeds32 hr)
  rw [u5_forbidden_absent x y h] at hs
  cases hs

#print axioms original_u5_forbidden_unreachable
end CCert
