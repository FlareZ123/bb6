import SourceBridge
import BitDefs
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace CQuotient192

private theorem encoded_bounded (s : Q) :
    (encode s).1 < 5 ∧ (encode s).2.1 < 192 ∧ (encode s).2.2 < 192 := by
  unfold encode
  split <;> simp <;> omega

private theorem cover_successor {q r : Q}
    (hcl : closedAt q.1 q.2.1 q.2.2 = true)
    (hq : cover q = true) (hr : r ∈ succs q) : cover r = true := by
  dsimp [closedAt] at hcl
  simp [hq] at hcl
  exact hcl _ _ _ hr

theorem reach_good_if_closed
  (hc : ∀ p : Fin 5, ∀ x y : Fin 192,
    closedAt p.val x.val y.val = true)
  (s : Q) (h : BB6CLine.Reach s) : cover (encode s) = true := by
  induction h with
  | init => decide
  | next s t hr he ih =>
    obtain ⟨hp,hx,hy⟩ := encoded_bounded s
    have hcl := hc ⟨(encode s).1,hp⟩
      ⟨(encode s).2.1,hx⟩ ⟨(encode s).2.2,hy⟩
    exact cover_successor hcl ih (source_step_sound s t he)

theorem no_142_if_closed
  (hc : ∀ p : Fin 5, ∀ x y : Fin 192,
    closedAt p.val x.val y.val = true)
  (k : Nat) (hk : k % 192 = 142) :
    ¬ BB6CLine.Reach (1,k,0) := by
  intro hr
  have hg := reach_good_if_closed hc (1,k,0) hr
  have he : encode (1,k,0) = (0,1,142) := by simp [encode, hk]
  rw [he] at hg
  have bad : cover (0,1,142) = false := by decide
  rw [bad] at hg
  cases hg

#print axioms reach_good_if_closed
#print axioms no_142_if_closed
end CQuotient192
