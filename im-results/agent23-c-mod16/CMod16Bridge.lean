import CM16
import CLine
namespace BB6.Agent23

theorem next_agree (s : Nat × Nat × Nat) : nextC s = BB6CLine.nextC s := by
  rfl

theorem reach_agree (s : Nat × Nat × Nat)
    (h : BB6CLine.Reach s) : Reach s := by
  induction h with
  | init => exact Reach.init
  | next p q hp hn ih =>
      exact Reach.next p q ih ((next_agree p).symm ▸ hn)

theorem source_reset_three_mod_sixteen_unreachable (t : Nat) :
    ¬BB6CLine.Reach (32*t+7,48*t+13,0) := by
  intro hr
  exact reset_three_mod_sixteen_unreachable t (reach_agree _ hr)

#print axioms BB6.Agent23.next_agree
#print axioms BB6.Agent23.source_reset_three_mod_sixteen_unreachable
end BB6.Agent23
