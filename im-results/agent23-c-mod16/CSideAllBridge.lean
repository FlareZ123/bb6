import CSideAll
import CMod16Bridge
namespace BB6.Agent23

theorem source_side_sixteen_unreachable (n : Nat) (hn : n%16=0) :
    ¬BB6CLine.Reach (0,4*n,24*n+23) := by
  intro hr
  exact side_sixteen_unreachable n hn (reach_agree _ hr)

#print axioms source_side_sixteen_unreachable
end BB6.Agent23
