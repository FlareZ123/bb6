import First80Source
import First80Arithmetic
set_option maxHeartbeats 0
namespace A4First80

theorem source_first_m39_unreachable (m k:Nat)
    (hm:m%80=39) (eqn:k+3*m+4=2*4^(m+1)) :
    ¬BB6CLine.Reach (1,k,0) := by
  exact source_no_first80 k (first_m39_mod80 m k hm eqn)

theorem source_first_iff_residue_excluded (m k:Nat) (hm:2≤m)
    (eqn:k+3*m+4=2*4^(m+1)) :
    (k%80=71 ↔ m%80=39) ∧
    (m%80=39 → ¬BB6CLine.Reach (1,k,0)) := by
  exact ⟨first_m80_iff m k hm eqn,fun h => source_first_m39_unreachable m k h eqn⟩

#print axioms source_first_m39_unreachable
#print axioms source_first_iff_residue_excluded
end A4First80
