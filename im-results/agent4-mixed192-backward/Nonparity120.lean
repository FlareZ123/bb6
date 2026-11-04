import SideStop
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace A4Mixed192Novel

/-- The two non-parity-obvious second-stop residue sectors certified by our
two mixed192 backward cores, in a compact two-clause parameter formulation.
These avoid the previously known a≡k≡3 (mod4) obstruction. -/
theorem second_stop_nonparity_120_excluded (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hres :
      (j%24=19 ∧ m%16=j%16) ∨
      (j%24=16 ∧ (3*m+34)%192=j%192)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  apply A4Mixed192Side.second_stop_504_mod192_excluded j m k hm heq
  rcases hres with hs | hd
  · have h48 : j%48=19 ∨ j%48=43 := by omega
    rcases h48 with hj19 | hj43
    · right; right; left
      exact ⟨hj19, by omega⟩
    · right; left
      exact ⟨hj43, by omega⟩
  · have hdir :
      ((j%192=16 ∧ m%64=58) ∨
       (j%192=112 ∧ m%64=26) ∨
       (j%192=64 ∧ m%64=10) ∨
       (j%192=160 ∧ m%64=42)) ∨
      ((j%192=40 ∧ m%64=2) ∨
       (j%192=136 ∧ m%64=34) ∨
       (j%192=88 ∧ m%64=18) ∨
       (j%192=184 ∧ m%64=50)) := by omega
    right; right; right
    exact hdir

#print axioms second_stop_nonparity_120_excluded
end A4Mixed192Novel
