import BB429NewResidue
import BB429RootOddRows
import Lean.Elab.Tactic.Omega

namespace Agent6Terminal16381Partial

open BB429NewResidue

/-- The q ≡ 4 (mod 8) subfamily of the inverse-kernel base cylinder
for terminal residue 16381 is excluded by the blank-root 1/5 row gate. -/
theorem no_base_q4 (q : Nat) (hq : q%8=4) :
    ¬ Reach (8*q+5) (65520*q+65480) := by
  intro hr
  have h13 : 13≤8*q+5 := by omega
  have hodd : (8*q+5)%2=1 := by omega
  rcases odd_back (8*q+5) (65520*q+65480) h13 hodd hr with hfirst|hsecond
  · rcases hfirst with ⟨x,y,hp,hx,hy⟩
    have hx' : x=4*q+1 := by omega
    subst x
    have ha : (4*q+1)%16=1 := by omega
    have hb : y%8=5 := by rw [hy]; omega
    rcases hp with ⟨n,hn⟩
    exact (Agent6RootOddRows.rooted_not_1_5 n (4*q+1) y hn ha) hb
  · rcases hsecond with ⟨x,y,hp,hx,hy,hb4⟩
    have hmod : (65520*q+65480)%4=0 := by omega
    omega

#print axioms no_base_q4

end Agent6Terminal16381Partial
