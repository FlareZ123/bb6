import SecondDeepSector
import ModThree
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Depth

/-- For every genuine second-family stopping input in the only
    potentially unbounded affine-normalization sector, the original
    Agent15 normalization ends with right counter at least four
    and divisible by four. The previously possible terminal 2
    cannot occur, by the stopping equation's factor of three. -/
theorem second_deep_affine_terminal_multiple_four
    (j m k : Nat)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hj : j%2=0) (hm : m%2=1) (hs : (j+m)%4=3) :
    let p := BB6.Agent15.affineNormalize (2*j+3) k
    4≤p.2 ∧ p.2%4=0 := by
  have hd := BB6.Agent15.second_halt_deep_sector j m k hgate hj hm hs
  have ha : (2*j+3)%4=3 := by omega
  have hshape :=
    BB6.Agent15.normalize_three_deep_right_0_or_2_mod4
      (2*j+3) k ha ⟨hd.1,hd.2.1⟩
  exact second_stopping_affine_residual_ge_four j m k
    (BB6.Agent15.oddDepth k)
    (BB6.Agent15.affineNormalize (2*j+3) k).2
    hgate hd.2.2.2.2 hshape

/-- Sharpen the surviving unbounded affine sector to one exact
    right-counter congruence class modulo twelve. -/
theorem second_deep_affine_terminal_four_mod_twelve
    (j m k : Nat)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hj : j%2=0) (hm : m%2=1) (hs : (j+m)%4=3) :
    (BB6.Agent15.affineNormalize (2*j+3) k).2%12=4 := by
  have hh := second_deep_affine_terminal_multiple_four
    j m k hgate hj hm hs
  have hd := BB6.Agent15.second_halt_deep_sector j m k hgate hj hm hs
  have hmod := second_stopping_affine_residual_mod_three j m k
    (BB6.Agent15.oddDepth k)
    (BB6.Agent15.affineNormalize (2*j+3) k).2
    hgate hd.2.2.2.2
  omega

#print axioms second_deep_affine_terminal_multiple_four
#print axioms second_deep_affine_terminal_four_mod_twelve
end BB6.Agent29Depth
