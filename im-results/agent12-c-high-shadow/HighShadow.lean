import NegativeShadow
import HighShadowArithmetic

namespace BB6.Agent12HighShadow
open BB6.Agent13AffineCone

def shadowCheck (f b x y : Nat) : Bool :=
  BB6.Agent13NegativeShadow.check f b ⟨x,y⟩

def highExcluded (f j m : Nat) : Bool :=
  highCheck shadowCheck f j m (v2Aux ((residual j m).log2+1) (residual j m))

private theorem sourceParent : ParentContract BB6.Agent3.CReach := by
  intro x y v hx hy hval hgt hr
  obtain ⟨a,k,hp,he⟩ := BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 x y hx hr
  exact ⟨a,k,hp,parent_equations a k x y v hy hval hgt
    ((BB6.Agent46.complete_section_inverse a k x y (by omega)).mp he)⟩

private theorem sourceShadow : ShadowContract BB6.Agent3.CReach shadowCheck := by
  intro f b x y sx sy h h1 h2
  apply BB6.Agent13NegativeShadow.check_sound BB6.Agent3.CReach ?_
    BB6.Agent13TwoParent.odd_forbidden_image f b x y ⟨sx,sy⟩ h ⟨h1,h2⟩
  intro a k hx hy hr
  obtain ⟨p,q,hp,he⟩ := BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5 a k hx hr
  exact ⟨p,q,hp,(BB6.Agent46.complete_section_inverse p q a k (by omega)).mp he⟩

theorem high_stop_excluded (f j m k : Nat) (h : highExcluded f j m=true)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) : ¬BB6.Agent3.CReach (2*j+3) k :=
  highCheck_sound _ _ sourceParent sourceShadow f j m _ k h hstop

example : highExcluded 20 4 25=true := by decide
example : highExcluded 20 5 49=true := by decide
example : highExcluded 20 8 5=true := by decide
example : highExcluded 20 2 16=true := by decide

#print axioms high_stop_excluded
end BB6.Agent12HighShadow
