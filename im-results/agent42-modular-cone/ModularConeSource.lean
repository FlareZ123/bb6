import ModularCone
import UnifiedShadow

namespace BB6.Agent42ModularCone

/-- The source interface is exactly Agent 13's all-depth inverse theorem,
    with the section-root predecessor fact that also applies at x=1. -/
theorem source_parent : ParentLaw BB6.Agent3.CReach := by
  intro x y v hr hy hv hgt
  obtain ⟨a,k,hreach,hpre⟩ := BB6.Agent13UnifiedShadow.source_parent_of_right_ge8 x y hy hr
  exact ⟨a,k,hreach,BB6.Agent13AffineCone.parent_equations a k x y v hy hv hgt hpre⟩

theorem source_forbidden : ForbiddenLaw BB6.Agent3.CReach :=
  BB6.Agent13TwoParent.odd_forbidden_image

theorem source_excluded (b : Nat) (s : Pair) (hc : excluded b s=true)
    (x y : Nat) (hl : Large b y) (hm : Matches b x y s) : ¬BB6.Agent3.CReach x y :=
  excluded_sound BB6.Agent3.CReach source_parent source_forbidden b s hc x y hl hm

theorem source_stop_cylinder_excluded (b j0 m0 j m y : Nat)
    (hb : b≤2*m+1 ∨ (2≤j ∧ b≤2*m+2))
    (hj : Cong b (j:Int) j0) (hm : Cong b (m:Int) m0)
    (he : y+j+3*m+4=P (2*m+2)*(j+2))
    (hc : excluded b (stopResidue j0 m0)=true) : ¬BB6.Agent3.CReach (2*j+1) y :=
  stop_cylinder_excluded BB6.Agent3.CReach source_parent source_forbidden b j0 m0 j m y hb hj hm he hc

#print axioms source_excluded
#print axioms source_stop_cylinder_excluded
end BB6.Agent42ModularCone
