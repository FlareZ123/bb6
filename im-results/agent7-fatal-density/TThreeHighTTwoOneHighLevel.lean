import TThreeHighTTwoOne
import HighLevel746Drain
set_option maxHeartbeats 0

namespace CascadeHighTTwo
open CascadeResetInverse

theorem reset_parent_highlevel_path {x u:Nat} (h:ResetParent x u) :
    Agent7HighLevel746.Steps (.C x 0) (.C u 0) := by
  rcases h with ⟨l,hband,heq⟩ | ⟨l,t,z,hz,hband,hnum,heq⟩
  · rcases hband with ⟨hlo,hhi⟩
    have hxlower : 4*2^l≤x+l+3 := by omega
    have hpath := Agent7HighLevel746.drain_path x l hxlower
    have hlow := Agent7HighLevel746.low_even_after_drain x l u hlo hhi heq
    exact Agent7HighLevel746.Steps.trans hpath
      (Agent7HighLevel746.Steps.step hlow (Agent7HighLevel746.Steps.refl _))
  · rcases hband with ⟨hlo,hhi⟩
    have hxlower : 4*2^l≤x+l+3 := by omega
    have hpath := Agent7HighLevel746.drain_path x l hxlower
    have hlow := Agent7HighLevel746.low_odd_after_drain x l (2^t*z) hlo hhi heq
    have htail := Agent7HighLevel746.odd_parent_underflow_path u l t z hz hlo hnum
    exact Agent7HighLevel746.Steps.trans hpath
      (Agent7HighLevel746.Steps.step hlow htail)

theorem reset_chain_highlevel_path {u:Nat} (h:ResetChain 2 u) :
    Agent7HighLevel746.Steps (.C 2 0) (.C u 0) := by
  induction h with
  | root => exact Agent7HighLevel746.Steps.refl _
  | append hchain hparent ih =>
      exact Agent7HighLevel746.Steps.trans ih (reset_parent_highlevel_path hparent)

theorem reachC_highlevel_path {u:Nat}
    (h:CascadeSweep.ReachC (2,0) (u,0)) :
    Agent7HighLevel746.Steps (.C 2 0) (.C u 0) := by
  have hr : ResetChain 2 u := (root_reset_chain_iff u).mp h
  exact reset_chain_highlevel_path hr

theorem gap_odd_parent_full_highlevel_path (g:Nat) (h:GapOddParent g) :
    Agent7HighLevel746.Steps (.C 0 2) (.C g 0) := by
  rcases h with ⟨x,l,t,z,hx,hz,hlo,hup,hnum,heq⟩
  have hroot := reachC_highlevel_path hx
  have hparent : ResetParent x g :=
    ResetParent.odd l t z hz ⟨hlo,hup⟩ hnum heq
  have hstep : Agent7HighLevel746.next (.C 0 2)=some (.C 2 0) := by
    simp [Agent7HighLevel746.next]
  exact Agent7HighLevel746.Steps.trans
    (Agent7HighLevel746.Steps.step hstep hroot)
    (reset_parent_highlevel_path hparent)

#print axioms reset_parent_highlevel_path
#print axioms gap_odd_parent_full_highlevel_path
end CascadeHighTTwo
