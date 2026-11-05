import FirstForkExactThree

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield CascadeSweep

theorem rooted_exact_three (u a b c : Nat) (hu:u≠2)
    (ha:ResetParent a u) (hb:ResetParent b u) (hc:ResetParent c u)
    (hall:∀ q, ResetParent q u ↔ q=a ∨ q=b ∨ q=c) :
    ReachC (2,0) (u,0) ↔
      ReachC (2,0) (a,0) ∨ ReachC (2,0) (b,0) ∨
      ReachC (2,0) (c,0) := by
  constructor
  · intro hroot
    have hchain:ResetChain 2 u := (root_reset_chain_iff u).mp hroot
    obtain ⟨q,hpart,hparent⟩:=reset_chain_last hchain hu
    rcases (hall q).mp hparent with h|h|h
    · left
      rw [h] at hpart
      exact (root_reset_chain_iff a).mpr hpart
    · right;left
      rw [h] at hpart
      exact (root_reset_chain_iff b).mpr hpart
    · right;right
      rw [h] at hpart
      exact (root_reset_chain_iff c).mpr hpart
  · intro hroot
    rcases hroot with h|h|h
    · have hc0:ResetChain 2 a := (root_reset_chain_iff a).mp h
      exact (root_reset_chain_iff u).mpr (hc0.append ha)
    · have hc0:ResetChain 2 b := (root_reset_chain_iff b).mp h
      exact (root_reset_chain_iff u).mpr (hc0.append hb)
    · have hc0:ResetChain 2 c := (root_reset_chain_iff c).mp h
      exact (root_reset_chain_iff u).mpr (hc0.append hc)

theorem rooted_near_top_three (n u A : Nat) (hn:5≤n)
    (hu:u≠2) (hA:3≤A) (hclose:u+A=4*2^n)
    (htight:64*A+164≤13*2^n)
    (hdiv:(2*u+5)%81=0) (hnot:(2*u+5)%2187≠0) :
    ReachC (2,0) (u,0) ↔
      ReachC (2,0) (oddPre3 n u,0) ∨
      ReachC (2,0) (oddPre n u,0) ∨
      ReachC (2,0) (evenPre n A,0) := by
  have hsize:8*A≤5*2^n:=by omega
  have hd9:(2*u+5)%9=0:=by omega
  exact rooted_exact_three u (oddPre3 n u) (oddPre n u)
    (evenPre n A) hu
    (near_top_has_tthree n u A (by omega) hclose htight hdiv)
    (odd_parent_near_top n u A (by omega) hclose hsize hd9)
    (even_parent_near_top n u A (by omega) hA hclose hsize)
    (fun q=>near_top_exact_three n u A q hn hA hclose htight hdiv hnot)

#print axioms rooted_exact_three
#print axioms rooted_near_top_three
end CascadeFirstFork
