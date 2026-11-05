import FirstForkExactFour
set_option maxHeartbeats 0

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield CascadeSweep

theorem rooted_exact_four (u a b c d:Nat) (hu:u≠2)
    (ha:ResetParent a u) (hb:ResetParent b u)
    (hc:ResetParent c u) (hd:ResetParent d u)
    (hall:∀q, ResetParent q u ↔ q=a ∨ q=b ∨ q=c ∨ q=d) :
    ReachC (2,0) (u,0) ↔
      ReachC (2,0) (a,0) ∨ ReachC (2,0) (b,0) ∨
      ReachC (2,0) (c,0) ∨ ReachC (2,0) (d,0) := by
  constructor
  · intro hroot
    have hchain:ResetChain 2 u := (root_reset_chain_iff u).mp hroot
    obtain ⟨q,hpart,hparent⟩:=reset_chain_last hchain hu
    rcases (hall q).mp hparent with h|h|h|h
    · left
      rw [h] at hpart
      exact (root_reset_chain_iff a).mpr hpart
    · right;left
      rw [h] at hpart
      exact (root_reset_chain_iff b).mpr hpart
    · right;right;left
      rw [h] at hpart
      exact (root_reset_chain_iff c).mpr hpart
    · right;right;right
      rw [h] at hpart
      exact (root_reset_chain_iff d).mpr hpart
  · intro hroot
    rcases hroot with h|h|h|h
    · have hc0:ResetChain 2 a := (root_reset_chain_iff a).mp h
      exact (root_reset_chain_iff u).mpr (hc0.append ha)
    · have hc0:ResetChain 2 b := (root_reset_chain_iff b).mp h
      exact (root_reset_chain_iff u).mpr (hc0.append hb)
    · have hc0:ResetChain 2 c := (root_reset_chain_iff c).mp h
      exact (root_reset_chain_iff u).mpr (hc0.append hc)
    · have hc0:ResetChain 2 d := (root_reset_chain_iff d).mp h
      exact (root_reset_chain_iff u).mpr (hc0.append hd)

theorem rooted_near_top_four (n u A:Nat) (hn:10≤n)
    (hu:u≠2) (hA:3≤A) (hclose:u+A=4*2^n)
    (htight:64*A+164≤13*2^n)
    (hdiv:(2*u+5)%2187=0) (hnot:(2*u+5)%6561≠0) :
    ReachC (2,0) (u,0) ↔
      ReachC (2,0) (oddPre6 n u,0) ∨
      ReachC (2,0) (oddPre3 n u,0) ∨
      ReachC (2,0) (oddPre n u,0) ∨
      ReachC (2,0) (evenPre n A,0) := by
  have hsize:8*A≤5*2^n:=by omega
  have hd81:(2*u+5)%81=0:=by omega
  have hd9:(2*u+5)%9=0:=by omega
  exact rooted_exact_four u (oddPre6 n u) (oddPre3 n u)
    (oddPre n u) (evenPre n A) hu
    (near_top_has_tsix n u A hn hclose htight hdiv)
    (near_top_has_tthree n u A (by omega) hclose htight hd81)
    (odd_parent_near_top n u A (by omega) hclose hsize hd9)
    (even_parent_near_top n u A (by omega) hA hclose hsize)
    (fun q=>near_top_exact_four n u A q hn hA hclose htight hdiv hnot)

theorem rooted_fatal_four (n:Nat) (hn:10≤n)
    (hres:n%4374=491 ∨ n%4374=3208)
    (hnot:(2*fatal n+5)%6561≠0) :
    ReachC (2,0) (fatal n,0) ↔
      ReachC (2,0) (oddPre6 n (fatal n),0) ∨
      ReachC (2,0) (oddPre3 n (fatal n),0) ∨
      ReachC (2,0) (oddPre n (fatal n),0) ∨
      ReachC (2,0) (evenPre n (n+4),0) := by
  have hne:fatal n≠2:=by
    have hp:=n_plus_three_le_pow n (by omega)
    dsimp [fatal]
    omega
  exact rooted_near_top_four n (fatal n) (n+4) hn
    hne (by omega) (fatal_close n (by omega))
    (tight_fatal n hn) (fatal_div2187_special n hn hres) hnot

theorem rooted_second_four (n:Nat) (hn:10≤n)
    (hres:n%4374=83 ∨ n%4374=1906)
    (hnot:(2*secondPred n+5)%6561≠0) :
    ReachC (2,0) (fatal n,0) ↔
      ReachC (2,0) (oddPre6 n (secondPred n),0) ∨
      ReachC (2,0) (oddPre3 n (secondPred n),0) ∨
      ReachC (2,0) (oddPre n (secondPred n),0) ∨
      ReachC (2,0) (evenPre n (7*n+13),0) := by
  have h18:n%18=11 ∨ n%18=16:=by omega
  have h18all:n%18=10 ∨ n%18=11 ∨ n%18=16 ∨ n%18=17:=by
    rcases h18 with h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  have hne:secondPred n≠2:=by
    have hp:=second_size n hn
    dsimp [secondPred]
    omega
  exact (genuine_fatal_iff_second_even n hn h18all).trans
    (rooted_near_top_four n (secondPred n) (7*n+13) hn
      hne (by omega) (second_close n hn)
      (tight_second n hn) (second_div2187_special n hn hres) hnot)

#print axioms rooted_exact_four
#print axioms rooted_near_top_four
#print axioms rooted_fatal_four
#print axioms rooted_second_four
end CascadeFirstFork
