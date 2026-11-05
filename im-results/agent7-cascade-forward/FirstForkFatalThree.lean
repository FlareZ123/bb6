import FirstForkRootThree

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield CascadeSweep

theorem rooted_fatal_three (n:Nat) (hn:10≤n)
    (hres:n%162=5 ∨ n%162=130)
    (hnot:(2*fatal n+5)%2187≠0) :
    ReachC (2,0) (fatal n,0) ↔
      ReachC (2,0) (oddPre3 n (fatal n),0) ∨
      ReachC (2,0) (oddPre n (fatal n),0) ∨
      ReachC (2,0) (evenPre n (n+4),0) := by
  have hnon:fatal n≠2:=by
    have hp:=n_plus_three_le_pow n (by omega)
    dsimp [fatal]
    omega
  exact rooted_near_top_three n (fatal n) (n+4) (by omega)
    hnon (by omega) (fatal_close n (by omega))
    (tight_fatal n hn) (fatal_div81_bad n hn hres) hnot

theorem rooted_second_fatal_three (n:Nat) (hn:10≤n)
    (hres:n%162=83 ∨ n%162=124)
    (hnot:(2*secondPred n+5)%2187≠0) :
    ReachC (2,0) (fatal n,0) ↔
      ReachC (2,0) (oddPre3 n (secondPred n),0) ∨
      ReachC (2,0) (oddPre n (secondPred n),0) ∨
      ReachC (2,0) (evenPre n (7*n+13),0) := by
  have h18:n%18=11 ∨ n%18=16:=by omega
  have h18all:n%18=10 ∨ n%18=11 ∨ n%18=16 ∨ n%18=17:=by
    rcases h18 with h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  have hnon:secondPred n≠2:=by
    have hp:=second_size n hn
    dsimp [secondPred]
    omega
  exact (genuine_fatal_iff_second_even n hn h18all).trans
    (rooted_near_top_three n (secondPred n) (7*n+13)
      (by omega) hnon (by omega) (second_close n hn)
      (tight_second n hn) (second_div81_bad n hn hres) hnot)

#print axioms rooted_fatal_three
#print axioms rooted_second_fatal_three
end CascadeFirstFork
