import OddResetBarrier
import BB429NewResidue
import BB429RootEven8

namespace BB429Q0Macro

def oddResetSource : Source BB429NewResidue.Reach where
  odd_back := BB429NewResidue.odd_back
  even_back := BB429NewResidue.even_back
  even8 := by
    intro a b ha he hr
    obtain ⟨n,hn⟩ := hr
    exact BB429RootEven8.rooted_positive_even_eight n a b hn ha he

/-- No genuine blank-root odd-reset candidate with a burst shorter than
    2,800,039; independent of the large rank-barrier certificates. -/
theorem rooted_odd_reset_small (n a b : Nat)
    (hn : 18≤n) (hnmax : n<2800039) (ho : a%2=1) (hb : b+3=2*a)
    (heq : 4*a+3*n+15=3*2^(n+2)) : ¬ BB429NewResidue.Reach a b := by
  intro hr
  rcases odd_reset_forces_path oddResetSource n a b hn ho hb heq hr with
    ⟨t,ht,hp⟩ | ⟨t,ht,hp⟩
  · exact rayFF_small t (by omega) hp
  · exact rayFE_small t (by omega) hp

theorem rooted_odd_reset_bounded (K n a b : Nat)
    (hK : 5≤K) (hn : 18≤n) (ho : a%2=1) (hb : b+3=2*a)
    (heq : 4*a+3*n+15=3*2^(n+2))
    (hhi : 3*n+27+24*K≤164*16^K)
    (hbar : ∀ k c, 5≤k → k≤K → c∈barrierCoeffs → RankBarrierValid c k) :
    ¬ BB429NewResidue.Reach a b :=
  odd_reset_bounded oddResetSource K n a b hK hn ho hb heq hhi hbar

#print axioms rooted_odd_reset_small
#print axioms rooted_odd_reset_bounded
end BB429Q0Macro
