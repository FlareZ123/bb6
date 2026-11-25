import PairCarryWalk
import BatchCarrySource

namespace BB6.Agent9PairCarry
open BB6.Agent9BatchCarry

theorem pair_checked_interval (L R lo hi : Nat) (hcap : R<2^L)
    (hlo : 14≤lo) (he : lo%2=0) (hF : hi+4≤2*R) (hK : 2*R+1≤2*lo+3)
    (hcheck : pairCheck L R lo hi=true) :
    ∀ n, lo≤n → n≤hi → n%2=0 → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro n hnlo hnhi hn
  apply critical_reset_no_reach_batch (2*R+1) lo n (by omega) hnlo (by omega) (by omega) hn
  intro hm
  have hcenter := ((mem_batch (2*R+1) lo n (by omega)).mp hm).2.2.2
  exact pairCheck_sound L R lo hi n hcap hnlo he hnhi (by omega) hn hcheck
    ((mem_live _ _ _).mp hcenter)

#print axioms pair_checked_interval
end BB6.Agent9PairCarry
