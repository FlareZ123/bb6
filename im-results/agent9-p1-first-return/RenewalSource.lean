import CostSource
import RenewalFourN

namespace BB6.Agent9FirstReturn
open BB6.Agent1Quarter BB6P1Unit

/-- Three certified renewal blocks exclude every right-five inverse history
    with cost at most 4n+2 for every n ≥ 8000. -/
theorem source_right_five_cost_four_n (n b m : Nat) (hn : 8000≤n)
    (h : OddCone (14*2^n-2*n-16) 3 b 5 m) : 4*n+2<m := by
  let Q := 7*2^n-n-3
  have hroot : (14*2^n-2*n-16)+10=2*Q := by
    have hdom := BB6.Agent9Renewal.large_power n hn
    dsimp [Q]; omega
  obtain ⟨v,hv,_,hg⟩ := gap_of_oddcone _ Q b 5 m hroot h
  have hv2 : v=2 := by omega
  subst v
  obtain ⟨q,hq,hret⟩ := gap_return_at_cost hg
  apply Nat.lt_of_not_ge
  intro hle
  exact BB6.Agent9Renewal.no_return_four_n n q (m+1) hn hq (by omega) (by omega) hret

#print axioms source_right_five_cost_four_n
end BB6.Agent9FirstReturn
