import RenewalUnboundedSource
import RenewalPrefix

namespace BB6.Agent9FirstReturn
open BB6.Agent1Quarter BB6P1Unit

/-- Three complete renewal blocks plus the fourth block's early shadow. -/
theorem source_right_five_cost_four_prefix (n b m : Nat) (hn : 8000≤n)
    (h : OddCone (14*2^n-2*n-16) 3 b 5 m) :
    4*n+2+BB6.Agent9Renewal.fourthPrefix n<m := by
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
  exact BB6.Agent9Renewal.no_return_four_prefix n q (m+1) hn hq (by omega) (by omega) hret

/-- At the first unresolved even index, the inverse cost is at least 42416. -/
theorem source_right_five_n10002_cost (b m : Nat)
    (h : OddCone (14*2^10002-2*10002-16) 3 b 5 m) : 42416≤m := by
  have hh := source_right_five_cost_four_prefix 10002 b m (by decide) h
  have he : BB6.Agent9Renewal.fourthPrefix 10002=2405 := by decide
  rw [he] at hh
  omega

#print axioms source_right_five_cost_four_prefix
#print axioms source_right_five_n10002_cost
end BB6.Agent9FirstReturn
