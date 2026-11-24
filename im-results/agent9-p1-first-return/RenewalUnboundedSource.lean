import RenewalSource
import RenewalUnbounded

namespace BB6.Agent9FirstReturn
open BB6.Agent1Quarter BB6P1Unit

/-- The exact critical right-five history cost has no uniform linear bound.
For each B the explicit computable threshold suffices for all n beyond it. -/
theorem source_right_five_cost_many (B n b m : Nat)
    (hn : BB6.Agent9Renewal.criticalThreshold B≤n)
    (h : OddCone (14*2^n-2*n-16) 3 b 5 m) : (B+1)*n+2<m := by
  let Q := 7*2^n-n-3
  have hpow := BB6.Agent9Renewal.critical_power B n hn
  have hBn : B*n+5*n<2^n := by simpa [Nat.add_mul] using hpow
  have hn14 : 14≤n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hroot : (14*2^n-2*n-16)+10=2*Q := by dsimp [Q]; omega
  obtain ⟨v,hv,_,hg⟩ := gap_of_oddcone _ Q b 5 m hroot h
  have hv2 : v=2 := by omega
  subst v
  obtain ⟨q,hq,hret⟩ := gap_return_at_cost hg
  apply Nat.lt_of_not_ge
  intro hle
  exact BB6.Agent9Renewal.no_return_many B n q (m+1) hn hq (by omega) (by omega) hret

#print axioms source_right_five_cost_many
end BB6.Agent9FirstReturn
