import Q33Finite

namespace BB6.Agent9BudgetFinite
open BB6.Agent9Q33

/-- Sound completion of a finite exact dyadic shadow graph at an arbitrary
    certified cost bound, with a fixed 10-bit source inverse-depth cutoff. -/
theorem closed_of_check (B L : Nat) (nodes : List (Nat×Nat))
    (hc : checkGraph L nodes = true)
    (hb : nodes.all (fun p => decide (p.1≤B ∧ ¬1024∣p.2)) = true)
    (m z t v zp : Nat) (hm : (m,z)∈nodes)
    (hdiv : z=2^t*v) (hn : 2*zp+1=L+m+t+v) :
    (m+t+1,zp)∈nodes := by
  have hnode := (List.all_eq_true.mp hb) (m,z) hm
  have hnodiv : ¬1024∣z := (of_decide_eq_true hnode).2
  have ht : t<10 := by
    by_cases hh : t<10
    · exact hh
    have hp : 1024∣2^t := by
      have hd : (2:Nat)^10∣2^t := Nat.pow_dvd_pow 2 (by omega)
      simpa using hd
    exact False.elim (hnodiv (Nat.dvd_trans hp ⟨v,hdiv⟩))
  exact checkGraph_sound L nodes hc m z t v zp hm ht hdiv hn

#print axioms closed_of_check
end BB6.Agent9BudgetFinite
