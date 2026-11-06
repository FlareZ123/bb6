import Lean
set_option maxHeartbeats 2000000

namespace BB6.Agent9BudgetFiniteK

/-- Kernel-decidable finite graph closure certificate at ANY dyadic cutoff K. -/
def checkGraphK (K L : Nat) (nodes : List (Nat×Nat)) : Bool :=
  nodes.all fun p =>
    (List.range K).all fun t =>
      decide (p.2 % 2^t ≠ 0 ∨
        (L+p.1+t+p.2/2^t)%2 ≠ 1 ∨
        (p.1+t+1,(L+p.1+t+p.2/2^t)/2) ∈ nodes)

theorem checkGraphK_sound (K L : Nat) (nodes : List (Nat×Nat))
    (hc : checkGraphK K L nodes = true)
    (m z t v zp : Nat) (hm : (m,z) ∈ nodes) (ht : t < K)
    (hdiv : z = 2^t*v) (hn : 2*zp+1 = L+m+t+v) :
    (m+t+1,zp) ∈ nodes := by
  have hh := (List.all_eq_true.mp hc) (m,z) hm
  have hhc := (List.all_eq_true.mp hh) t (List.mem_range.mpr ht)
  have hp : z%2^t ≠ 0 ∨ (L+m+t+z/2^t)%2 ≠ 1 ∨
      (m+t+1,(L+m+t+z/2^t)/2) ∈ nodes := of_decide_eq_true hhc
  have hmod : z%2^t = 0 := Nat.mod_eq_zero_of_dvd ⟨v,hdiv⟩
  have hquot : z/2^t = v := by
    rw [hdiv]
    exact Nat.mul_div_cancel_left v (Nat.pow_pos (by decide))
  have hpar : (L+m+t+z/2^t)%2=1 := by
    rw [hquot, ←hn]
    omega
  have hhalf : (L+m+t+z/2^t)/2=zp := by
    rw [hquot, ←hn]
    omega
  rcases hp with hx | hx | hx
  · exact False.elim (hx hmod)
  · exact False.elim (hx hpar)
  · simpa [hhalf] using hx

/-- Any full graph with no coordinate divisible by 2^K is closed
    under every true edge depth, even when depths are unbounded a priori. -/
theorem closed_of_checkK (K B L : Nat) (nodes : List (Nat×Nat))
    (hc : checkGraphK K L nodes = true)
    (hb : nodes.all (fun p => decide (p.1≤B ∧ ¬2^K∣p.2)) = true)
    (m z t v zp : Nat) (hm : (m,z) ∈ nodes)
    (hd : z=2^t*v) (hn : 2*zp+1=L+m+t+v) :
    (m+t+1,zp)∈nodes := by
  have hnode := (List.all_eq_true.mp hb) (m,z) hm
  have hnodiv : ¬2^K∣z := (of_decide_eq_true hnode).2
  have ht : t<K := by
    by_cases h : t<K
    · exact h
    have hp : 2^K∣2^t := Nat.pow_dvd_pow 2 (by omega)
    exact False.elim (hnodiv (Nat.dvd_trans hp ⟨v,hd⟩))
  exact checkGraphK_sound K L nodes hc m z t v zp hm ht hd hn

#print axioms closed_of_checkK
end BB6.Agent9BudgetFiniteK
