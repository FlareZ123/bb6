import DyadicReach

namespace BB6.Agent21Dyadic
namespace OpenMonotone

/-- The first and final inverse gap contribute independently; this
    lets us truncate an inverse word without losing the bit congruence. -/
theorem positive_prefix_of_append (w:List Nat)(r:Nat)
    (hp:Positive (w++[r])):Positive w := by
  intro k hk
  exact hp k (by simp [hk])

theorem cost_append_single (w:List Nat)(r:Nat):
    cost (w++[r])=cost w+r := by
  simp [cost]

theorem acc_append_single (s:Int)(w:List Nat)(r:Nat):
    acc s (w++[r])=acc s w+P (cost w)*offset (s+drift w) r := by
  rw [acc_append]
  simp [acc]

theorem acc_last_extend (s:Int)(w:List Nat)(r:Nat):
    acc s (w++[r+2])=acc s (w++[r]) := by
  rw [acc_append_single,acc_append_single,offset_extend]

theorem open_prefix_dvd (s z:Int)(w:List Nat)(r n:Nat)
    (hc:cost w=n)(h:P (n+1)∣z+acc s (w++[r])):
    P n∣z+acc s w := by
  have hd:P n∣z+acc s (w++[r]):=Int.dvd_trans (P_dvd n (n+1) (by omega)) h
  rw [acc_append_single,hc] at hd
  have hm:P n∣P n*offset (s+drift w) r:=Int.dvd_mul_right _ _
  have he:=Int.dvd_sub hd hm
  have ht:(z+(acc s w+P n*offset (s+drift w) r))-P n*offset (s+drift w) r=z+acc s w:=by omega
  rwa [ht] at he

/-- The full completed/pending inverse language is *nested downward*
    in dyadic precision. In the pending case, the final gap contracts
    by two and its exact signed accumulator remains unchanged. -/
theorem open_at_down (s z:Int)(n:Nat)
    (ho:OpenAt s z (n+1)) : OpenAt s z n := by
  rcases ho with ⟨w,hp,hc,hdiv⟩ | ⟨w,r,hr,hp,hc,hdiv⟩
  · have hnonempty:w≠[]:=by
      intro hw
      simp [hw,cost] at hc
    cases hrev:w.reverse with
    | nil =>
        have hw:w=[]:=by
          have hh:=congrArg List.reverse hrev
          simpa using hh
        exact (hnonempty hw).elim
    | cons r v =>
        have hw:w=v.reverse++[r]:=by
          have hh:=congrArg List.reverse hrev
          simpa [List.reverse_cons] using hh
        have hr:0<r:=hp r (by rw [hw];simp)
        by_cases hone:r=1
        · subst r
          have hc':cost v.reverse=n:=by
            rw [hw,cost_append_single] at hc
            omega
          have hpd:P n∣z+acc s v.reverse:=by
            rw [hw] at hdiv
            exact open_prefix_dvd s z v.reverse 1 n hc' hdiv
          left
          refine ⟨v.reverse,?_,hc',hpd⟩
          exact positive_prefix_of_append _ _ (by simpa only [hw] using hp)
        · right
          have hr2:2≤r:=by omega
          refine ⟨v.reverse,r,hr2,?_,?_,?_⟩
          · simpa only [hw] using hp
          · simpa only [hw] using hc
          · simpa only [hw] using (Int.dvd_trans (P_dvd n (n+1) (by omega)) hdiv)
  · by_cases h2:r=2
    · subst r
      have hc':cost w=n:=by
        rw [cost_append_single] at hc
        omega
      left
      refine ⟨w,positive_prefix_of_append w 2 hp,hc',?_⟩
      exact open_prefix_dvd s z w 2 n hc' hdiv
    · let k:=r-2
      have hk:0<k:=by dsimp [k];omega
      have hkr:k+2=r:=by dsimp [k];omega
      have hcost:cost (w++[k])=n:=by
        rw [cost_append_single] at hc ⊢
        dsimp [k]
        omega
      have hpos:Positive (w++[k]):=by
        intro j hj
        simp only [List.mem_append,List.mem_singleton] at hj
        rcases hj with hj|hj
        · exact hp j (by simp [hj])
        · subst j; exact hk
      have heq:acc s (w++[k])=acc s (w++[r]):=by
        rw [←hkr]
        exact (acc_last_extend s w k).symm
      have hdiv':P n∣z+acc s (w++[k]):=by
        have hw := Int.dvd_trans (P_dvd n (n+1) (by omega)) hdiv
        rwa [heq]
      exact Or.inl ⟨w++[k],hpos,hcost,hdiv'⟩

/-- Arbitrary downward extension, not merely a one-bit reduction. -/
theorem open_at_down_add (s z:Int)(n k:Nat)
    (ho:OpenAt s z (n+k)) : OpenAt s z n := by
  induction k with
  | zero => simpa using ho
  | succ k ih =>
      have h':OpenAt s z (n+k+1) := by simpa only [Nat.add_succ] using ho
      exact ih (open_at_down s z (n+k) h')

#print axioms open_at_down
#print axioms open_at_down_add

end OpenMonotone
end BB6.Agent21Dyadic
