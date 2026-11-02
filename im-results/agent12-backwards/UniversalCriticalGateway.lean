import AllFourCritical

namespace BB6.Agent12

/-- A universal backward gateway: any positive reset target with no
    matching exponential corridor must be preceded by (d-6,3). -/
theorem blank_two_d_gateway (d:Nat) (hdlarge:30≤d)
    (hdeven:d%2=0) (hnocorr:∀k:Nat,d+8≠14*2^k)
    (hr:BlankReach 2 d) : BlankReach (d-6) 3 := by
  obtain ⟨a,c,hpre,ht⟩ := blank_predecessor 2 d hr (Or.inr (by omega))
  obtain ⟨ha,hc⟩ := T_to_two_positive a c d (by omega) ht
  have haodd:a%2=1 := by omega
  cases hpre with
  | init => omega
  | next x y _ _ hpre2 ht2 =>
      rcases T_odd_left_predecessor x y a c ht2 haodd with hfirst | hsecond
      · obtain ⟨hy,hb,hd'⟩ := hfirst
        have hxodd:x%2=1 := by omega
        cases hpre2 with
        | init => omega
        | next u v _ _ hpre3 ht3 =>
            rcases T_odd_left_predecessor u v x y ht3 hxodd with hh | hh
            · omega
            · obtain ⟨hu,hv,_,_⟩ := hh
              have hu':u=d-6 := by omega
              have hv':v=3 := by omega
              simpa [hu',hv'] using hpre3
      · obtain ⟨hx,hy,_,_⟩ := hsecond
        obtain ⟨k,hcorr⟩ := blank_even_even_shape x y hpre2
          (by omega) (by omega) hx
        have hneq := hnocorr k
        apply False.elim
        apply hneq
        omega

/-- Every critical target of index n>=2 requires an actual blank-start
    excursion through one specific c=3 gateway. -/
theorem blank_critical_requires_gateway (n:Nat) (hn:2≤n)
    (hr:BlankReach 2 (14*2^n-2*n-10)) :
    BlankReach (14*2^n-2*n-16) 3 := by
  have hbound : ∀j:Nat, j+1≤2^j := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      rw [Nat.pow_succ]
      omega
  have hs:=hbound (n-1)
  have hpowe:2^n=2*(2^(n-1)) := by
    have he:2^n=2^(n-1+1) := by congr 1;omega
    rw [Nat.pow_succ] at he
    omega
  have hl:30≤14*2^n-2*n-10 := by omega
  have hdeven:(14*2^n-2*n-10)%2=0 := by omega
  have hg:=blank_two_d_gateway (14*2^n-2*n-10) hl hdeven
    (fun k => critical_between_no_corridor n k hn) hr
  have heq:(14*2^n-2*n-10)-6=14*2^n-2*n-16 := by omega
  simpa [heq] using hg

#print axioms BB6.Agent12.blank_critical_requires_gateway
end BB6.Agent12
