import AllOddCritical
import Mod16SixBarrier

namespace BB6.Agent12

/-- Odd-even corridor obstruction at the exact predecessor of an n=0 mod4 critical target. -/
theorem fourth_critical_between_powers (n m:Nat) (hn:4≤n)
    (heq:8*m+6=14*2^n-2*n-10) :
    14*2^(n-1)<6*m+8 ∧ 6*m+8<14*2^n := by
  have hbound : ∀j:Nat, j+1≤2^j := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      rw [Nat.pow_succ]
      omega
  have hsize := hbound (n-1)
  have hpowe : 2^n=2*(2^(n-1)) := by
    have he : 2^n = 2^(n-1+1) := by congr 1; omega
    rw [Nat.pow_succ] at he
    omega
  constructor <;> omega

theorem fourth_critical_no_corridor (n m k:Nat) (hn:4≤n)
    (heq:8*m+6=14*2^n-2*n-10) :
    6*m+8≠14*2^k := by
  obtain ⟨hl,hu⟩ := fourth_critical_between_powers n m hn heq
  by_cases hk:k<n
  · have hp:2^k≤2^(n-1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have hp:2^n≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- All critical targets indexed by multiples of four, n>=4, are unreachable. -/
theorem blank_no_all_four_critical (n:Nat) (hn:4≤n) (hmod:n%4=0) :
    ¬BlankReach 2 (14*2^n-2*n-10) := by
  let d:=14*2^n-2*n-10
  let m:=(d-6)/8
  have hbound : ∀j:Nat, j+1≤2^j := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      rw [Nat.pow_succ]
      omega
  have hs:=hbound n
  have hpow : (2^n)%8=0 := by
    have h3:n=n-3+3 := by omega
    rw [h3,Nat.pow_add]
    simp
  have hlarge : 30≤d := by dsimp[d];omega
  have hmod8 : d%8=6 := by dsimp[d];omega
  have hd : d=8*m+6 := by dsimp[m];omega
  have hmpos : 0<m := by omega
  intro hr
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
                  have hu8:u=8*m := by omega
                  have hv3:v=3 := by omega
                  cases hpre3 with
                  | init => omega
                  | next p q _ _ hpre4 ht4 =>
                      have ht4' : T p q=some (8*m,3) := by simpa [hu8,hv3] using ht4
                      rcases T_to_eight_multiple_three m p q hmpos ht4' with
                        ⟨hp,hq⟩ | ⟨hp,hq⟩
                      · have hpodd:p%2=1 := by omega
                        cases hpre4 with
                        | init => omega
                        | next s t _ _ hpre5 ht5 =>
                            rcases T_odd_left_predecessor s t p q ht5 hpodd with hh | hh
                            · omega
                            · obtain ⟨hs,ht,_,_⟩ := hh
                              have hinv:=blank_even_left_invariant s t hpre5 (by omega) hs
                              rcases hinv with h | h <;> omega
                      · have hpodd:p%2=1 := by omega
                        have hqpos:0<q := by omega
                        have hqeven:q%2=0 := by omega
                        obtain ⟨k,hcorr⟩ := (blank_even_right_corridors p q hpre4 hqpos hqeven).2 hpodd
                        have hneq:=fourth_critical_no_corridor n m k hn (by dsimp [d] at hd;omega)
                        apply hneq
                        omega
          · obtain ⟨hx,hy,_,_⟩ := hsecond
            have hinv:=blank_even_left_invariant x y hpre2 (by omega) hx
            rcases hinv with h | h <;> omega

#print axioms BB6.Agent12.blank_no_all_four_critical
end BB6.Agent12
