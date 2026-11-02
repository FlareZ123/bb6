import EvenEvenCorridor
import Mod32SixBarrier

namespace BB6.Agent12

/-- The critical right value sits strictly between two consecutive
    exponential-corridor values. -/
theorem critical_between_corridor_powers (n : Nat) (hn:2≤n) :
    14*2^(n-1) < (14*2^n - 2*n - 10)+8 ∧
    (14*2^n - 2*n - 10)+8 < 14*2^n := by
  have hbound : ∀ j:Nat, j+1≤2^j := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      rw [Nat.pow_succ]
      omega
  have hsize:=hbound n
  have hsize' := hbound (n-1)
  have hpowe : 2^n=2*(2^(n-1)) := by
    have he : 2^n = 2^(n-1+1) := by congr 1; omega
    rw [Nat.pow_succ] at he
    omega
  constructor <;> omega

/-- No critical n>=2 target can lie in the exact even-even corridor at (d-4,2). -/
theorem critical_between_no_corridor (n k:Nat) (hn:2≤n) :
    (14*2^n - 2*n - 10)+8 ≠ 14*2^k := by
  obtain ⟨hl,hu⟩ := critical_between_corridor_powers n hn
  by_cases hk:k<n
  · have hp:2^k≤2^(n-1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have hp:2^n≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- Every odd critical-index halting target beyond n=1 is unreachable from
    the *actual* blank-entry accelerated state, uniformly for all odd n. -/
theorem blank_no_all_odd_critical (n:Nat) (hn:3≤n) (hnodd:n%2=1) :
    ¬BlankReach 2 (14*2^n - 2*n - 10) := by
  let d:=14*2^n - 2*n - 10
  have hbound : ∀ j:Nat, j+1≤2^j := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      rw [Nat.pow_succ]
      omega
  have hsize:=hbound n
  have hpowmod : (2^n)%4=0 := by
    have h2:n=n-2+2 := by omega
    rw [h2,Nat.pow_add]
    simp
  have hlarge : 30≤d := by dsimp [d]; omega
  have hmod : d%4=0 := by dsimp [d]; omega
  intro hr
  obtain ⟨a,c,hpre,ht⟩ := blank_predecessor 2 d hr (Or.inr (by omega))
  obtain ⟨ha,hc⟩ := T_to_two_positive a c d (by omega) ht
  have haodd:a%2=1 := by omega
  cases hpre with
    | init => omega
    | next x y _ _ hpre2 ht2 =>
        rcases T_odd_left_predecessor x y a c ht2 haodd with hfirst | hsecond
        · obtain ⟨hy,hb,hd⟩ := hfirst
          have hxodd:x%2=1 := by omega
          cases hpre2 with
          | init => omega
          | next u v _ _ hpre3 ht3 =>
              rcases T_odd_left_predecessor u v x y ht3 hxodd with hh | hh
              · omega
              · obtain ⟨hu,hv,_,_⟩ := hh
                have hinv:=blank_even_left_invariant u v hpre3 (by omega) hu
                rcases hinv with h | h <;> omega
        · obtain ⟨hx,hy,_,_⟩ := hsecond
          obtain ⟨k,hcorr⟩ := blank_even_even_shape x y hpre2
            (by omega) (by omega) hx
          have hneq := critical_between_no_corridor n k (by omega)
          apply hneq
          dsimp [d] at *
          omega
#print axioms BB6.Agent12.blank_no_all_odd_critical
end BB6.Agent12
