import HalfRank
import FirstInverseComplete
set_option maxHeartbeats 0
namespace CascadeHalfRank
open CascadeResetInverse

private theorem eight_pow (k : Nat) : 8*2^k=2^(k+3) := by
  simp [Nat.pow_add]
  omega

private theorem four_pow (k : Nat) : 4*2^k=2^(k+2) := by
  simp [Nat.pow_add]
  omega

private theorem even_rank_decreases (h u k : Nat)
 (hband : 6*2^k-1 ≤ u ∧ u ≤ 8*2^k-3)
 (heq : 2*u = 8*2^k + h + k) : halfRank h < halfRank u := by
  have hp : 0 < 2^k := Nat.pow_pos (by decide)
  have hupos : 0<u := by omega
  have hlt : h<u := by omega
  have hbelow : 4*2^k ≤ u := by omega
  have habove : u<8*2^k := by omega
  have hm : u.log2=k+2 :=
    (Nat.log2_eq_iff (by omega : u≠0)).2 ⟨by simpa [four_pow] using hbelow,
      by simpa [eight_pow] using habove⟩
  by_cases heqm : h.log2=u.log2
  · have height : 2^(u.log2+1)=8*2^k := by
      rw [hm]
      have h : (k+2)+1=k+3 := by omega
      rw [h]
      exact (eight_pow k).symm
    have hdelta : 2*(2^(u.log2+1)-u) ≤ 2^(h.log2+1)-h := by
      rw [heqm, height]
      omega
    exact half_rank_lt_of_same_log_doubling h u heqm hupos hdelta
  · have hltm : h.log2 < u.log2 := by
      by_cases hh:h=0
      · simp [hh]; rw [hm]; omega
      · have hle:=log2_mono (by omega : 0<h) (by omega : h≤u)
        omega
    exact half_rank_lt_of_log_lt h u hltm hupos

private theorem odd_rank_decreases (h u k t d : Nat)
 (hband : 6*2^k+1 ≤ 2^t*d ∧ 2^t*d ≤ 8*2^k-1)
 (hout : 2*u+5=3^(t+1)*d)
 (heq : 2*(2^t*d)=8*2^k+h+k+5) :
 halfRank h < halfRank u := by
  have hp : 0<2^k := Nat.pow_pos (by decide)
  have hpow : 2^t≤3^t := Nat.pow_le_pow_left (by decide) t
  have hprod : 3*(2^t*d)≤3^(t+1)*d := by
    calc
      3*(2^t*d) ≤ 3*(3^t*d) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right d hpow)
      _ = 3^(t+1)*d := by rw [Nat.pow_succ]; ac_rfl
  have hulong : 8*2^k ≤ u := by omega
  have hhshort : h < 8*2^k := by omega
  have hlog : h.log2<u.log2 := by
    have hk : 0<k+3 := by omega
    have ha : h<2^(k+3) := by simpa [eight_pow] using hhshort
    have hb : 2^(k+3)≤u := by simpa [eight_pow] using hulong
    have hupos : u≠0 := by omega
    have hule : k+3≤u.log2 := (Nat.le_log2 hupos).2 hb
    by_cases hz : h=0
    · simp [hz]; omega
    · have hhlt : h.log2<k+3 := (Nat.log2_lt hz).2 ha
      omega
  have hupos : 0<u := by omega
  exact half_rank_lt_of_log_lt h u hlog hupos

/-- Strict decrease of the triangular binary rank along every exact
source first-reset inverse edge. -/
theorem reset_parent_half_rank_decreases (h u : Nat)
 (hp : ResetParent h u) : halfRank h < halfRank u := by
  rcases hp with ⟨k,hband,heq⟩ | ⟨k,t,d,hd,hband,hout,heq⟩
  · exact even_rank_decreases h u k hband heq
  · exact odd_rank_decreases h u k t d hband hout heq

#print axioms reset_parent_half_rank_decreases
end CascadeHalfRank
