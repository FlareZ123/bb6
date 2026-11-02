import PosEvenForm

namespace BB6.P1Deep
open BB6.Agent1

def left (L K i : Nat) : Nat := 8 * 2^(L-i) * K - 12

def right (L K : Nat) : Nat → Nat
  | 0 => 3
  | i+1 => right L K i + left L K (i+1) + 10

private theorem pow_times_lower (K e : Nat) (hK : 3 ≤ K) :
    3 ≤ 2^e * K := by
  have hpow : 1 ≤ (2:Nat)^e := Nat.one_le_pow e 2 (by decide)
  calc
    3 = 1*3 := by omega
    _ ≤ 2^e * 3 := Nat.mul_le_mul_right 3 hpow
    _ ≤ 2^e * K := Nat.mul_le_mul_left (2^e) hK

theorem left_positive_mod (L K i : Nat) (hK : 3 ≤ K) :
    12 ≤ left L K i ∧ left L K i % 4 = 0 := by
  have ht := pow_times_lower K (L-i) hK
  have hfac : 8 * 2^(L-i) * K = 8 * (2^(L-i)*K) := by simp [Nat.mul_assoc]
  dsimp [left]
  rw [hfac]
  omega

theorem left_step (L K i : Nat) (hK : 3 ≤ K) (hi : i < L) :
    left L K i = 2*left L K (i+1)+12 := by
  have he : L-i = (L-(i+1))+1 := by omega
  have hh : 2^(L-i) = 2 * 2^(L-(i+1)) := by
    rw [he,Nat.pow_succ]
    omega
  have hl := pow_times_lower K (L-(i+1)) hK
  have hf1 : 8 * (2 * 2^(L-(i+1))) * K = 16*(2^(L-(i+1))*K) := by
    calc
      _ = (8*2)*(2^(L-(i+1))*K) := by ac_rfl
      _ = 16*(2^(L-(i+1))*K) := by rfl
  have hf2 : 8 * 2^(L-(i+1)) * K = 8*(2^(L-(i+1))*K) := by simp [Nat.mul_assoc]
  dsimp [left]
  rw [hh,hf1,hf2]
  omega

theorem right_odd (L K i : Nat) (hK : 3 ≤ K) :
    3 ≤ right L K i ∧ right L K i % 2 = 1 := by
  induction i with
  | zero => simp [right]
  | succ i ih =>
    have hl := left_positive_mod L K (i+1) hK
    simp only [right]
    omega

/-- Exact two-T-step upper-G preimage of an arbitrary positive hub. -/
theorem high_pair (x d : Nat) (hx : 12 ≤ x) (hm : x % 4 = 0) (hd : 0 < d) :
    T x (d+x+10) = some (x+3,d+x+8) ∧
    T (x+3) (d+x+8) = some (2*x+12,d) := by
  have he : x%2=0 := by omega
  have hc0 : d+x+10 ≠ 0 := by omega
  have hc1 : d+x+10 ≠ 1 := by omega
  have hc02 : d+x+8 ≠ 0 := by omega
  have hc12 : d+x+8 ≠ 1 := by omega
  have hc22 : d+x+8 ≠ 2 := by omega
  have hc32 : d+x+8 ≠ 3 := by omega
  have ho : (x+3)%2 ≠ 0 := by omega
  have hk : (x+3)/2+1 = x/2+2 := by omega
  have hk2 : 2*(x/2+2)+2 = x+6 := by omega
  have hnotlow : ¬(d+x+6 < 2*(x/2+2)) := by omega
  have hnotmid : ¬(d+x+6 ≤ 2*(x/2+2)+1) := by omega
  have hg : G (x/2+2) (d+x+6) = (2*x+12,d) := by
    rw [G]
    simp only [hnotlow, dite_false, hnotmid, ite_false]
    have heq1 : 4*(x/2+2)+4 = 2*x+12 := by omega
    have heq2 : d+x+6-(2*(x/2+2)+2)=d := by omega
    simp only [heq1,heq2]
  constructor
  · simp [T, hc0, hc1, he]
  · have hdeq : d+x+8-2=d+x+6 := by omega
    simp [T,hc02,hc12,ho,hc22,hc32,hk,hdeq,hg]

/-- All links are valid original accelerated transitions, not just algebraic inversions. -/
theorem corridor_link (L K i : Nat) (hK : 3≤K) (hi : i<L) :
    T (left L K (i+1)) (right L K (i+1)) =
      some (left L K (i+1)+3, right L K (i+1)-2) ∧
    T (left L K (i+1)+3) (right L K (i+1)-2) =
      some (left L K i, right L K i) := by
  have hleft := left_positive_mod L K (i+1) hK
  have hright := right_odd L K i hK
  have hstep := left_step L K i hK hi
  have hp := high_pair (left L K (i+1)) (right L K i)
    hleft.1 hleft.2 (by omega)
  have hrd : right L K (i+1) = right L K i + left L K (i+1)+10 := rfl
  constructor
  · rw [hrd]
    have heq : right L K i + left L K (i+1) + 10 - 2 =
      right L K i + left L K (i+1) + 8 := by omega
    rw [heq]
    exact hp.1
  · rw [hrd]
    have heq : right L K i + left L K (i+1) + 10 - 2 =
      right L K i + left L K (i+1) + 8 := by omega
    rw [heq, hstep]
    exact hp.2

#print axioms BB6.P1Deep.corridor_link
end BB6.P1Deep
