import Std
set_option maxHeartbeats 0
namespace CascadeRank

theorem pow_pos (k : Nat) : 0 < 2^k := Nat.pow_pos (by decide)

theorem log2_mono {a b : Nat} (ha : 0<a) (hab : a≤b) : a.log2≤b.log2 := by
  have hb : b≠0 := by omega
  apply (Nat.le_log2 hb).2
  exact Nat.le_trans ((Nat.le_log2 (by omega : a≠0)).1 (Nat.le_refl _)) hab

theorem log2_lt_of_power (h u k : Nat) (hk : 0<k)
    (hh : h<2^k) (hu : 2^k≤u) : h.log2 < u.log2 := by
  have hupos : u≠0 := by have hp:=pow_pos k; omega
  have hule : k≤u.log2 := (Nat.le_log2 hupos).2 hu
  by_cases hzero : h=0
  · simp [hzero]; omega
  · have hhlt : h.log2<k := (Nat.log2_lt hzero).2 hh
    omega

theorem delta_pos (u : Nat) (hu : 0<u) :
    0 < 2^(u.log2+1)-u := by
  have hup : u<2^(u.log2+1) := (Nat.log2_lt (by omega : u≠0)).1 (by omega)
  omega

theorem delta_log_bound (u : Nat) (hu : 0<u) :
    (2^(u.log2+1)-u).log2 ≤ u.log2 := by
  have hlo : 2^u.log2 ≤ u := (Nat.le_log2 (by omega : u≠0)).1 (by omega)
  have hp : 0<2^(u.log2+1)-u := delta_pos u hu
  have he : 2^(u.log2+1)=2*2^u.log2 := by
    rw [Nat.pow_succ]; omega
  have hsmall : 2^(u.log2+1)-u ≤ 2^u.log2 := by omega
  calc
    (2^(u.log2+1)-u).log2 ≤ (2^u.log2).log2 := log2_mono hp hsmall
    _ = u.log2 := Nat.log2_two_pow

def reverseRank (u : Nat) : Nat :=
  (u.log2+1)^2 - (2^(u.log2+1)-u).log2

theorem rank_lt_of_log_lt (h u : Nat)
  (hlog : h.log2<u.log2) (hu : 0<u) : reverseRank h < reverseRank u := by
  let a := h.log2
  let b := u.log2
  let c := (2^(u.log2+1)-u).log2
  have hcb : c≤b := delta_log_bound u hu
  have hab : a+1≤b := by dsimp [a,b] at *; omega
  have hsquare : (a+1)^2≤b^2 := by
    exact Nat.pow_le_pow_left hab 2
  have hbstrict : b^2 < (b+1)^2 - c := by
    have he : (b+1)^2 = b^2 + 2*b+1 := by
      simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    omega
  have hrh : reverseRank h ≤ (a+1)^2 := by
    simp only [reverseRank]
    dsimp [a]
    omega
  have hru : reverseRank u = (b+1)^2-c := rfl
  omega

theorem rank_lt_of_same_log_doubling (h u : Nat)
 (hlog : h.log2=u.log2) (hu : 0<u)
 (hd : 2*(2^(u.log2+1)-u) ≤ 2^(h.log2+1)-h) :
 reverseRank h < reverseRank u := by
  have hdp : 0 < 2^(u.log2+1)-u := delta_pos u hu
  have hlt : (2^(u.log2+1)-u).log2 < (2^(h.log2+1)-h).log2 := by
    have hle : (2*(2^(u.log2+1)-u)).log2 ≤ (2^(h.log2+1)-h).log2 :=
      log2_mono (by omega) hd
    rw [Nat.log2_two_mul (by omega : 2^(u.log2+1)-u≠0)] at hle
    omega
  have hbpos : (u.log2+1)^2 > (2^(u.log2+1)-u).log2 := by
    have hbound := delta_log_bound u hu
    have hsquare : u.log2+1 ≤ (u.log2+1)^2 :=
      Nat.le_pow (by omega)
    omega
  have hltprime : (2^(u.log2+1)-u).log2 < (2^(u.log2+1)-h).log2 := by
    simpa only [hlog] using hlt
  dsimp [reverseRank]
  rw [hlog]
  omega

end CascadeRank
