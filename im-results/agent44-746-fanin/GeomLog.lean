import LogBands
import Telescope
import LogStep
set_option maxHeartbeats 0
namespace CascadeAgent44

def geometricOddQ (n d t : Nat) : Nat := 2^t * 3^(n-t)*d
def geometricOddR (n d t : Nat) : Nat := 2^t * 3^(n-t-1)*d

theorem geometricOddQ_step (n d t : Nat) (ht : t<n) :
    geometricOddQ n d t = 3*geometricOddR n d t ∧
    geometricOddQ n d (t+1) = 2*geometricOddR n d t := by
  have he : n-t=(n-t-1)+1 := by omega
  have he' : n-(t+1) = n-t-1 := by omega
  constructor
  · dsimp [geometricOddQ,geometricOddR]
    have hepow : 3^(n-t)=3^(n-t-1)*3 := by
      calc
        3^(n-t)=3^((n-t-1)+1) := congrArg (fun k : Nat => 3^k) he
        _ = 3^(n-t-1)*3 := Nat.pow_succ ..
    rw [hepow]
    ac_rfl
  · dsimp [geometricOddQ,geometricOddR]
    rw [he',Nat.pow_succ]
    ac_rfl

theorem pos_geometricOddR (n d t:Nat) (hd:0<d) :
    0<geometricOddR n d t := by
  unfold geometricOddR
  have hp : 0 < 2^t := Nat.one_le_pow t 2 (by decide)
  have h3 : 0 < 3^(n-t-1) := Nat.one_le_pow (n-t-1) 3 (by decide)
  exact Nat.mul_pos (Nat.mul_pos hp h3) hd

theorem geometric_odd_log_step (n d t : Nat) (ht : t<n) (hd : 0<d) :
    Nat.log2 (geometricOddQ n d (t+1)) ≤
      Nat.log2 (geometricOddQ n d t) ∧
    Nat.log2 (geometricOddQ n d t) ≤
      Nat.log2 (geometricOddQ n d (t+1))+1 := by
  obtain ⟨hqt,hqt1⟩ := geometricOddQ_step n d t ht
  rw [hqt,hqt1]
  exact two_three_log_step _ (pos_geometricOddR n d t hd)

private theorem geometricOddQ_start (n d : Nat) :
    geometricOddQ n d 0 = 3^n*d := by
  simp [geometricOddQ]
private theorem geometricOddQ_end (n d : Nat) :
    geometricOddQ n d n = 2^n*d := by
  simp [geometricOddQ]

private theorem log2_two_pow_times (n d : Nat) (hd : 0<d) :
    Nat.log2 (2^n*d) = n + Nat.log2 d := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : 2^(n+1)*d = 2*(2^n*d) := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [he, Nat.log2_two_mul]
    · rw [ih]
      omega
    · have hp : 0<2^n := Nat.one_le_pow n 2 (by decide)
      have hprod : 0<2^n*d := Nat.mul_pos hp hd
      omega

theorem geometric_log_plateau_count (n d : Nat) (hd : 0<d) :
    sameLogCount (fun t => Nat.log2 (geometricOddQ n d t)) n +
      Nat.log2 (3^n*d) = 2*n + Nat.log2 d := by
  have hbase := sameLogCount_telescope_bounded
    (fun t => Nat.log2 (geometricOddQ n d t)) n
    (fun t ht => geometric_odd_log_step n d t ht hd)
  rw [geometricOddQ_start,geometricOddQ_end,log2_two_pow_times n d hd] at hbase
  have hrewrite : n+(n+Nat.log2 d)=2*n+Nat.log2 d := by omega
  exact hbase.trans hrewrite

private theorem odd_exact_power_one (a k : Nat) (ha : a%2=1)
    (he : a=2^k) : a=1 := by
  cases k with
  | zero => simpa using he
  | succ k =>
    have heven : a%2=0 := by
      rw [he,Nat.pow_succ,Nat.mul_mod]
      simp
    omega

private theorem odd_factor_in_power_two (i a k : Nat)
    (ha : a%2=1) (he : 2^i*a=2^k) : a=1 := by
  have hapos : 0<a := by omega
  have hlog := log2_two_pow_times i a hapos
  rw [he,log2_exact_power] at hlog
  have hpEq : 2^i*a = 2^i*2^(Nat.log2 a) := by
    calc
      2^i*a = 2^k := he
      _ = 2^(i+Nat.log2 a) := by rw [hlog]
      _ = 2^i*2^(Nat.log2 a) := Nat.pow_add ..
  have hTwo : a=2^(Nat.log2 a) := by
    have hp : 0 < 2^i := Nat.one_le_pow i 2 (by decide)
    exact Nat.eq_of_mul_eq_mul_left hp hpEq
  exact odd_exact_power_one a (Nat.log2 a) ha hTwo

private theorem pow_three_odd (e : Nat) : 3^e %2 =1 := by
  induction e with
  | zero => decide
  | succ e ih => rw [Nat.pow_succ,Nat.mul_mod,ih]

private theorem product_odd (e d : Nat) (hd : d%2=1) :
    (3^e*d)%2=1 := by
  rw [Nat.mul_mod,pow_three_odd,hd]

theorem geometric_odd_r_power_iff (n d t : Nat) (hd : d%2=1) (ht : t<n) :
    (∃k, geometricOddR n d t = 2^k) ↔ (t+1=n ∧ d=1) := by
  constructor
  · rintro ⟨k,hk⟩
    let e := n-t-1
    have he : 2^t*(3^e*d)=2^k := by
      simpa [geometricOddR,e,Nat.mul_assoc] using hk
    have hodd : (3^e*d)%2=1 := product_odd e d hd
    have heq : 3^e*d=1 := odd_factor_in_power_two t (3^e*d) k hodd he
    have hD : d=1 := Nat.eq_one_of_mul_eq_one_left heq
    have h3one : 3^e=1 := by
      simpa [hD] using heq
    have hE : e=0 := by
      by_cases he0 : e=0
      · exact he0
      · have hEpos : 0<e := by omega
        have hPow : 3≤3^e := by
          have hh : 1≤e := by omega
          have hv : 3^1 ≤ 3^e := Nat.pow_le_pow_right (by decide) hh
          exact hv
        omega
    have htEnd : t+1=n := by dsimp [e] at hE;omega
    exact ⟨htEnd,hD⟩
  · rintro ⟨htLast,hdOne⟩
    refine ⟨t,?_⟩
    simp [geometricOddR,hdOne,show n-t-1=0 by omega]

#print axioms geometric_odd_r_power_iff
#print axioms geometric_log_plateau_count
end CascadeAgent44
