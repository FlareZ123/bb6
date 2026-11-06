import Std
set_option maxHeartbeats 0
namespace CascadeHalfRank

def tri : Nat → Nat
  | 0 => 0
  | n+1 => tri n + n+1

theorem tri_mono (a b : Nat) (hab : a≤b) : tri a≤tri b := by
  induction b generalizing a with
  | zero =>
      have : a=0 := by omega
      subst a
      omega
  | succ b ih =>
      by_cases h:a≤b
      · have hh := ih a h
        have hstep : tri b≤tri (b+1) := by simp only [tri]; omega
        omega
      · have he:a=b+1 := by omega
        subst a
        omega

theorem tri_closed (n : Nat) : 2*tri n=n*(n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : tri (n+1)=tri n+n+1 := rfl
      rw [he]
      calc
        2*(tri n+n+1)=2*tri n+2*(n+1) := by omega
        _=n*(n+1)+2*(n+1) := by rw [ih]
        _=(n+1)*(n+2) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
          omega

theorem log2_mono {a b : Nat} (ha : 0<a) (hab : a≤b) : a.log2≤b.log2 := by
  have hb : b≠0 := by omega
  apply (Nat.le_log2 hb).2
  exact Nat.le_trans ((Nat.le_log2 (by omega : a≠0)).1 (Nat.le_refl _)) hab

theorem delta_pos (u : Nat) (hu : 0<u) :
    0<2^(u.log2+1)-u := by
  have hup : u<2^(u.log2+1) := (Nat.log2_lt (by omega : u≠0)).1 (by omega)
  omega

theorem delta_log_bound (u : Nat) (hu : 0<u) :
    (2^(u.log2+1)-u).log2 ≤ u.log2 := by
  have hlo : 2^u.log2 ≤ u := (Nat.le_log2 (by omega : u≠0)).1 (by omega)
  have hp : 0<2^(u.log2+1)-u := delta_pos u hu
  have he : 2^(u.log2+1)=2*2^u.log2 := by rw [Nat.pow_succ]; omega
  have hsmall : 2^(u.log2+1)-u ≤ 2^u.log2 := by omega
  calc
    (2^(u.log2+1)-u).log2 ≤ (2^u.log2).log2 := log2_mono hp hsmall
    _=u.log2 := Nat.log2_two_pow

def halfRank (u : Nat) : Nat :=
  tri (u.log2+1) - (2^(u.log2+1)-u).log2

theorem half_rank_lt_of_log_lt (h u : Nat)
    (hlog : h.log2<u.log2) (hu : 0<u) : halfRank h < halfRank u := by
  let a:=h.log2
  let b:=u.log2
  let c:=(2^(u.log2+1)-u).log2
  have hcb : c≤b := delta_log_bound u hu
  have hab : a+1≤b := by dsimp [a,b] at *; omega
  have ht : tri (a+1)≤tri b := tri_mono _ _ hab
  have hnext : tri (b+1)=tri b+b+1 := rfl
  have hstrict : tri b < tri (b+1)-c := by omega
  have hrh : halfRank h ≤ tri (a+1) := by dsimp [halfRank,a]; omega
  have hru : halfRank u = tri (b+1)-c := rfl
  omega

theorem half_rank_lt_of_same_log_doubling (h u : Nat)
    (hlog : h.log2=u.log2) (hu : 0<u)
    (hd : 2*(2^(u.log2+1)-u) ≤ 2^(h.log2+1)-h) :
    halfRank h < halfRank u := by
  have hdp : 0<2^(u.log2+1)-u := delta_pos u hu
  have hlt : (2^(u.log2+1)-u).log2 < (2^(h.log2+1)-h).log2 := by
    have hle : (2*(2^(u.log2+1)-u)).log2 ≤ (2^(h.log2+1)-h).log2 :=
      log2_mono (by omega) hd
    rw [Nat.log2_two_mul (by omega : 2^(u.log2+1)-u≠0)] at hle
    omega
  have hc : (2^(u.log2+1)-u).log2≤u.log2 := delta_log_bound u hu
  have htnext : tri (u.log2+1)=tri u.log2+u.log2+1 := rfl
  have htri : (2^(u.log2+1)-u).log2<tri (u.log2+1) := by omega
  have hltprime : (2^(u.log2+1)-u).log2<(2^(u.log2+1)-h).log2 := by
    simpa only [hlog] using hlt
  dsimp [halfRank]
  rw [hlog]
  omega

#print axioms half_rank_lt_of_log_lt
#print axioms half_rank_lt_of_same_log_doubling
end CascadeHalfRank
