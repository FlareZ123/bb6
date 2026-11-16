import FirstInverseComplete

namespace CascadeResetInverse

private theorem pow_two_le_three_scale (n : Nat) : 2^n ≤ 3^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.mul_le_mul ih (by decide)

private theorem odd_source_valuation_le_level
    (L t d : Nat)
    (hlo : 6*2^L+1 ≤ 2^t*d)
    (hhi : 2^t*d ≤ 8*2^L-1) :
    t ≤ L := by
  by_contra hnot
  have htl : L+1 ≤ t := by omega
  have hp : 2^(L+1) ≤ 2^t :=
    Nat.pow_le_pow_right (by decide) htl
  have hlo' : 6*2^L+1 ≤ 2^(L+1)*d :=
    le_trans hlo (Nat.mul_le_mul_right d hp)
  have hhi' : 2^(L+1)*d ≤ 8*2^L-1 :=
    le_trans (Nat.mul_le_mul_right d hp) hhi
  have hpow : 2^(L+1)=2*2^L := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [hpow] at hlo' hhi'
  have hdlo : 4 ≤ d := by
    by_contra h
    have hdhi : d ≤ 3 := by omega
    have hmul : 2*2^L*d ≤ 2*2^L*3 :=
      Nat.mul_le_mul_left (2*2^L) hdhi
    have hmul' : 2*2^L*3 = 6*2^L := by ring
    rw [hmul'] at hmul
    omega
  have hdhi : d ≤ 3 := by
    by_contra h
    have hdlo' : 4 ≤ d := by omega
    have hmul : 2*2^L*4 ≤ 2*2^L*d :=
      Nat.mul_le_mul_left (2*2^L) hdlo'
    have hmul' : 2*2^L*4 = 8*2^L := by ring
    rw [hmul'] at hmul
    omega
  omega

private theorem pow_ratio_three_two
    (t L : Nat) (ht : t ≤ L) :
    3^t*2^L ≤ 3^L*2^t := by
  obtain ⟨r, hr⟩ : ∃ r, L=t+r := ⟨L-t, by omega⟩
  rw [hr, Nat.pow_add]
  have h23 := pow_two_le_three_scale r
  calc
    3^t*(2^t*2^r) = (3^t*2^t)*2^r := by ac_rfl
    _ ≤ (3^t*2^t)*3^r := Nat.mul_le_mul_left (3^t*2^t) h23
    _ = (3^t*3^r)*2^t := by ac_rfl

private theorem two_mul_add_three_le_two_pow
    (K : Nat) (hK : 2 ≤ K) :
    2*K+3 ≤ 2*2^K := by
  let n := K-2
  have hK' : K=n+2 := by dsimp [n]; omega
  rw [hK']
  induction n with
  | zero => decide
  | succ n ih =>
      have hpow : 2^(n+3)=2^(n+2)*2 := by
        rw [show n+3=(n+2)+1 by omega, Nat.pow_succ]
      have hp : 1 ≤ 2^(n+2) :=
        Nat.one_le_pow (n+2) 2 (by decide)
      rw [show Nat.succ n+2=n+3 by omega, hpow]
      omega

/-- Exact scale bound for every odd arm of the first-reset parent grammar.
The source parameter is in the genuine odd band and the child has a
first-failure level K>=2. No blank-root reachability is assumed. -/
theorem odd_parent_level_scale_of_data
    (L t d u K : Nat)
    (hodd : d%2=1)
    (hband : 6*2^L+1 ≤ 2^t*d ∧ 2^t*d ≤ 8*2^L-1)
    (hout : 2*u+5=3^(t+1)*d)
    (hK : 2 ≤ K)
    (hlevel : 4*2^K ≤ u+K+4) :
    t ≤ L ∧ 2^(K-2) < 3^L := by
  have ht : t ≤ L :=
    odd_source_valuation_le_level L t d hband.1 hband.2
  have hP : 2^t*d < 8*2^L := by omega
  let X : Nat := 2*u+5
  have hX : X=3^(t+1)*d := by
    dsimp [X]
    exact hout
  have hmul : 2^t*X < 3^(t+1)*(8*2^L) := by
    calc
      2^t*X = 3^(t+1)*(2^t*d) := by rw [hX]; ac_rfl
      _ < 3^(t+1)*(8*2^L) :=
        Nat.mul_lt_mul_of_pos_left hP (Nat.pow_pos (by decide))
  have hratio := pow_ratio_three_two t L ht
  have hupper : 3^(t+1)*(8*2^L) ≤ 24*3^L*2^t := by
    rw [Nat.pow_succ]
    calc
      3^t*3*(8*2^L) = 24*(3^t*2^L) := by ring
      _ ≤ 24*(3^L*2^t) := Nat.mul_le_mul_left 24 hratio
      _ = 24*3^L*2^t := by ring
  have hmul' : 2^t*X < 2^t*(24*3^L) := by
    calc
      _ < 3^(t+1)*(8*2^L) := hmul
      _ ≤ 24*3^L*2^t := hupper
      _ = 2^t*(24*3^L) := by ac_rfl
  have hpos : 0 < 2^t := Nat.pow_pos (by decide)
  have hXupper : X < 24*3^L :=
    (Nat.mul_lt_mul_left hpos).mp hmul'
  have hlev' := Nat.mul_le_mul_left 2 hlevel
  have hlinear := two_mul_add_three_le_two_pow K hK
  have hXlower : 6*2^K ≤ X := by
    dsimp [X]
    omega
  have hcmp : 6*2^K < 24*3^L :=
    lt_of_le_of_lt hXlower hXupper
  have hpowK : 2^K=4*2^(K-2) := by
    calc
      2^K = 2^(K-2+2) := by congr 1; omega
      _ = 2^(K-2)*2^2 := by rw [Nat.pow_add]
      _ = 4*2^(K-2) := by norm_num
  have hmulK : 24*2^(K-2) < 24*3^L := by
    calc
      24*2^(K-2) = 6*(4*2^(K-2)) := by ring
      _ = 6*2^K := by rw [←hpowK]
      _ < 24*3^L := hcmp
  have hfinal : 2^(K-2) < 3^L :=
    (Nat.mul_lt_mul_left (by decide : 0 < 24)).mp hmulK
  exact ⟨ht,hfinal⟩

#print axioms odd_parent_level_scale_of_data

end CascadeResetInverse
