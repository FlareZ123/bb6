import Std

namespace BB6.P1DualValuation

private theorem big16_aux (r : Nat) :
    20*(r+1)+8 < 2^(16*(r+1)) := by
  induction r with
  | zero => decide
  | succ r ih =>
    have hp : 2^(16*(r+1+1)) = 65536*2^(16*(r+1)) := by
      have he : 16*(r+1+1)=16*(r+1)+16 := by omega
      rw [he,Nat.pow_add, show (2:Nat)^16=65536 by decide]
      omega
    rw [show r+1+1=r+2 by omega,
        show 16*(r+2)=16*(r+1+1) by omega, hp]
    omega

private theorem big16 (q : Nat) (hq : 1≤q) :
    4*(5*q+2)<2^(16*q) := by
  cases q with
  | zero => omega
  | succ r =>
    have hb:=big16_aux r
    omega

def shift (q : Nat) : Nat := 35*2^(16*q)-4*(5*q+2)

private theorem shift_identity (q:Nat) (hq:1≤q) :
    shift q + 4*(5*q+2) = 35*2^(16*q) := by
  have hbig:=big16 q hq
  simp only [shift]
  omega

private theorem shift_small (q t : Nat) (hq:1≤q) (ht:t+2≤16*q) :
    (2^(t+2) ∣ shift q) ↔ (2^t ∣ 5*q+2) := by
  have hG:=shift_identity q hq
  have hdiv : 2^(t+2) ∣ 35*2^(16*q) := by
    obtain ⟨z,hz⟩:= Nat.pow_dvd_pow 2 ht
    refine ⟨35*z,?_⟩
    rw [hz]
    ac_rfl
  have hpow:2^(t+2)=4*2^t := by
    have he:t+2=2+t:=by omega
    rw [he,Nat.pow_add]
  have hcancel : (2^(t+2) ∣ 4*(5*q+2)) ↔ (2^t ∣ 5*q+2) := by
    rw [hpow]
    exact Nat.mul_dvd_mul_iff_left (by decide : 0<4)
  have hs1 : 35*2^(16*q)-shift q=4*(5*q+2) := by omega
  have hs2 : 35*2^(16*q)-4*(5*q+2)=shift q := by
    simp [shift]
  constructor
  · intro hv
    exact hcancel.mp (hs1 ▸ Nat.dvd_sub hdiv hv)
  · intro hv
    exact hs2 ▸ Nat.dvd_sub hdiv (hcancel.mpr hv)

private theorem shift_not_pow16 (q:Nat) (hq:1≤q) :
    ¬ (2^(16*q) ∣ shift q) := by
  intro hv
  have hG:=shift_identity q hq
  have hdiv : 2^(16*q) ∣ 35*2^(16*q) := by
    refine ⟨35,?_⟩
    ac_rfl
  have hh:35*2^(16*q)-shift q=4*(5*q+2):=by omega
  have hm: 2^(16*q) ∣ 4*(5*q+2) := by
    rw [←hh]
    exact Nat.dvd_sub hdiv hv
  have hbig:=big16 q hq
  have hle:=Nat.le_of_dvd (by omega : 0<4*(5*q+2)) hm
  omega

private theorem shift_no_big_rhs (q t:Nat) (hq:1≤q) (ht:16*q<t+2) :
    ¬ (2^t ∣ 5*q+2) := by
  intro hv
  have hb:=big16 q hq
  have hpos:2≤16*q:=by omega
  have he:2^(16*q)=4*2^(16*q-2):=by
    have e:16*q=(16*q-2)+2:=by omega
    calc
      2^(16*q) = 2^((16*q-2)+2) := congrArg (fun n:Nat=>2^n) e
      _ = 2^(16*q-2)*4 := by rw [Nat.pow_add]
      _ = 4*2^(16*q-2) := by omega
  have hm:5*q+2 < 2^(16*q-2) := by omega
  have hdiv:2^(16*q-2) ∣ 2^t := Nat.pow_dvd_pow 2 (by omega)
  have hsmall :2^(16*q-2) ∣ 5*q+2 := Nat.dvd_trans hdiv hv
  have hg:=Nat.le_of_dvd (by omega : 0<5*q+2) hsmall
  omega

theorem shift_all_powers (q t:Nat) (hq:1≤q):
    (2^(t+2) ∣ shift q) ↔ (2^t ∣ 5*q+2) := by
  by_cases ht:t+2≤16*q
  · exact shift_small q t hq ht
  have hn:16*q<t+2:=by omega
  have hnleft : ¬(2^(t+2) ∣ shift q) := by
    intro hv
    have hdiv:2^(16*q) ∣ 2^(t+2) := Nat.pow_dvd_pow 2 (by omega)
    exact shift_not_pow16 q hq (Nat.dvd_trans hdiv hv)
  have hnright:=shift_no_big_rhs q t hq hn
  simp [hnleft,hnright]

/-- Exact arithmetic coupling of the two feeder parameters. -/
theorem feeder_factors_coprime (q : Nat) :
    Nat.Coprime (3*q+1) (5*q+2) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd (3*q+1) (5*q+2)
  have ha : g ∣ 3*q+1 := Nat.gcd_dvd_left _ _
  have hb : g ∣ 5*q+2 := Nat.gcd_dvd_right _ _
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  have h5a : g ∣ 5*(3*q+1) := by
    refine ⟨5*x, ?_⟩
    rw [hx]
    ac_rfl
  have h3b : g ∣ 3*(5*q+2) := by
    refine ⟨3*y, ?_⟩
    rw [hy]
    ac_rfl
  have hdiff : 3*(5*q+2)-5*(3*q+1)=1 := by omega
  have hone : g ∣ 1 := by
    rw [←hdiff]
    exact Nat.dvd_sub h3b h5a
  exact Nat.dvd_one.mp hone

theorem complementary_parity (q:Nat):
    ((3*q+1)%2=0) ↔ ((5*q+2)%2=1) := by omega

/-- The second feeder's G-inverse shift with u2(q)=7*2^(16*q)-4*q-3. -/
theorem second_feeder_shift (q : Nat) (hq : 1 ≤ q) :
    5*(7*2^(16*q)-4*q-3)+7 = shift q := by
  have hb := big16 q hq
  simp only [shift]
  omega

/-- For odd q the second feeder's shifted counter has valuation exactly 2. -/
theorem second_feeder_odd_exact (q : Nat) (hq : 1 ≤ q)
    (ho : q%2=1) :
    (4 ∣ shift q) ∧ ¬ (8 ∣ shift q) := by
  have h4 : 4 ∣ shift q := by
    simpa using (shift_all_powers q 0 hq).mpr (by simp)
  have h8 : ¬ 8 ∣ shift q := by
    intro h
    have hh : 2 ∣ 5*q+2 :=
      (shift_all_powers q 1 hq).mp (by simpa using h)
    have hmod : (5*q+2)%2=1 := by omega
    have he : (5*q+2)%2=0 := Nat.dvd_iff_mod_eq_zero.mp hh
    omega
  exact ⟨h4,h8⟩

theorem dual_no_simultaneous_deep (q : Nat) (hq : 1 ≤ q) :
    ¬ ((2 ∣ 3*q+1) ∧ (8 ∣ shift q)) := by
  rintro ⟨hl,hr⟩
  have hm : 2 ∣ 5*q+2 :=
    (shift_all_powers q 1 hq).mp (by simpa using hr)
  have hfactor := feeder_factors_coprime q
  have hc : Nat.Coprime (3*q+1) (5*q+2) := hfactor
  have hodd : (3*q+1)%2=1 ∨ (5*q+2)%2=1 := by
    have hkey := complementary_parity q
    omega
  rcases hodd with ha | hb
  · exact (by omega : False)
  · exact (by omega : False)

#print axioms second_feeder_shift
#print axioms second_feeder_odd_exact
#print axioms dual_no_simultaneous_deep
#print axioms shift_all_powers
#print axioms complementary_parity
#print axioms feeder_factors_coprime

end BB6.P1DualValuation
