import OneResetArithmetic
import P1InverseLog

namespace BB6.Agent1OneReset
open BB6.Agent1RootWall
open BB6.Agent1Quarter
open BB6.Agent1UpperTail
open BB6.Agent47P1
open BB6.Agent45TwoRoot

/-- Authentic L0 first positive-depth inverse, followed by an arbitrary
    length all-upper inverse tail, cannot land on the P1 q-sector wall.
    Every inverse is the exact original source inverseAt. -/
theorem l0_first_reset_no_wall
    (q t k c b d m n : Nat)
    (hq : 1≤q) (ht : 1≤t) (hk : 2≤k) (hc : c%2=1)
    (hi : inverseAt (4*u2 q-4) (4*u2 q+9) t = some (k,c))
    (htail : UpperTail (2*k-4) (c+4) (t+1) b d m n)
    (hwall : b=4*m+64*q+12) : False := by
  let u := u2 q
  let P := 2^(16*q)
  have hpowerbound : 65536*q*q≤P := large_power q hq
  have hqq : q≤q*q := by
    have h:=Nat.mul_le_mul_right q hq
    omega
  have hpowq : 65536*(q*q)≤P := by
    calc
      65536*(q*q)=65536*q*q := by ac_rfl
      _≤P := hpowerbound
  have hqbig : 65536*q≤P := by
    have hh := Nat.mul_le_mul_left 65536 hqq
    omega
  have hNsmall : 24*q+8<P := by omega
  have hu : u+4*q+3=7*P := by
    dsimp [u,u2,P]
    omega
  have hu1 : 1≤u := by omega
  have hi' : inverseAt (4*u-4) (4*u+9) t = some (k,c) := by
    simpa [u] using hi
  have hPow := inverseAt_power (4*u-4) (4*u+9) t k c hi'
  have hShift : 4*u+9+(4*u-4)/2+3=6*u+10 := by omega
  have hs : 2^t*(c+3)+24*q+8=42*P := by
    rw [hShift] at hPow
    omega
  have htbound : t≤16*q := by
    by_cases hle : t≤16*q
    · exact hle
    have hge : 16*q≤t := by omega
    have hPD : P∣2^t := by
      dsimp [P]
      exact Nat.pow_dvd_pow 2 hge
    have hPshift : P∣2^t*(c+3) := by
      obtain ⟨v,hv⟩:=hPD
      refine ⟨v*(c+3),?_⟩
      rw [hv]
      ac_rfl
    have hP42 : P∣42*P := ⟨42,by ac_rfl⟩
    have hPsum : P∣2^t*(c+3)+(24*q+8) := by
      rw [show 2^t*(c+3)+(24*q+8)=42*P by omega]
      exact hP42
    have hPN : P∣24*q+8 :=
      (Nat.dvd_add_iff_right hPshift).mpr hPsum
    have hPsmall := Nat.le_of_dvd (by omega) hPN
    omega
  have hXD : 2^t∣P := by
    dsimp [P]
    exact Nat.pow_dvd_pow 2 htbound
  have hX42 : 2^t∣42*P := by
    obtain ⟨v,hv⟩ := hXD
    refine ⟨42*v,?_⟩
    rw [hv]
    ac_rfl
  have hXS : 2^t ∣ 2^t*(c+3) := ⟨c+3,rfl⟩
  have hXsum : 2^t ∣ 2^t*(c+3)+(24*q+8) := by
    rw [show 2^t*(c+3)+(24*q+8)=42*P by omega]
    exact hX42
  have hXN : 2^t∣24*q+8 :=
    (Nat.dvd_add_iff_right hXS).mpr hXsum
  have hsmallt : 2^t≤24*q+8 :=
    Nat.le_of_dvd (by omega) hXN
  obtain ⟨r,hr⟩ := hXN
  let p0 := 2^(16*q-t)
  have hPfact : P=2^t*p0 := by
    dsimp [P,p0]
    rw [←Nat.pow_add]
    congr 1
    omega
  have hXpos : 1≤2^t := by exact Nat.two_pow_pos _
  have hrbound : r≤24*q+8 := by
    have hh := Nat.mul_le_mul_right r hXpos
    omega
  have hyr : c+3+r=42*p0 := by
    have hh : 2^t*(c+3+r)=2^t*(42*p0) := by
      calc
        2^t*(c+3+r)=2^t*(c+3)+2^t*r := by rw [Nat.mul_add]
        _ = 42*P := by omega
        _ = 2^t*(42*p0) := by rw [hPfact]; ac_rfl
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) hh
  let K := 32*q+10+2*t-r
  have hKsum : K+r=32*q+10+2*t := by dsimp [K]; omega
  have hK : 0<K := by dsimp [K]; omega
  have hKmax : K≤64*q+10 := by dsimp [K]; omega
  have hmass0 := inverseAt_odd_cost (4*u-4) (4*u+9) t k c
    (by omega) (by omega) (by omega) hi' hc
  have hmass : (2*k-4)+12+32*q+10+2*t+(c+3)=56*P := by
    omega
  let B := (2*k-4)+12
  have hBalance : B+K+42*p0=56*P := by dsimp [B]; omega
  have htail' := upper_tail_dyadic (2*k-4) (c+4)
    (t+1) b d m n htail
  have hWall : B=2^n*(4*(t+1+n)+64*q+24) := by
    calc
      B = 2^n*(b+12) := htail'.1.symm
      _ = 2^n*(4*(t+1+n)+64*q+24) := by
        rw [hwall,htail'.2]
  exact no_one_reset_l0_budget q t n p0 B K
    hq ht htbound hsmallt rfl hK hKmax hBalance hWall

#print axioms l0_first_reset_no_wall
end BB6.Agent1OneReset
