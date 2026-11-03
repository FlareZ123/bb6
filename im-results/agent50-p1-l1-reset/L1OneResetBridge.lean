import L1OneResetArithmetic
import RootWallArithmetic
import P1InverseLog

namespace BB6.Agent50L1OneReset
open BB6.Agent1RootWall
open BB6.Agent1Quarter
open BB6.Agent1UpperTail
open BB6.Agent47P1
open BB6.Agent45TwoRoot

/-- Any authentic positive-depth inverse of the L1 q-sector feeder,
    followed by an arbitrary number of depth-zero odd inverse edges,
    misses the affine wall b=4*m+64*q+16. -/
theorem l1_first_reset_no_wall
    (q t k c b d m n : Nat)
    (hq : 1 ≤ q) (ht : 1 ≤ t) (hk : 2 ≤ k) (hc : c%2=1)
    (hi : inverseAt (6*u2 q-2) (2*u2 q+5) t = some (k,c))
    (htail : UpperTail (2*k-4) (c+4) (t+1) b d m n)
    (hwall : b=4*m+64*q+16) : False := by
  let u := u2 q
  let P := 2^(16*q)
  have hpowerbound : 65536*q*q ≤ P := large_power q hq
  have hqq : q≤q*q := by
    have h := Nat.mul_le_mul_right q hq
    omega
  have hpowq : 65536*(q*q)≤P := by
    calc
      65536*(q*q)=65536*q*q := by ac_rfl
      _≤P := hpowerbound
  have hqbig : 65536*q≤P := by
    have hh := Nat.mul_le_mul_left 65536 hqq
    omega
  have hNsmall : 20*q+8 < P := by omega
  have hu : u+4*q+3 = 7*P := by
    dsimp [u,u2,P]
    omega
  have hu1 : 1≤u := by omega
  have hi' : inverseAt (6*u-2) (2*u+5) t = some (k,c) := by
    simpa [u] using hi
  have hPow := inverseAt_power (6*u-2) (2*u+5) t k c hi'
  have hShift : 2*u+5+(6*u-2)/2+3=5*u+7 := by omega
  have hs : 2^t*(c+3)+20*q+8=35*P := by
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
      obtain ⟨v,hv⟩ := hPD
      refine ⟨v*(c+3),?_⟩
      rw [hv]
      ac_rfl
    have hP35 : P∣35*P := ⟨35,by ac_rfl⟩
    have hPsum : P∣2^t*(c+3)+(20*q+8) := by
      rw [show 2^t*(c+3)+(20*q+8)=35*P by omega]
      exact hP35
    have hPN : P∣20*q+8 :=
      (Nat.dvd_add_iff_right hPshift).mpr hPsum
    have hPsmall := Nat.le_of_dvd (by omega) hPN
    omega
  have hXD : 2^t ∣ P := by
    dsimp [P]
    exact Nat.pow_dvd_pow 2 htbound
  have hX35 : 2^t∣35*P := by
    obtain ⟨v,hv⟩ := hXD
    refine ⟨35*v,?_⟩
    rw [hv]
    ac_rfl
  have hXS : 2^t∣2^t*(c+3) := ⟨c+3,rfl⟩
  have hXsum : 2^t∣2^t*(c+3)+(20*q+8) := by
    rw [show 2^t*(c+3)+(20*q+8)=35*P by omega]
    exact hX35
  have hXN : 2^t∣20*q+8 :=
    (Nat.dvd_add_iff_right hXS).mpr hXsum
  have hsmallt : 2^t≤20*q+8 := Nat.le_of_dvd (by omega) hXN
  obtain ⟨r,hr⟩ := hXN
  let p0 := 2^(16*q-t)
  have hPfact : P=2^t*p0 := by
    dsimp [P,p0]
    rw [←Nat.pow_add]
    congr 1
    omega
  have hXpos : 1≤2^t := Nat.two_pow_pos _
  have hrbound : r≤20*q+8 := by
    have hh := Nat.mul_le_mul_right r hXpos
    omega
  have hyr : c+3+r=35*p0 := by
    have hh : 2^t*(c+3+r)=2^t*(35*p0) := by
      calc
        2^t*(c+3+r)=2^t*(c+3)+2^t*r := by rw [Nat.mul_add]
        _=35*P := by omega
        _=2^t*(35*p0) := by rw [hPfact]; ac_rfl
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) hh
  let K := 32*q+12+2*t-r
  have hKsum : K+r=32*q+12+2*t := by dsimp [K]; omega
  have hK : 0<K := by dsimp [K]; omega
  have hKmax : K≤64*q+12 := by dsimp [K]; omega
  have hP2 : P%2=0 := by
    have htwodiv : 2 ∣ P := by
      have htwo : (2:Nat)^1 ∣ 2^(16*q) :=
        Nat.pow_dvd_pow 2 (by omega : 1≤16*q)
      simpa [P] using htwo
    exact Nat.dvd_iff_mod_eq_zero.mp htwodiv
  have huodd : u%2=1 := by omega
  have hmod4 : (6*u-2)%4=0 := by omega
  have hb8 : 8≤6*u-2 := by omega
  have hmass0 := inverseAt_odd_cost (6*u-2) (2*u+5) t k c
    hb8 hmod4 (by omega) hi' hc
  have hmass : (2*k-4)+12+32*q+12+2*t+(c+3)=56*P := by
    omega
  let B := (2*k-4)+12
  have hBalance : B+K+35*p0=56*P := by dsimp [B]; omega
  have htail' := upper_tail_dyadic (2*k-4) (c+4)
    (t+1) b d m n htail
  have hWall : B=2^n*(4*(t+1+n)+64*q+28) := by
    calc
      B = 2^n*(b+12) := htail'.1.symm
      _ = 2^n*(4*(t+1+n)+64*q+28) := by
        rw [hwall,htail'.2]
  exact no_one_reset_l1_budget q t n p0 B K hq ht htbound
    hsmallt rfl hK hKmax hBalance hWall hpowerbound

#print axioms l1_first_reset_no_wall
end BB6.Agent50L1OneReset
