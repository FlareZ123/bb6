import L1UpperPrefix
import L1AllPrefixArithmetic
import L1ScaledIdent

namespace BB6.Agent50L1All
open BB6.Agent1RootWall
open BB6.Agent1UpperTail
open BB6.Agent1Quarter
open BB6.Agent47P1
open BB6.Agent45TwoRoot

/-- The entire source-true L1 cone sector with exactly one positive-depth
    inverse and any number of upper steps before and after it misses the wall. -/
theorem l1_one_reset_cone_no_wall
    (q bp dp mp r t k c b d m n : Nat)
    (hq : 1≤q)
    (hpre : UpperTail (6*u2 q-2) (2*u2 q+5) 0 bp dp mp r)
    (hbp:8≤bp) (hb4:bp%4=0) (hdp:dp%2=1)
    (hi : inverseAt bp dp t=some (k,c))
    (ht:1≤t) (hk:2≤k) (hc:c%2=1)
    (hpost:UpperTail (2*k-4) (c+4) (mp+t+1) b d m n)
    (hwall:b=4*m+64*q+16) : False := by
  let P := 2^(16*q)
  let u := u2 q
  let X := 2^r
  let Y := 2^t
  let S := 32*q+12+2*r
  let V := 56*X-21
  let J := S*X-(12*q+4)
  have hPpos : 0<P := Nat.two_pow_pos _
  have hXpos : 0<X := Nat.two_pow_pos _
  have hXunit : 1≤X := Nat.two_pow_pos _
  have hlarge := large_power q hq
  have hlarge' : 65536*q*q≤P := hlarge
  have hqle : q≤q*q := by
    have hh := Nat.mul_le_mul_right q hq
    omega
  have hqbig : 65536*q≤P := by
    have hh:=Nat.mul_le_mul_left 65536 hqle
    have hbig : 65536*(q*q)≤P := by simpa only [Nat.mul_assoc] using hlarge
    omega
  have hu : u+4*q+3=7*P := by dsimp [u,u2,P]; omega
  have hu1 : 1≤u := by omega
  have hpreexact := upper_tail_dyadic (6*u2 q-2) (2*u2 q+5) 0 bp dp mp r hpre
  have hmp : mp=r := by omega
  have hroot : X*(bp+12)+24*q+8=42*P := by
    have hh : X*(bp+12)=6*u-2+12 := by simpa [X,u] using hpreexact.1
    omega
  have hXsmall : X≤6*q+2 := l1_upper_prefix_short q bp dp mp r hq hpre hb4
  have hr : r≤16*q := by
    by_cases hle : r≤16*q
    · exact hle
    have hh : P≤X := by
      dsimp [P,X]
      exact Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
    omega
  have hSbound : S≤76*q := by dsimp [S]; omega
  have hXbound : X≤8*q := by omega
  have hSpos : 0<S := by dsimp [S]; omega
  have hSmul : S≤S*X := by
    have hh:=Nat.mul_le_mul_left S hXunit
    simpa only [Nat.mul_one] using hh
  have hVdef : V+21=56*X := by
    have hh:=Nat.mul_le_mul_left 56 hXunit
    dsimp [V]
    omega
  have hJdef : J+12*q+4=S*X := by
    dsimp [J]
    omega
  have hJpos : 0<J := by
    dsimp [J]
    omega
  have hJbound : J≤608*(q*q) := by
    have hle : J≤S*X := by omega
    calc
      J ≤ S*X := hle
      _ ≤ (76*q)*(8*q) := Nat.mul_le_mul hSbound hXbound
      _ = 608*(q*q) := by ac_rfl
  have hJsmall : J<P := by
    have hsqpos : 0<q*q := Nat.mul_pos (by omega : 0<q) (by omega : 0<q)
    have hm : 608*(q*q)<65536*(q*q) :=
      Nat.mul_lt_mul_of_pos_right (by decide) hsqpos
    have hlargeEq : 65536*(q*q)≤P := by simpa only [Nat.mul_assoc] using hlarge
    omega
  have hmassTail := upper_tail_mass (6*u2 q-2) (2*u2 q+5) 0 bp dp mp r hpre
  have hmass : bp+dp+2*r+32*q+21=56*P := by
    omega
  have hpow := inverseAt_power bp dp t k c hi
  have hcost := inverseAt_odd_cost bp dp t k c
    (by omega) hb4 hdp hi hc
  have hpostMass : (2*k-4)+12+c+3+32*q+12+2*r+2*t=56*P := by omega
  have hsource : X*Y*(c+3)+J=V*P := by
    apply scaled_root_mass_power_to_dyadic q r X Y P V J bp dp c
    · omega
    · exact hroot
    · exact hmass
    · simpa [Y] using hpow
    · exact hVdef
    · simpa [S] using hJdef
  have hpostExact := upper_tail_dyadic (2*k-4) (c+4) (mp+t+1) b d m n hpost
  have hwallReset : (2*k-4)+12=2^n*(4*(r+t+1+n)+64*q+28) := by
    have hpostm : m=mp+t+1+n := by omega
    calc
      (2*k-4)+12=2^n*(b+12) := hpostExact.1.symm
      _=2^n*(4*(r+t+1+n)+64*q+28) := by
        rw [hwall,hpostm,hmp]
  exact all_prefix_one_reset_obstruction q r t n X Y P V J c ((2*k-4)+12)
    hq ht rfl rfl rfl hXsmall hr (by simpa [S] using hJdef)
    hVdef hJpos hJsmall hsource hpostMass hwallReset

#print axioms l1_one_reset_cone_no_wall
end BB6.Agent50L1All
