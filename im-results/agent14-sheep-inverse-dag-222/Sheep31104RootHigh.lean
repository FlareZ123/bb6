import SheepOddGap
set_option maxHeartbeats 0
namespace Sheep31104RootHigh

/-- Uniform gap used for all seven hidden h alternatives. -/
private theorem high_bound (a : Nat) (ha : 15≤a) :
    1458*a+128 < 2^a := by
  obtain ⟨t,rfl⟩ : ∃t,a=15+t := ⟨a-15,by omega⟩
  induction t with
  | zero => decide
  | succ t ih =>
    have hpow : (2:Nat)^15 ≤ 2^(15+t) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hlarge : 1458 ≤ 2^(15+t) := by omega
    have he : 15+(t+1)=(15+t)+1 := by omega
    rw [he,Nat.pow_succ]
    omega

/-- h=0: no large 2-adic predecessor. -/
theorem no_h0 (k a v : Nat) (ha : 15≤a)
    (hs : 3^0*(2^(a+1)+1)*v+2*a*3^0+2^(0+1)=2^((31104+122472*k)+0+1)+3*3^0) : False := by
  have hsource : 1*((2:Nat)^(a+1)+1)*v+2*a*1+2 =
      2^((31104+122472*k)+0+1)+3 := by
    simpa only [show (3:Nat)^0=1 by decide, show (2:Nat)^(0+1)=2 by decide] using hs
  have hEqNat : 2^((31104+122472*k)+0+1)+1 =
      1*((2:Nat)^(a+1)+1)*v+2*a*1 := by omega
  have ht := congrArg (fun z:Nat => (z:Int)) hEqNat
  have hEqInt : (2:Int)^((31104+122472*k)+0+1) =
       ((2:Int)^(a+1)+1)*(1*(v:Int))+(2*(a:Int)-1) := by
    simp only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
      show ((2:Nat):Int)=(2:Int) by decide,
      show ((1:Nat):Int)=(1:Int) by decide,
      show ((1:Nat):Int)=(1:Int) by decide,
      show ((1:Nat):Int)=(1:Int) by decide] at ht
    have hfactor : 1*((2:Int)^(a+1)+1)*(v:Int) =
        ((2:Int)^(a+1)+1)*(1*(v:Int)) := by ac_rfl
    rw [hfactor] at ht
    omega
  have hdiv : ((2:Int)^(a+1)+1) ∣
      (2:Int)^((31104+122472*k)+0+1)-(2*(a:Int)-1) := by
    refine ⟨1*(v:Int),?_⟩
    omega
  have hK : 1 < 2*(a:Int)-1 := by omega
  have hodd : (2*(a:Int)-1)%2=1 := by omega
  have hhigh : 2*(a:Int)-1 < (2:Int)^a := by
    have hb := high_bound a ha
    have hbc : ((1458*a+128:Nat):Int) < ((2:Nat)^a:Int) :=
      Int.ofNat_lt.mpr hb
    have hp : (1458*(a:Int)+128) < (2:Int)^a := by
      simpa only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
       show ((2:Nat):Int)=(2:Int) by decide,
       show ((1458:Nat):Int)=(1458:Int) by decide,
       show ((128:Nat):Int)=(128:Int) by decide] using hbc
    omega
  exact (SheepOddGap.no_power_signed_small_odd a
     (2*(a:Int)-1) hK hodd hhigh ((31104+122472*k)+0+1)).1 hdiv

#print axioms no_h0

/-- h=1: no large 2-adic predecessor. -/
theorem no_h1 (k a v : Nat) (ha : 15≤a)
    (hs : 3^1*(2^(a+1)+1)*v+2*a*3^1+2^(1+1)=2^((31104+122472*k)+1+1)+3*3^1) : False := by
  have hsource : 3*((2:Nat)^(a+1)+1)*v+2*a*3+4 =
      2^((31104+122472*k)+1+1)+9 := by
    simpa only [show (3:Nat)^1=3 by decide, show (2:Nat)^(1+1)=4 by decide] using hs
  have hEqNat : 2^((31104+122472*k)+1+1)+5 =
      3*((2:Nat)^(a+1)+1)*v+2*a*3 := by omega
  have ht := congrArg (fun z:Nat => (z:Int)) hEqNat
  have hEqInt : (2:Int)^((31104+122472*k)+1+1) =
       ((2:Int)^(a+1)+1)*(3*(v:Int))+(6*(a:Int)-5) := by
    simp only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
      show ((2:Nat):Int)=(2:Int) by decide,
      show ((1:Nat):Int)=(1:Int) by decide,
      show ((3:Nat):Int)=(3:Int) by decide,
      show ((5:Nat):Int)=(5:Int) by decide] at ht
    have hfactor : 3*((2:Int)^(a+1)+1)*(v:Int) =
        ((2:Int)^(a+1)+1)*(3*(v:Int)) := by ac_rfl
    rw [hfactor] at ht
    omega
  have hdiv : ((2:Int)^(a+1)+1) ∣
      (2:Int)^((31104+122472*k)+1+1)-(6*(a:Int)-5) := by
    refine ⟨3*(v:Int),?_⟩
    omega
  have hK : 1 < 6*(a:Int)-5 := by omega
  have hodd : (6*(a:Int)-5)%2=1 := by omega
  have hhigh : 6*(a:Int)-5 < (2:Int)^a := by
    have hb := high_bound a ha
    have hbc : ((1458*a+128:Nat):Int) < ((2:Nat)^a:Int) :=
      Int.ofNat_lt.mpr hb
    have hp : (1458*(a:Int)+128) < (2:Int)^a := by
      simpa only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
       show ((2:Nat):Int)=(2:Int) by decide,
       show ((1458:Nat):Int)=(1458:Int) by decide,
       show ((128:Nat):Int)=(128:Int) by decide] using hbc
    omega
  exact (SheepOddGap.no_power_signed_small_odd a
     (6*(a:Int)-5) hK hodd hhigh ((31104+122472*k)+1+1)).1 hdiv

#print axioms no_h1

/-- h=2: no large 2-adic predecessor. -/
theorem no_h2 (k a v : Nat) (ha : 15≤a)
    (hs : 3^2*(2^(a+1)+1)*v+2*a*3^2+2^(2+1)=2^((31104+122472*k)+2+1)+3*3^2) : False := by
  have hsource : 9*((2:Nat)^(a+1)+1)*v+2*a*9+8 =
      2^((31104+122472*k)+2+1)+27 := by
    simpa only [show (3:Nat)^2=9 by decide, show (2:Nat)^(2+1)=8 by decide] using hs
  have hEqNat : 2^((31104+122472*k)+2+1)+19 =
      9*((2:Nat)^(a+1)+1)*v+2*a*9 := by omega
  have ht := congrArg (fun z:Nat => (z:Int)) hEqNat
  have hEqInt : (2:Int)^((31104+122472*k)+2+1) =
       ((2:Int)^(a+1)+1)*(9*(v:Int))+(18*(a:Int)-19) := by
    simp only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
      show ((2:Nat):Int)=(2:Int) by decide,
      show ((1:Nat):Int)=(1:Int) by decide,
      show ((9:Nat):Int)=(9:Int) by decide,
      show ((19:Nat):Int)=(19:Int) by decide] at ht
    have hfactor : 9*((2:Int)^(a+1)+1)*(v:Int) =
        ((2:Int)^(a+1)+1)*(9*(v:Int)) := by ac_rfl
    rw [hfactor] at ht
    omega
  have hdiv : ((2:Int)^(a+1)+1) ∣
      (2:Int)^((31104+122472*k)+2+1)-(18*(a:Int)-19) := by
    refine ⟨9*(v:Int),?_⟩
    omega
  have hK : 1 < 18*(a:Int)-19 := by omega
  have hodd : (18*(a:Int)-19)%2=1 := by omega
  have hhigh : 18*(a:Int)-19 < (2:Int)^a := by
    have hb := high_bound a ha
    have hbc : ((1458*a+128:Nat):Int) < ((2:Nat)^a:Int) :=
      Int.ofNat_lt.mpr hb
    have hp : (1458*(a:Int)+128) < (2:Int)^a := by
      simpa only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
       show ((2:Nat):Int)=(2:Int) by decide,
       show ((1458:Nat):Int)=(1458:Int) by decide,
       show ((128:Nat):Int)=(128:Int) by decide] using hbc
    omega
  exact (SheepOddGap.no_power_signed_small_odd a
     (18*(a:Int)-19) hK hodd hhigh ((31104+122472*k)+2+1)).1 hdiv

#print axioms no_h2

/-- h=3: no large 2-adic predecessor. -/
theorem no_h3 (k a v : Nat) (ha : 15≤a)
    (hs : 3^3*(2^(a+1)+1)*v+2*a*3^3+2^(3+1)=2^((31104+122472*k)+3+1)+3*3^3) : False := by
  have hsource : 27*((2:Nat)^(a+1)+1)*v+2*a*27+16 =
      2^((31104+122472*k)+3+1)+81 := by
    simpa only [show (3:Nat)^3=27 by decide, show (2:Nat)^(3+1)=16 by decide] using hs
  have hEqNat : 2^((31104+122472*k)+3+1)+65 =
      27*((2:Nat)^(a+1)+1)*v+2*a*27 := by omega
  have ht := congrArg (fun z:Nat => (z:Int)) hEqNat
  have hEqInt : (2:Int)^((31104+122472*k)+3+1) =
       ((2:Int)^(a+1)+1)*(27*(v:Int))+(54*(a:Int)-65) := by
    simp only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
      show ((2:Nat):Int)=(2:Int) by decide,
      show ((1:Nat):Int)=(1:Int) by decide,
      show ((27:Nat):Int)=(27:Int) by decide,
      show ((65:Nat):Int)=(65:Int) by decide] at ht
    have hfactor : 27*((2:Int)^(a+1)+1)*(v:Int) =
        ((2:Int)^(a+1)+1)*(27*(v:Int)) := by ac_rfl
    rw [hfactor] at ht
    omega
  have hdiv : ((2:Int)^(a+1)+1) ∣
      (2:Int)^((31104+122472*k)+3+1)-(54*(a:Int)-65) := by
    refine ⟨27*(v:Int),?_⟩
    omega
  have hK : 1 < 54*(a:Int)-65 := by omega
  have hodd : (54*(a:Int)-65)%2=1 := by omega
  have hhigh : 54*(a:Int)-65 < (2:Int)^a := by
    have hb := high_bound a ha
    have hbc : ((1458*a+128:Nat):Int) < ((2:Nat)^a:Int) :=
      Int.ofNat_lt.mpr hb
    have hp : (1458*(a:Int)+128) < (2:Int)^a := by
      simpa only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
       show ((2:Nat):Int)=(2:Int) by decide,
       show ((1458:Nat):Int)=(1458:Int) by decide,
       show ((128:Nat):Int)=(128:Int) by decide] using hbc
    omega
  exact (SheepOddGap.no_power_signed_small_odd a
     (54*(a:Int)-65) hK hodd hhigh ((31104+122472*k)+3+1)).1 hdiv

#print axioms no_h3

/-- h=4: no large 2-adic predecessor. -/
theorem no_h4 (k a v : Nat) (ha : 15≤a)
    (hs : 3^4*(2^(a+1)+1)*v+2*a*3^4+2^(4+1)=2^((31104+122472*k)+4+1)+3*3^4) : False := by
  have hsource : 81*((2:Nat)^(a+1)+1)*v+2*a*81+32 =
      2^((31104+122472*k)+4+1)+243 := by
    simpa only [show (3:Nat)^4=81 by decide, show (2:Nat)^(4+1)=32 by decide] using hs
  have hEqNat : 2^((31104+122472*k)+4+1)+211 =
      81*((2:Nat)^(a+1)+1)*v+2*a*81 := by omega
  have ht := congrArg (fun z:Nat => (z:Int)) hEqNat
  have hEqInt : (2:Int)^((31104+122472*k)+4+1) =
       ((2:Int)^(a+1)+1)*(81*(v:Int))+(162*(a:Int)-211) := by
    simp only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
      show ((2:Nat):Int)=(2:Int) by decide,
      show ((1:Nat):Int)=(1:Int) by decide,
      show ((81:Nat):Int)=(81:Int) by decide,
      show ((211:Nat):Int)=(211:Int) by decide] at ht
    have hfactor : 81*((2:Int)^(a+1)+1)*(v:Int) =
        ((2:Int)^(a+1)+1)*(81*(v:Int)) := by ac_rfl
    rw [hfactor] at ht
    omega
  have hdiv : ((2:Int)^(a+1)+1) ∣
      (2:Int)^((31104+122472*k)+4+1)-(162*(a:Int)-211) := by
    refine ⟨81*(v:Int),?_⟩
    omega
  have hK : 1 < 162*(a:Int)-211 := by omega
  have hodd : (162*(a:Int)-211)%2=1 := by omega
  have hhigh : 162*(a:Int)-211 < (2:Int)^a := by
    have hb := high_bound a ha
    have hbc : ((1458*a+128:Nat):Int) < ((2:Nat)^a:Int) :=
      Int.ofNat_lt.mpr hb
    have hp : (1458*(a:Int)+128) < (2:Int)^a := by
      simpa only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
       show ((2:Nat):Int)=(2:Int) by decide,
       show ((1458:Nat):Int)=(1458:Int) by decide,
       show ((128:Nat):Int)=(128:Int) by decide] using hbc
    omega
  exact (SheepOddGap.no_power_signed_small_odd a
     (162*(a:Int)-211) hK hodd hhigh ((31104+122472*k)+4+1)).1 hdiv

#print axioms no_h4

/-- h=5: no large 2-adic predecessor. -/
theorem no_h5 (k a v : Nat) (ha : 15≤a)
    (hs : 3^5*(2^(a+1)+1)*v+2*a*3^5+2^(5+1)=2^((31104+122472*k)+5+1)+3*3^5) : False := by
  have hsource : 243*((2:Nat)^(a+1)+1)*v+2*a*243+64 =
      2^((31104+122472*k)+5+1)+729 := by
    simpa only [show (3:Nat)^5=243 by decide, show (2:Nat)^(5+1)=64 by decide] using hs
  have hEqNat : 2^((31104+122472*k)+5+1)+665 =
      243*((2:Nat)^(a+1)+1)*v+2*a*243 := by omega
  have ht := congrArg (fun z:Nat => (z:Int)) hEqNat
  have hEqInt : (2:Int)^((31104+122472*k)+5+1) =
       ((2:Int)^(a+1)+1)*(243*(v:Int))+(486*(a:Int)-665) := by
    simp only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
      show ((2:Nat):Int)=(2:Int) by decide,
      show ((1:Nat):Int)=(1:Int) by decide,
      show ((243:Nat):Int)=(243:Int) by decide,
      show ((665:Nat):Int)=(665:Int) by decide] at ht
    have hfactor : 243*((2:Int)^(a+1)+1)*(v:Int) =
        ((2:Int)^(a+1)+1)*(243*(v:Int)) := by ac_rfl
    rw [hfactor] at ht
    omega
  have hdiv : ((2:Int)^(a+1)+1) ∣
      (2:Int)^((31104+122472*k)+5+1)-(486*(a:Int)-665) := by
    refine ⟨243*(v:Int),?_⟩
    omega
  have hK : 1 < 486*(a:Int)-665 := by omega
  have hodd : (486*(a:Int)-665)%2=1 := by omega
  have hhigh : 486*(a:Int)-665 < (2:Int)^a := by
    have hb := high_bound a ha
    have hbc : ((1458*a+128:Nat):Int) < ((2:Nat)^a:Int) :=
      Int.ofNat_lt.mpr hb
    have hp : (1458*(a:Int)+128) < (2:Int)^a := by
      simpa only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
       show ((2:Nat):Int)=(2:Int) by decide,
       show ((1458:Nat):Int)=(1458:Int) by decide,
       show ((128:Nat):Int)=(128:Int) by decide] using hbc
    omega
  exact (SheepOddGap.no_power_signed_small_odd a
     (486*(a:Int)-665) hK hodd hhigh ((31104+122472*k)+5+1)).1 hdiv

#print axioms no_h5

/-- h=6: no large 2-adic predecessor. -/
theorem no_h6 (k a v : Nat) (ha : 15≤a)
    (hs : 3^6*(2^(a+1)+1)*v+2*a*3^6+2^(6+1)=2^((31104+122472*k)+6+1)+3*3^6) : False := by
  have hsource : 729*((2:Nat)^(a+1)+1)*v+2*a*729+128 =
      2^((31104+122472*k)+6+1)+2187 := by
    simpa only [show (3:Nat)^6=729 by decide, show (2:Nat)^(6+1)=128 by decide] using hs
  have hEqNat : 2^((31104+122472*k)+6+1)+2059 =
      729*((2:Nat)^(a+1)+1)*v+2*a*729 := by omega
  have ht := congrArg (fun z:Nat => (z:Int)) hEqNat
  have hEqInt : (2:Int)^((31104+122472*k)+6+1) =
       ((2:Int)^(a+1)+1)*(729*(v:Int))+(1458*(a:Int)-2059) := by
    simp only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
      show ((2:Nat):Int)=(2:Int) by decide,
      show ((1:Nat):Int)=(1:Int) by decide,
      show ((729:Nat):Int)=(729:Int) by decide,
      show ((2059:Nat):Int)=(2059:Int) by decide] at ht
    have hfactor : 729*((2:Int)^(a+1)+1)*(v:Int) =
        ((2:Int)^(a+1)+1)*(729*(v:Int)) := by ac_rfl
    rw [hfactor] at ht
    omega
  have hdiv : ((2:Int)^(a+1)+1) ∣
      (2:Int)^((31104+122472*k)+6+1)-(1458*(a:Int)-2059) := by
    refine ⟨729*(v:Int),?_⟩
    omega
  have hK : 1 < 1458*(a:Int)-2059 := by omega
  have hodd : (1458*(a:Int)-2059)%2=1 := by omega
  have hhigh : 1458*(a:Int)-2059 < (2:Int)^a := by
    have hb := high_bound a ha
    have hbc : ((1458*a+128:Nat):Int) < ((2:Nat)^a:Int) :=
      Int.ofNat_lt.mpr hb
    have hp : (1458*(a:Int)+128) < (2:Int)^a := by
      simpa only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
       show ((2:Nat):Int)=(2:Int) by decide,
       show ((1458:Nat):Int)=(1458:Int) by decide,
       show ((128:Nat):Int)=(128:Int) by decide] using hbc
    omega
  exact (SheepOddGap.no_power_signed_small_odd a
     (1458*(a:Int)-2059) hK hodd hhigh ((31104+122472*k)+6+1)).1 hdiv

#print axioms no_h6

theorem no_high (k a h v : Nat) (ha : 15≤a) (hh : h<7)
  (hs : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)=
      2^((31104+122472*k)+h+1)+3*3^h) : False := by
  have hc : h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h
    exact no_h0 k a v ha hs
  · subst h
    exact no_h1 k a v ha hs
  · subst h
    exact no_h2 k a v ha hs
  · subst h
    exact no_h3 k a v ha hs
  · subst h
    exact no_h4 k a v ha hs
  · subst h
    exact no_h5 k a v ha hs
  · subst h
    exact no_h6 k a v ha hs

#print axioms no_high
end Sheep31104RootHigh
