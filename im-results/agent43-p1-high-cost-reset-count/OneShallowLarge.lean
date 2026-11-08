import DyadicGap
import CubicGap

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace BB6.Agent43TwoRun

private theorem pow8 (s : Nat) : (8:Nat)^s = 2^(3*s) := by
  simpa only [show (8:Nat) = 2^3 by decide] using (Nat.pow_mul 2 3 s).symm

/-- General cubic-gap obstruction for a middle shallow edge and two runs of
arbitrary depths two. The two possible shallow depths instantiate parameters. -/
theorem no_middle_large_generic
    (n s r p d A R K alpha beta kappa : Nat)
    (hn : 28≤n)
    (hP : 8^s*p=2^n)
    (hD : 8^s*d=14*n+92)
    (hRpos : 0<R)
    (hRsmall : 3*s≤n → R≤168*(n+2))
    (hRbound : 3*s≤n → R≤beta*(n+2))
    (hK : kappa≤K) (hkpos : 0<kappa)
    (hcoef : 21*alpha*beta≤8192*kappa)
    (hAbound : 3*(s+r)≤n → A+1≤alpha*(n+2))
    (heq : K*p=A*8^r+R) : False := by
  let q : Nat := 8^s
  have hqpos : 0<q := by dsimp [q]; exact Nat.pow_pos (by decide)
  have hqdvd : q ∣ 14*n+92 := ⟨d, by simpa [q] using hD.symm⟩
  have hqD : q≤14*n+92 := Nat.le_of_dvd (by omega) hqdvd
  have hqbound : q≤21*(n+2) := by omega
  have hnumeric := cubic_lt_pow n hn
  have hp3 : (n+2)^3=(n+2)*((n+2)^2) := by
    calc
      _ = (n+2)^2*(n+2) := Nat.pow_succ _ _
      _ = (n+2)*((n+2)^2) := Nat.mul_comm _ _
  have hx : n+2≤(n+2)^3 := by
    have hle : 1≤(n+2)^2 := Nat.one_le_pow 2 (n+2) (by omega)
    have hmul := Nat.mul_le_mul_left (n+2) hle
    calc
      n+2 = (n+2)*1 := by omega
      _ ≤ (n+2)*((n+2)^2) := hmul
      _ = (n+2)^3 := hp3.symm
  have hxscale := Nat.mul_le_mul_left 8192 hx
  have hqsmaller : q<2^n := by omega
  have h3s : 3*s≤n := by
    by_cases hh : 3*s≤n
    · exact hh
    · have hpowle : 2^n≤(2:Nat)^(3*s) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hqeq : q=2^(3*s) := pow8 s
      omega
  have hRle := hRsmall h3s
  have hRbeta := hRbound h3s
  have hqR : q*R≤(21*(n+2))*(168*(n+2)) :=
    Nat.mul_le_mul hqbound hRle
  have hquad : q*R≤3528*(n+2)^2 := by
    calc
      _ ≤ 21*(n+2)*(168*(n+2)) := hqR
      _ = 3528*(n+2)^2 := by
        rw [Nat.pow_two]
        calc
          21*(n+2)*(168*(n+2)) = (21*168)*((n+2)*(n+2)) := by ac_rfl
          _ = 3528*((n+2)*(n+2)) := by simp only [show 21*168=3528 by decide]
  have hcoefQuad : 3528≤8192*(n+2) := by omega
  have hquad2 := Nat.mul_le_mul_right ((n+2)^2) hcoefQuad
  have hquad3 : q*R≤8192*(n+2)^3 := by
    calc
      q*R ≤ 3528*(n+2)^2 := hquad
      _ ≤ 8192*(n+2)^3 := by
        calc
          _ ≤ (8192*(n+2))*((n+2)^2) := hquad2
          _ = 8192*(n+2)^3 := by rw [hp3]; ac_rfl
  have hsmallRmul : q*R<q*p := by rw [hP]; omega
  have hsmallR : R<p := Nat.lt_of_mul_lt_mul_left hsmallRmul
  have hpow : 2^n = 2^(3*s)*2^(n-3*s) := by
    rw [←Nat.pow_add]
    congr 1
    omega
  have hp : p=2^(n-3*s) := by
    have hqeq : q=2^(3*s) := pow8 s
    have hqpp : 2^(3*s)*p=2^(3*s)*2^(n-3*s) := by
      calc
        _ = q*p := by rw [hqeq]
        _ = 2^n := hP
        _ = 2^(3*s)*2^(n-3*s) := hpow
    exact Nat.mul_left_cancel (Nat.pow_pos (by decide)) hqpp
  have hRsmallPow : R<2^(n-3*s) := by simpa [hp] using hsmallR
  obtain ⟨h3r, hpowR⟩ :=
    dyadic_remainder (n-3*s) r A K R hRpos hRsmallPow
      (by simpa [hp] using heq)
  have htotal : 3*(s+r)≤n := by omega
  have hAb := hAbound htotal
  have hmul := Nat.mul_le_mul_left A hpowR
  have hKP : K*p≤(A+1)*R := by
    have hx : (A+1)*R=A*R+R := by simp [Nat.add_mul]
    omega
  have hkP : kappa*p≤(A+1)*R := by
    have hh := Nat.mul_le_mul_right p hK
    omega
  have hqKP : q*(kappa*p)≤q*((A+1)*R) :=
    Nat.mul_le_mul_left q hkP
  have hAprod := Nat.mul_le_mul hAb hRbeta
  have hqprod := Nat.mul_le_mul hqbound hAprod
  have hlimit : kappa*2^n ≤(21*alpha*beta)*(n+2)^3 := by
    calc
      kappa*2^n = q*(kappa*p) := by rw [←hP]; ac_rfl
      _ ≤ q*((A+1)*R) := hqKP
      _ ≤ (21*(n+2))*(alpha*(n+2)*(beta*(n+2))) := hqprod
      _ = (21*alpha*beta)*(n+2)^3 := by rw [hp3, Nat.pow_two]; ac_rfl
  have hcoefmul := Nat.mul_le_mul_right ((n+2)^3) hcoef
  have hlimit2 : kappa*2^n≤(8192*kappa)*(n+2)^3 := by omega
  have hgap := (Nat.mul_lt_mul_left hkpos).mpr hnumeric
  have hgap' : (8192*kappa)*(n+2)^3 <kappa*2^n := by
    calc
      _ = kappa*(8192*(n+2)^3) := by ac_rfl
      _ < kappa*2^n := hgap
  omega

/-- A 0 shallow edge between two arbitrary depth-two runs cannot reach
 the wall in the large-parameter regime. This is arithmetic, not source-lifted. -/
theorem no_zero_middle_large
    (n s r p d : Nat) (hn : 28≤n)
    (hP : 8^s*p=2^n) (hD : 8^s*d=14*n+92)
    (heq : (588*8^s-98)*p =
      (224*n+672*s+672*r+800)*8^r +
      (84*n+252*s+272-d)) : False := by
  let R := 84*n+252*s+272-d
  let A := 224*n+672*s+672*r+800
  have hqpos : 1≤8^s := Nat.one_le_pow s 8 (by decide)
  have hd : d≤14*n+92 := by
    have hqmul := Nat.mul_le_mul_right d hqpos
    omega
  have hRpos : 0<R := by dsimp [R]; omega
  have hRbound : 3*s≤n → R≤168*(n+2) := by
    intro hs
    dsimp [R]
    omega
  have hA: 3*(s+r)≤n → A+1≤448*(n+2) := by intro h; dsimp [A]; omega
  exact no_middle_large_generic n s r p d A R (588*8^s-98)
    448 168 490 hn hP hD hRpos hRbound hRbound
    (by omega) (by decide) (by decide) hA (by simpa [A,R] using heq)

/-- A 1 shallow edge between two arbitrary depth-two runs cannot reach
 the wall in the large-parameter regime. This is arithmetic, not source-lifted. -/
theorem no_one_middle_large
    (n s r p d : Nat) (hn : 28≤n)
    (hP : 8^s*p=2^n) (hD : 8^s*d=14*n+92)
    (heq : (392*8^s-98)*p =
      (448*n+1344*s+1344*r+2048)*8^r +
      (56*n+168*s+200-d)) : False := by
  let R := 56*n+168*s+200-d
  let A := 448*n+1344*s+1344*r+2048
  have hqpos : 1≤8^s := Nat.one_le_pow s 8 (by decide)
  have hd : d≤14*n+92 := by
    have hqmul := Nat.mul_le_mul_right d hqpos
    omega
  have hRpos : 0<R := by dsimp [R]; omega
  have hRbound : 3*s≤n → R≤112*(n+2) := by
    intro hs
    dsimp [R]
    omega
  have hRsmall : 3*s≤n → R≤168*(n+2) := by
    intro hs
    dsimp [R]
    omega
  have hA: 3*(s+r)≤n → A+1≤1024*(n+2) := by intro h; dsimp [A]; omega
  exact no_middle_large_generic n s r p d A R (392*8^s-98)
    1024 112 294 hn hP hD hRpos hRsmall hRbound
    (by omega) (by decide) (by decide) hA (by simpa [A,R] using heq)

#print axioms BB6.Agent43TwoRun.no_zero_middle_large
#print axioms BB6.Agent43TwoRun.no_one_middle_large
end BB6.Agent43TwoRun