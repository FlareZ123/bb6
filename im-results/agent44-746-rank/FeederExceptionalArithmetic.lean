import FeederExceptionalStep
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

namespace CascadeFeederExceptional
open CascadeFeederSix

/-- 2 has order 486 modulo 729; this is the period needed by the
    two exceptional 1458-adic feeder families below. -/
theorem pow_period486_729 (m : Nat) :
    (2:Nat)^(m+486)%729=(2:Nat)^m%729 := by
  calc
    (2:Nat)^(m+486)%729
        = ((2:Nat)^m * (2:Nat)^486)%729 := by rw [Nat.pow_add]
    _ = ((2:Nat)^m%729)*((2:Nat)^486%729)%729 := by rw [Nat.mul_mod]
    _ = (2:Nat)^m%729 := by
      have h : (2:Nat)^486%729=1 := by decide
      rw [h]
      simp

theorem pow_period1458_729 (m : Nat) :
    (2:Nat)^(m+1458)%729=(2:Nat)^m%729 := by
  calc
    (2:Nat)^(m+1458)%729 = (2:Nat)^(m+972)%729 := by
      have h := pow_period486_729 (m+972)
      simpa [Nat.add_assoc] using h
    _ = (2:Nat)^(m+486)%729 := by
      have h := pow_period486_729 (m+486)
      simpa [Nat.add_assoc] using h
    _ = (2:Nat)^m%729 := pow_period486_729 m

private theorem pow_period1458_many (m t : Nat) :
    (2:Nat)^(m+1458*t)%729=(2:Nat)^m%729 := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hs : m+1458*(t+1)=(m+1458*t)+1458 := by omega
      rw [hs]
      exact (pow_period1458_729 (m+1458*t)).trans ih

theorem exceptional_numeric (n p : Nat)
    (hp : p=2^(n-2))
    (hr : n%1458=1085 ∨ n%1458=1372) :
    (n%729=356 ∧ p%729=332) ∨
      (n%729=643 ∧ p%729=112) := by
  rcases hr with hr | hr
  · have hn : n%729=356 := by omega
    have hexp : n-2=1083+1458*(n/1458) := by omega
    have hpm : p%729=332 := by
      rw [hp,hexp]
      rw [pow_period1458_many 1083 (n/1458)]
    exact Or.inl ⟨hn,hpm⟩
  · have hn : n%729=643 := by omega
    have hexp : n-2=1370+1458*(n/1458) := by omega
    have hpm : p%729=112 := by
      rw [hp,hexp]
      rw [pow_period1458_many 1370 (n/1458)]
    exact Or.inr ⟨hn,hpm⟩

theorem mod_x (n p x : Nat)
    (h : 9*x+17*n+39=56*p)
    (hnp : (n%729=356 ∧ p%729=332) ∨
      (n%729=643 ∧ p%729=112)) :
    x%3≠2 := by
  rcases hnp with ⟨hn,hp⟩ | ⟨hn,hp⟩ <;> omega

theorem mod_h (n p h : Nat)
    (ha : 9*h+43*n+60=40*p)
    (hnp : (n%729=356 ∧ p%729=332) ∨
      (n%729=643 ∧ p%729=112)) :
    h%3=2 ∧ (2*h+5)%27=0 ∧ (2*h+5)%81=27 := by
  rcases hnp with ⟨hn,hp⟩ | ⟨hn,hp⟩ <;> omega

theorem mod_a (n p a : Nat)
    (ha : 81*a+425*n+381=158*p)
    (hnp : (n%729=356 ∧ p%729=332) ∨
      (n%729=643 ∧ p%729=112)) :
    a%3=2 ∧ (2*a+5)%9=3 := by
  rcases hnp with ⟨hn,hp⟩ | ⟨hn,hp⟩ <;> omega

theorem mod_b (n p b : Nat)
    (hb : 81*b+931*n+438=154*p)
    (hnp : (n%729=356 ∧ p%729=332) ∨
      (n%729=643 ∧ p%729=112)) :
    b%3=2 ∧ (2*b+5)%9=3 := by
  rcases hnp with ⟨hn,hp⟩ | ⟨hn,hp⟩ <;> omega

theorem mod_c (n p c : Nat)
    (hc : 81*c+1943*n+552=146*p)
    (hnp : (n%729=356 ∧ p%729=332) ∨
      (n%729=643 ∧ p%729=112)) :
    c%3=2 ∧ (2*c+5)%9=3 := by
  rcases hnp with ⟨hn,hp⟩ | ⟨hn,hp⟩ <;> omega

theorem mod_d (n p d : Nat)
    (hd : 81*d+3967*n+780=130*p)
    (hnp : (n%729=356 ∧ p%729=332) ∨
      (n%729=643 ∧ p%729=112)) :
    d%3=2 ∧ (2*d+5)%9=3 := by
  rcases hnp with ⟨hn,hp⟩ | ⟨hn,hp⟩ <;> omega

theorem mod_e (n p e : Nat)
    (he : 81*e+8015*n+1236=98*p)
    (hnp : (n%729=356 ∧ p%729=332) ∨
      (n%729=643 ∧ p%729=112)) :
    e%3=2 ∧ (2*e+5)%9=3 := by
  rcases hnp with ⟨hn,hp⟩ | ⟨hn,hp⟩ <;> omega

theorem mod_f (n p f : Nat)
    (hf : 243*f+32303*n+4134=149*p)
    (hnp : (n%729=356 ∧ p%729=332) ∨
      (n%729=643 ∧ p%729=112)) :
    f%3≠2 := by
  rcases hnp with ⟨hn,hp⟩ | ⟨hn,hp⟩ <;> omega

theorem affine_f (n p e q f : Nat)
    (he : 81*e+8015*n+1236=98*p)
    (hq : 3*q=2*e+5)
    (hf : 2*q=p+f+n) :
    243*f+32303*n+4134=149*p := by
  omega

theorem q_a_gap (n p a q : Nat)
    (ha : 81*a+425*n+381=158*p)
    (hq : 3*q=2*a+5)
    (hbig : 10000*n+10000≤p) :
    p<q ∧ 2*q<3*p := by
  have hlin : 243*q+850*n+357=316*p := by omega
  have hbig73 : 73*(10000*n+10000)≤73*p := Nat.mul_le_mul_left 73 hbig
  have hsmall : 850*n+357 < 73*(10000*n+10000) := by omega
  have hineq : 850*n+357 <73*p := by omega
  have hscaled1 : 243*p<243*q := by omega
  have hpq : p<q := Nat.lt_of_mul_lt_mul_left hscaled1
  have hlin2 : 486*q+1700*n+714=632*p := by omega
  have hpos : 0<p := by omega
  have hlt : 632*p<729*p :=
    Nat.mul_lt_mul_of_pos_right (by decide : 632<729) hpos
  have hscaled2 : 243*(2*q)<243*(3*p) := by omega
  have htwice : 2*q<3*p := Nat.lt_of_mul_lt_mul_left hscaled2
  exact ⟨hpq,htwice⟩

theorem q_b_gap (n p b q : Nat)
    (hb : 81*b+931*n+438=154*p)
    (hq : 3*q=2*b+5)
    (hbig : 10000*n+10000≤p) :
    p<q ∧ 2*q<3*p := by
  have hlin : 243*q+1862*n+471=308*p := by omega
  have hbig73 : 73*(10000*n+10000)≤73*p := Nat.mul_le_mul_left 73 hbig
  have hsmall : 1862*n+471 < 73*(10000*n+10000) := by omega
  have hineq : 1862*n+471 <73*p := by omega
  have hscaled1 : 243*p<243*q := by omega
  have hpq : p<q := Nat.lt_of_mul_lt_mul_left hscaled1
  have hlin2 : 486*q+3724*n+942=616*p := by omega
  have hpos : 0<p := by omega
  have hlt : 616*p<729*p :=
    Nat.mul_lt_mul_of_pos_right (by decide : 616<729) hpos
  have hscaled2 : 243*(2*q)<243*(3*p) := by omega
  have htwice : 2*q<3*p := Nat.lt_of_mul_lt_mul_left hscaled2
  exact ⟨hpq,htwice⟩

theorem q_c_gap (n p c q : Nat)
    (hc : 81*c+1943*n+552=146*p)
    (hq : 3*q=2*c+5)
    (hbig : 10000*n+10000≤p) :
    p<q ∧ 2*q<3*p := by
  have hlin : 243*q+3886*n+699=292*p := by omega
  have hbig73 : 73*(10000*n+10000)≤73*p := Nat.mul_le_mul_left 73 hbig
  have hsmall : 3886*n+699 < 73*(10000*n+10000) := by omega
  have hineq : 3886*n+699 <73*p := by omega
  have hscaled1 : 243*p<243*q := by omega
  have hpq : p<q := Nat.lt_of_mul_lt_mul_left hscaled1
  have hlin2 : 486*q+7772*n+1398=584*p := by omega
  have hpos : 0<p := by omega
  have hlt : 584*p<729*p :=
    Nat.mul_lt_mul_of_pos_right (by decide : 584<729) hpos
  have hscaled2 : 243*(2*q)<243*(3*p) := by omega
  have htwice : 2*q<3*p := Nat.lt_of_mul_lt_mul_left hscaled2
  exact ⟨hpq,htwice⟩

theorem q_d_gap (n p d q : Nat)
    (hd : 81*d+3967*n+780=130*p)
    (hq : 3*q=2*d+5)
    (hbig : 10000*n+10000≤p) :
    p<q ∧ 2*q<3*p := by
  have hlin : 243*q+7934*n+1155=260*p := by omega
  have hbig73 : 73*(10000*n+10000)≤73*p := Nat.mul_le_mul_left 73 hbig
  have hsmall : 7934*n+1155 < 73*(10000*n+10000) := by omega
  have hineq : 7934*n+1155 <73*p := by omega
  have hscaled1 : 243*p<243*q := by omega
  have hpq : p<q := Nat.lt_of_mul_lt_mul_left hscaled1
  have hlin2 : 486*q+15868*n+2310=520*p := by omega
  have hpos : 0<p := by omega
  have hlt : 520*p<729*p :=
    Nat.mul_lt_mul_of_pos_right (by decide : 520<729) hpos
  have hscaled2 : 243*(2*q)<243*(3*p) := by omega
  have htwice : 2*q<3*p := Nat.lt_of_mul_lt_mul_left hscaled2
  exact ⟨hpq,htwice⟩

theorem q_e_band (n p e q : Nat)
    (he : 81*e+8015*n+1236=98*p)
    (hq : 3*q=2*e+5)
    (hbig : 10000*n+10000≤p) :
    3*p<4*q ∧ q<p := by
  have hlin : 243*q+16030*n+2067=196*p := by omega
  have hbig55 : 55*(10000*n+10000)≤55*p := Nat.mul_le_mul_left 55 hbig
  have hsmall : 64120*n+8268 < 55*(10000*n+10000) := by omega
  have hineq : 64120*n+8268 <55*p := by omega
  have hscaled1 : 729*p<972*q := by omega
  have hscaled1' : 243*(3*p)<243*(4*q) := by omega
  have h3p : 3*p<4*q := Nat.lt_of_mul_lt_mul_left hscaled1'
  have hscaled2 : 243*q<243*p := by omega
  have hqp : q<p := Nat.lt_of_mul_lt_mul_left hscaled2
  exact ⟨h3p,hqp⟩

theorem geom_f (n p j f : Nat)
    (hpj : p=8*2^j)
    (hf : 243*f+32303*n+4134=149*p)
    (hbig : 10000*n+10000≤p) :
    4*2^j-3<f ∧ f<6*2^j-1 := by
  have hB : 1250*n+1250≤2^j := by rw [hpj] at hbig; omega
  have hf' : 243*f+32303*n+4134=1192*2^j := by rw [hpj] at hf; omega
  have hcoeff : 32303*n+4134≤220*2^j+486 := by omega
  have hlow : 4*2^j-3<f := by omega
  have hhigh : f<6*2^j-1 := by omega
  exact ⟨hlow,hhigh⟩

end CascadeFeederExceptional
