import Std
set_option maxHeartbeats 0
namespace CascadeSeam

private theorem quad_double (m : Nat) (hm : 20 ≤ m) :
    8*m+12 ≤ 2*m*(2*m+4) := by
  have hs : m ≤ m*m := by
    have h : (1:Nat) ≤ m := by omega
    simpa using (Nat.mul_le_mul_right m h)
  calc
    8*m+12 ≤ 12*m := by omega
    _ ≤ 4*(m*m)+8*m := by omega
    _ = 2*m*(2*m+4) := by simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem growth_aux (c start a : Nat)
    (hbase : c*2^start > 2*20*(2*20+4)) :
    c*2^(a+start) > 2*(a+20)*(2*(a+20)+4) := by
  induction a with
  | zero => simpa using hbase
  | succ a ih =>
    let m := a+20
    have hm : 20 ≤ m := by dsimp [m]; omega
    have hd := quad_double m hm
    have hstep : 2*(m+1)*(2*(m+1)+4) =
        2*m*(2*m+4)+8*m+12 := by simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]; omega
    have hpow : 2^(a+1+start) = 2*2^(a+start) := by
      rw [show a+1+start=(a+start)+1 by omega, Nat.pow_succ]
      omega
    change c*2^(a+start)>2*m*(2*m+4) at ih
    rw [hpow]
    change 2*(m+1)*(2*(m+1)+4) < c*(2*2^(a+start))
    rw [hstep]
    have hmul : c*(2*2^(a+start)) = 2*(c*2^(a+start)) := by ac_rfl
    rw [hmul]
    omega

private theorem center17_growth (n : Nat) (hn : 20 ≤ n) :
    2*n*(2*n+4) < 17*2^(n-13) := by
  let a := n-20
  have hn' : n=a+20 := by dsimp [a]; omega
  have h := growth_aux 17 7 a (by decide)
  rw [hn']
  simpa [a, show (a+20)-13=a+7 by omega] using h

private theorem center49_growth (n : Nat) (hn : 20 ≤ n) :
    2*n*(2*n+4) < 49*2^(n-12) := by
  let a := n-20
  have hn' : n=a+20 := by dsimp [a]; omega
  have h := growth_aux 49 8 a (by decide)
  rw [hn']
  simpa [a, show (a+20)-12=a+8 by omega] using h

private theorem no_close_to_power (n j m c e:Nat)
  (hcenter : 2*n*(2*n+4) < c*2^m)
  (hc : c < 2*(2*n+3))
  (hpos : 0<e) (hsmall : e≤2*n)
  (heq : c*2^m = 2^j*(2*n+3)+e) : False := by
  by_cases hj : j≤m
  · have hpow : 2^m=2^j*2^(m-j) := by
      calc
        2^m = 2^(j+(m-j)) := congrArg (fun x:Nat=>2^x) (by omega)
        _ = 2^j*2^(m-j) := by rw [Nat.pow_add]
    have hdiv1 : (2^j) ∣ c*2^m := by
      rw[hpow]
      exact ⟨c*2^(m-j), by ac_rfl⟩
    have hdiv2 : (2^j) ∣ 2^j*(2*n+3) := ⟨2*n+3,rfl⟩
    have heval : e=c*2^m - 2^j*(2*n+3) := by omega
    have hdiv : (2^j) ∣ e := by
      rw[heval]
      exact Nat.dvd_sub hdiv1 hdiv2
    have hl : 2^j ≤ e := Nat.le_of_dvd hpos hdiv
    have hx : 2^j*(2*n+3) ≤ 2*n*(2*n+3) :=
      Nat.mul_le_mul_right (2*n+3) (by omega)
    have hs : 2*n*(2*n+4) = 2*n*(2*n+3)+2*n := by
      simp [Nat.mul_add]
      omega
    rw [hs] at hcenter
    omega
  · have hj' : m+1≤j := by omega
    have hp : 2^(m+1)≤2^j :=
      Nat.pow_le_pow_right (by decide:0<(2:Nat)) hj'
    have hpow : 2^(m+1)=2*2^m := by
      rw [Nat.pow_succ]
      omega
    have hlt : c*2^m < 2^(m+1)*(2*n+3) := by
      rw[hpow]
      have hprime : c*2^m < (2*(2*n+3))*2^m :=
        Nat.mul_lt_mul_of_pos_right hc (Nat.pow_pos (by decide))
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hprime
    have hx : 2^(m+1)*(2*n+3) ≤ 2^j*(2*n+3) :=
      Nat.mul_le_mul_right (2*n+3) hp
    omega

private theorem no_seam17 (n j e:Nat) (hn:20≤n)
  (he:0<e) (he2:e≤2*n)
  (hh:17*2^(n-13)=2^j*(2*n+3)+e):False:=by
  exact no_close_to_power n j (n-13) 17 e (center17_growth n hn)
    (by omega) he he2 hh

private theorem no_seam49 (n j e:Nat) (hn:20≤n)
  (he:0<e) (he2:e≤2*n)
  (hh:49*2^(n-12)=2^j*(2*n+3)+e):False:=by
  exact no_close_to_power n j (n-12) 49 e (center49_growth n hn)
    (by omega) he he2 hh

private theorem power_at_least_linear (n:Nat) (hn:20≤n) :
  128*n ≤ 2^(n-4) := by
  let a := n-20
  have he:n=a+20:=by dsimp[a];omega
  rw[he]
  have h:∀a:Nat,128*(a+20)≤2^(a+16):=by
    intro a
    induction a with
    | zero => decide
    | succ a ih =>
      have hp:2^(a+1+16)=2*2^(a+16):=by
        rw[show a+1+16=(a+16)+1 by omega,Nat.pow_succ]
        omega
      rw[hp]
      omega
  simpa [show (a+20)-4=a+16 by omega] using h a

private theorem scale49 (n:Nat) (hn:20≤n) :
  512*(49*2^(n-12))=98*2^(n-4) := by
  have he:n-4=(n-12)+8:=by omega
  calc
    512*(49*2^(n-12)) = (512*49)*2^(n-12) := by ac_rfl
    _ = (98*256)*2^(n-12) := by rw [show (512:Nat)*49=98*256 by decide]
    _ = 98*2^(n-4) := by rw [he, Nat.pow_add]; simp only [show (2:Nat)^8=256 by decide]; ac_rfl

private theorem scale17 (n:Nat) (hn:20≤n) :
  1024*(17*2^(n-13))=34*2^(n-4) := by
  have he:n-4=(n-13)+9:=by omega
  calc
    1024*(17*2^(n-13)) = (1024*17)*2^(n-13) := by ac_rfl
    _ = (34*512)*2^(n-13) := by rw [show (1024:Nat)*17=34*512 by decide]
    _ = 34*2^(n-4) := by rw [he, Nat.pow_add]; simp only [show (2:Nat)^9=512 by decide]; ac_rfl

private theorem seam23 (n X p B center:Nat) (hn:20≤n)
 (hs:81*B+3=16*p+128*X+169*n)
 (hc:512*center=98*p)
 (hl:4*B+3*(n-4)≤2*p+1)
 (hh:4*p+3≤8*B+7*(n-4)) :
 ∃e, 0<e ∧ e≤2*n ∧ center=X+e := by
  have hm:n-4+4=n:=by omega
  have hlt:X<center:=by omega
  let e:=center-X
  have heq:center=X+e:=by dsimp[e];omega
  have helo:0<e:=by dsimp[e];omega
  have hehi:e≤2*n:=by dsimp[e];omega
  exact ⟨e,helo,hehi,heq⟩

private theorem seam34 (n X p B center:Nat) (hn:20≤n)
 (hs:81*B+3=16*p+128*X+169*n)
 (hc:1024*center=34*p)
 (hl:8*B+7*(n-4)≤2*p+1)
 (hh:4*p+3≤16*B+15*(n-4)) :
 ∃e, 0<e ∧ e≤2*n ∧ center=X+e := by
  have hlt:X<center:=by omega
  let e:=center-X
  have heq:center=X+e:=by dsimp[e];omega
  have helo:0<e:=by dsimp[e];omega
  have hehi:e≤2*n:=by dsimp[e];omega
  exact ⟨e,helo,hehi,heq⟩

private theorem elementary_bounds (n p X B:Nat) (hn:20≤n)
 (hp:128*n≤p)
 (hs:81*B+3=16*p+128*X+169*n)
 (hm:32*X+32*n+160≤16*p) :
  2*B+(n-4)≤2*p+1 ∧
  4*B+3*(n-4)<4*p+3 ∧
  2*p+1<16*B+15*(n-4) := by
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Every weak-margin second-generation t=1 inverse whose numerical
    equations hold enters the no-parent dyadic gap within 2, 3, or 4
    forced even inverse steps. This is an arithmetic statement; genuine
    source-root transfer is provided separately by EvenChainGap. -/
theorem weak_margin_no_seam (n j B:Nat) (hn:20≤n)
 (hs:81*B+3=16*2^(n-4)+128*(2^j*(2*n+3))+169*n)
 (hm:32*(2^j*(2*n+3))+32*n+160≤16*2^(n-4)) :
 let p:=2^(n-4)
 let m:=n-4
 let C1:=2*B+m
 let C2:=4*B+3*m
 let C3:=8*B+7*m
 let C4:=16*B+15*m
 (3≤B ∧ B≤2*p+1) →
 ∃ r, (r=2 ∨ r=3 ∨ r=4) ∧
   (if r=2 then (3≤B ∧ B≤2*p+1) ∧ (3≤C1 ∧ C1≤2*p+1) ∧
       (2*p+1<C2 ∧ C2<4*p+3)
    else if r=3 then (3≤B ∧ B≤2*p+1) ∧ (3≤C1 ∧ C1≤2*p+1) ∧
       (3≤C2 ∧ C2≤2*p+1) ∧ (2*p+1<C3 ∧ C3<4*p+3)
    else (3≤B ∧ B≤2*p+1) ∧ (3≤C1 ∧ C1≤2*p+1) ∧
       (3≤C2 ∧ C2≤2*p+1) ∧ (3≤C3 ∧ C3≤2*p+1) ∧
       (2*p+1<C4 ∧ C4<4*p+3)) := by
  dsimp only
  let p:=2^(n-4)
  let X:=2^j*(2*n+3)
  let m:=n-4
  intro hB
  have hpow:128*n≤p:=by dsimp[p];exact power_at_least_linear n hn
  have hbds:=elementary_bounds n p X B hn hpow hs hm
  have hC1lo:3≤2*B+m:=by dsimp[m];omega
  have hC2lo:3≤4*B+3*m:=by dsimp[m];omega
  have hC3lo:3≤8*B+7*m:=by dsimp[m];omega
  have hC1hi:2*B+m≤2*p+1:=hbds.1
  have hC2hi:4*B+3*m<4*p+3:=hbds.2.1
  have hC4lo:2*p+1<16*B+15*m:=hbds.2.2
  by_cases hC2:2*p+1<4*B+3*m
  · refine ⟨2,Or.inl rfl,?_⟩
    simp only [if_pos rfl]
    exact ⟨hB,⟨hC1lo,hC1hi⟩,⟨hC2,hC2hi⟩⟩
  · have hC2low:4*B+3*m≤2*p+1:=by omega
    have hC3hi:8*B+7*m<4*p+3:=by
      by_cases hbad:8*B+7*m<4*p+3
      · exact hbad
      · have hbad':4*p+3≤8*B+7*m:=by omega
        have hh:=seam23 n X p B (49*2^(n-12)) hn hs (scale49 n hn)
          (by dsimp[m] at hC2low ⊢; omega) (by dsimp[m] at hbad' ⊢; omega)
        obtain ⟨e,elo,ehi,heq⟩:=hh
        exact False.elim (no_seam49 n j e hn elo ehi (by dsimp[X] at heq;exact heq))
    by_cases hC3:2*p+1<8*B+7*m
    · refine ⟨3,Or.inr (Or.inl rfl),?_⟩
      simp only [if_neg (show (3:Nat)≠2 by decide), if_pos rfl]
      exact ⟨hB,⟨hC1lo,hC1hi⟩,⟨hC2lo,hC2low⟩,⟨hC3,hC3hi⟩⟩
    · have hC3low:8*B+7*m≤2*p+1:=by omega
      have hC4hi:16*B+15*m<4*p+3:=by
        by_cases hbad:16*B+15*m<4*p+3
        · exact hbad
        · have hbad':4*p+3≤16*B+15*m:=by omega
          have hh:=seam34 n X p B (17*2^(n-13)) hn hs (scale17 n hn)
            (by dsimp[m] at hC3low ⊢; omega) (by dsimp[m] at hbad' ⊢; omega)
          obtain ⟨e,elo,ehi,heq⟩:=hh
          exact False.elim (no_seam17 n j e hn elo ehi (by dsimp[X] at heq;exact heq))
      refine ⟨4,Or.inr (Or.inr rfl),?_⟩
      simp only [if_neg (show (4:Nat)≠2 by decide),if_neg (show (4:Nat)≠3 by decide)]
      exact ⟨hB,⟨hC1lo,hC1hi⟩,⟨hC2lo,hC2low⟩,⟨hC3lo,hC3low⟩,⟨hC4lo,hC4hi⟩⟩

private theorem scale16 (n:Nat) (hn:20≤n):
  2^n=16*2^(n-4):=by
  have he:n=(n-4)+4:=by omega
  calc
    2^n = 2^((n-4)+4) := congrArg (fun k:Nat=>2^k) he
    _ = 16*2^(n-4) := by
      rw [Nat.pow_add]
      simp only [show (2:Nat)^4=16 by decide]
      ac_rfl

private theorem linear_second_fork
 (n p X D h w q d:Nat) (hn:20≤n)
 (hdef:D+(n-1)=X)
 (hm:32*D+64*n+128≤16*p)
 (hl:9*h+8*D+9*n+7=224*p)
 (he:2*h=32*p+w+(n-2))
 (hw:2*w+5=9*d)
 (hq:4*d=8*p+q+(n-4)+5) :
  (q+3≤8*p) ∧ (6*p≤q+1) ∧
  (32*X+32*n+160≤16*p) ∧
  (81*(8*p-q)+3=16*p+128*X+169*n) := by
  have h1 : 9*w+16*D+27*n =160*p+4:=by omega
  have h2 : 81*d+32*D+54*n=320*p+53:=by omega
  have h3 : 81*q+128*D+297*n=632*p+131:=by omega
  have h4 : 128*D+256*n+512≤64*p:=by omega
  have hbhi:q+3≤8*p:=by
    clear hdef hm hl he hw hq h1 h2 h4
    omega
  have hblo:6*p≤q+1:=by
    clear hdef hl he hw hq h1 h2
    omega
  have hmargin:32*X+32*n+160≤16*p:=by
    clear hl he hw hq h1 h2 h3 h4
    omega
  let B:=8*p-q
  have hqle:q≤8*p := Nat.le_trans (Nat.le_add_right q 3) hbhi
  have hB:B+q=8*p := Nat.sub_add_cancel hqle
  have hsource:81*B+3=16*p+128*X+169*n:=by
    clear hm hl he hw hq h1 h2 h4 hbhi hblo hmargin
    omega
  exact ⟨hbhi,hblo,hmargin,by simpa only [B] using hsource⟩

private theorem inverse_b_bounds (p q :Nat)
 (hqhi:q+3≤8*p) (hqlo:6*p≤q+1) :
  3≤8*p-q ∧ 8*p-q≤2*p+1 := by omega

/-- Exact two-tier algebra derived from canonical source fork equations,
    plus the weak margin and deficit closed form. -/
theorem second_fork_to_seam (n j D h w q d:Nat) (hn:20≤n)
 (hdef:D+(n-1)=2^j*(2*n+3))
 (hm:32*D+64*n+128≤2^n)
 (hl:9*h+8*D+9*n+7=14*2^n)
 (he:2*h=2*2^n+w+(n-2))
 (hw:2*w+5=9*d)
 (hq:4*d=8*2^(n-4)+q+(n-4)+5) :
 let p:=2^(n-4)
 let B:=8*p-q
 (3≤B ∧ B≤2*p+1) ∧
 (81*B+3=16*p+128*(2^j*(2*n+3))+169*n) ∧
 (32*(2^j*(2*n+3))+32*n+160≤16*p) := by
  dsimp only
  let p:=2^(n-4)
  let X:=2^j*(2*n+3)
  have hp:2^n=16*p:=scale16 n hn
  have hm':32*D+64*n+128≤16*p:=by rw[hp] at hm;exact hm
  have hl':9*h+8*D+9*n+7=224*p:=by rw[hp] at hl;omega
  have he':2*h=32*p+w+(n-2):=by rw[hp] at he;omega
  obtain ⟨hqhi,hqlo,hmargin,hsource⟩:=
    linear_second_fork n p X D h w q d hn hdef hm' hl' he' hw hq
  have hbds:=inverse_b_bounds p q hqhi hqlo
  exact ⟨hbds,hsource,hmargin⟩

#print axioms weak_margin_no_seam
#print axioms second_fork_to_seam
end CascadeSeam
