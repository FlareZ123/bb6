import TwoShallowFiniteBounds
import TwoShallowIntegerAlgebra

namespace BB6.Agent43TwoShallowFinite
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

theorem first_true
 (n s t : Nat)
 (hP : 2^n % 8^s = 0)
 (hD : (14*n+92) % 8^s = 0)
 (hN : let (alpha,C,L,O) := triple t
   (98*((↑((2:Nat)^n/8^s):Int))-(↑((14*n+92)/8^s):Int)-(C:Int)*(2^n:Int)+(L:Int)*(n+6+3*s:Int)-(O:Int)) % ((2:Int)^alpha*512) = 0) :
 firstOverflow n s t = true := by
  simpa [firstOverflow, hP, hD, triple] using hN

theorem finite_first_obstruction
 (n s t : Nat) (hn : 14 ≤ n) (hn48 : n < 48) (hs : s < 4) (ht : t < 2)
 (hP : 2^n % 8^s = 0)
 (hD : (14*n+92) % 8^s = 0)
 (hdiv : let (alpha,C,L,O) := triple t
   ((2:Int)^alpha*512) ∣
   (98*((↑((2:Nat)^n/8^s):Int))-(↑((14*n+92)/8^s):Int)-(C:Int)*(2^n:Int)+(L:Int)*(n+6+3*s:Int)-(O:Int))) : False := by
  have hN : let (alpha,C,L,O) := triple t
    (98*((↑((2:Nat)^n/8^s):Int))-(↑((14*n+92)/8^s):Int)-(C:Int)*(2^n:Int)+(L:Int)*(n+6+3*s:Int)-(O:Int)) % ((2:Int)^alpha*512) = 0 := by
    exact Int.emod_eq_zero_of_dvd hdiv
  have hF : firstOverflow n s t = false := by
    have hh := first_overflow_false (⟨n-14, by omega⟩ : Fin 34) (⟨s,hs⟩ : Fin 4) (⟨t,ht⟩ : Fin 2)
    simpa [Fin.val, Nat.sub_add_cancel hn] using hh
  have hT : firstOverflow n s t = true := first_true n s t hP hD hN
  rw [hT] at hF
  contradiction

#print axioms finite_first_obstruction

theorem num_small_u_bound
  (n s u r t1 t2 p d alpha beta C1 C2 L1 L2 O1 O2 K R1 R2 E : Nat)
  (hn : 14≤n) (hn48 : n<48) (hs : s≤3) (ht1 : t1≤1)
  (hprof1 : (alpha,C1,L1,O1)=triple t1)
  (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
  (hR1 : R1+O1+d=L1*(n+6+3*s))
  (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
  (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u)))
  (hEq : K*p=(2^alpha*8^u)*(2^beta*8^r*E+R2)+R1) : u≤2 := by
 have hmodP : 2^n % 8^s=0 := Nat.mod_eq_zero_of_dvd ⟨p, hP.symm⟩
 have hmodD : (14*n+92) % 8^s=0 := Nat.mod_eq_zero_of_dvd ⟨d, hD.symm⟩
 have hpDiv : 2^n/8^s=p := by
   have hpos : 0<(8:Nat)^s := Nat.pow_pos (by decide)
   rw [←hP]
   exact Nat.mul_div_cancel_left p hpos
 have hdDiv : (14*n+92)/8^s=d := by
   have hpos : 0<(8:Nat)^s := Nat.pow_pos (by decide)
   rw [←hD]
   exact Nat.mul_div_cancel_left d hpos
 by_cases huBound : u≤2
 · exact huBound
 · exfalso
   have hu3 : 3≤u := by omega
   have hN1 := BB6.Agent43TwoShallowAlgebra.algebraic_first (2^n) (8^s) p d alpha beta C1 C2 L1 L2 O1 O2 K R1 R2 E
      (n+6+3*s) (n+6+3*s+alpha+3*u) (8^u) (8^r) hP hR1 hR2 hK hEq
   have h8 : (8:Int)^u=512*(8:Int)^(u-3) := by
     have he : u=3+(u-3) := by omega
     calc
       (8:Int)^u = (8:Int)^(3+(u-3)) := congrArg (fun x : Nat => (8:Int)^x) he
       _ = (8:Int)^3*(8:Int)^(u-3) := by rw [Int.pow_add]
       _ = 512*(8:Int)^(u-3) := by rw [show (8:Int)^3=512 by decide]
   simp at hN1
   have hDiv : ((2:Int)^alpha*512) ∣
      (98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+(L1:Int)*(n+6+3*s:Int)-(O1:Int)) := by
     rw [hN1]
     refine ⟨(8:Int)^(u-3)*((C2:Int)*(2^n:Int)-((2:Int)^beta*(8^r:Int)*(E:Int)+(R2:Int))), ?_⟩
     rw [h8]
     ac_rfl
   have hDivP : let (a,c,l,o) := triple t1
      ((2:Int)^a*512) ∣
      (98*((↑((2:Nat)^n/8^s):Int))-(↑((14*n+92)/8^s):Int)-(c:Int)*(2^n:Int)+(l:Int)*(n+6+3*s:Int)-(o:Int)) := by
     simp only [hpDiv,hdDiv]
     simpa [←hprof1] using hDiv
   exact finite_first_obstruction n s t1 hn hn48 (by omega) (by omega) hmodP hmodD hDivP

#print axioms num_small_u_bound

theorem num_small_r_bound
  (n s u r t1 t2 p d alpha beta C1 C2 L1 L2 O1 O2 K R1 R2 E : Nat)
  (hn : 14≤n) (hn48 : n<48) (hs : s≤3) (ht1 : t1≤1) (ht2 : t2≤1)
  (hprof1 : (alpha,C1,L1,O1)=triple t1)
  (hprof2 : (beta,C2,L2,O2)=triple t2)
  (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
  (hR1 : R1+O1+d=L1*(n+6+3*s))
  (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
  (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u)))
  (hEq : K*p=(2^alpha*8^u)*(2^beta*8^r*E+R2)+R1) : r≤2 := by
 have hu : u≤2 := num_small_u_bound n s u r t1 t2 p d alpha beta C1 C2 L1 L2 O1 O2 K R1 R2 E
    hn hn48 hs ht1 hprof1 hP hD hR1 hR2 hK hEq
 have hmodP : 2^n % 8^s=0 := Nat.mod_eq_zero_of_dvd ⟨p, hP.symm⟩
 have hmodD : (14*n+92) % 8^s=0 := Nat.mod_eq_zero_of_dvd ⟨d, hD.symm⟩
 have hpDiv : 2^n/8^s=p := by
   rw [←hP]
   exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
 have hdDiv : (14*n+92)/8^s=d := by
   rw [←hD]
   exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
 have hN1 := BB6.Agent43TwoShallowAlgebra.algebraic_first (2^n) (8^s) p d alpha beta C1 C2 L1 L2 O1 O2 K R1 R2 E
    (n+6+3*s) (n+6+3*s+alpha+3*u) (8^u) (8^r) hP hR1 hR2 hK hEq
 simp at hN1
 let X : Int := (C2:Int)*(2^n:Int) - ((2:Int)^beta*(8^r:Int)*(E:Int)+(R2:Int))
 let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+(L1:Int)*(n+6+3*s:Int)-(O1:Int)
 let Imid : Int := (N1/((2:Int)^alpha))/((8:Int)^u)
 let N2 : Int := Imid-(C2:Int)*(2^n:Int)+(L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int)
 have hN1eq : N1=(2:Int)^alpha*(8:Int)^u*X := by simpa [N1,X] using hN1
 have hapos : (2:Int)^alpha≠0 := Int.pow_ne_zero (by decide)
 have huzpos : (8:Int)^u≠0 := Int.pow_ne_zero (by decide)
 have hImid : Imid=X := by
   dsimp [Imid]
   rw [hN1eq]
   rw [Int.mul_assoc]
   rw [Int.mul_ediv_cancel_left _ hapos]
   exact Int.mul_ediv_cancel_left X huzpos
 have hR2int : (R2:Int)+(O2:Int)=(L2:Int)*(n+6+3*s+alpha+3*u:Int) := by
   have hh : (↑(R2+O2):Int)=↑(L2*(n+6+3*s+alpha+3*u):Nat) := congrArg (fun x : Nat => (x:Int)) hR2
   simpa using hh
 have hN2 : N2=-((2:Int)^beta*(8:Int)^r*(E:Int)) := by
   dsimp [N2,X] at *
   rw [hImid]
   omega
 by_cases hr : r≤2
 · exact hr
 · exfalso
   have hr3 : 3≤r := by omega
   have hr8 : (8:Int)^r=512*(8:Int)^(r-3) := by
     have he : r=3+(r-3) := by omega
     calc
       (8:Int)^r=(8:Int)^(3+(r-3)) := congrArg (fun x : Nat => (8:Int)^x) he
       _ = (8:Int)^3*(8:Int)^(r-3) := by rw [Int.pow_add]
       _ = 512*(8:Int)^(r-3) := by rw [show (8:Int)^3=512 by decide]
   have hN1div : ((2:Int)^alpha) ∣ N1 := by
     rw [hN1eq]
     exact ⟨(8:Int)^u*X, by ac_rfl⟩
   have hN1zero : N1%((2:Int)^alpha)=0 := Int.emod_eq_zero_of_dvd hN1div
   have hI1mod : (N1/((2:Int)^alpha))%((8:Int)^u)=0 := by
     rw [hN1eq, Int.mul_assoc, Int.mul_ediv_cancel_left _ hapos]
     exact Int.emod_eq_zero_of_dvd ⟨X, by ac_rfl⟩
   have hN2div : ((2:Int)^beta*512) ∣ N2 := by
     rw [hN2,hr8]
     refine ⟨-((8:Int)^(r-3)*(E:Int)), ?_⟩
     simp only [Int.mul_neg,Int.neg_mul]
     ac_rfl
   have hN2mod : N2%((2:Int)^beta*512)=0 := Int.emod_eq_zero_of_dvd hN2div
   have hsecond : secondOverflow n s u t1 t2=true := by
     have htt1 : triple t1=(alpha,C1,L1,O1) := hprof1.symm
     have htt2 : triple t2=(beta,C2,L2,O2) := hprof2.symm
     simp [secondOverflow,hmodP,hmodD,htt1,htt2,hpDiv,hdDiv,hN1zero,hI1mod,hN2mod,N1,N2,Imid]
   have hF : secondOverflow n s u t1 t2=false := by
     have hh := second_overflow_false (⟨n-14,by omega⟩ : Fin 34) (⟨s,by omega⟩ : Fin 4)
      (⟨u,by omega⟩ : Fin 3) (⟨t1,by omega⟩ : Fin 2) (⟨t2,by omega⟩ : Fin 2)
     simpa [Fin.val,Nat.sub_add_cancel hn] using hh
   rw [hsecond] at hF
   contradiction

#print axioms num_small_r_bound

/-- Every two-shallow terminal equality is impossible at the remaining indices. -/
theorem no_small_numeric
  (n s u r t1 t2 p d alpha beta C1 C2 L1 L2 O1 O2 K R1 R2 E : Nat)
  (hn : 14≤n) (hn48 : n<48) (hs : s≤3) (ht1 : t1≤1) (ht2 : t2≤1)
  (hprof1 : (alpha,C1,L1,O1)=triple t1)
  (hprof2 : (beta,C2,L2,O2)=triple t2)
  (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
  (hR1 : R1+O1+d=L1*(n+6+3*s))
  (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
  (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*r))
  (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u)))
  (hEq : K*p=(2^alpha*8^u)*(2^beta*8^r*E+R2)+R1) : False := by
 have hu := num_small_u_bound n s u r t1 t2 p d alpha beta C1 C2 L1 L2 O1 O2 K R1 R2 E
    hn hn48 hs ht1 hprof1 hP hD hR1 hR2 hK hEq
 have hr := num_small_r_bound n s u r t1 t2 p d alpha beta C1 C2 L1 L2 O1 O2 K R1 R2 E
    hn hn48 hs ht1 ht2 hprof1 hprof2 hP hD hR1 hR2 hK hEq
 have hmodP : 2^n % 8^s=0 := Nat.mod_eq_zero_of_dvd ⟨p, hP.symm⟩
 have hmodD : (14*n+92) % 8^s=0 := Nat.mod_eq_zero_of_dvd ⟨d, hD.symm⟩
 have hpDiv : 2^n/8^s=p := by
   rw [←hP]
   exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
 have hdDiv : (14*n+92)/8^s=d := by
   rw [←hD]
   exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
 have hR1nat : L1*(n+6+3*s)-O1-d=R1 := by omega
 have hR2nat : L2*(n+6+3*s+alpha+3*u)-O2=R2 := by omega
 have hEnat : 112*(n+6+3*s+alpha+3*u+beta+3*r)-384=E := by omega
 have hKnat : C1*8^s+C2*(8^s*(2^alpha*8^u))-98=K := by omega
 have hKnat' : C1*8^s+C2*8^s*(2^alpha*8^u)-98=K := by
   simpa only [Nat.mul_assoc] using hKnat
 have hBad : smallBad n s u r t1 t2=true := by
   simp [smallBad, hmodP, hmodD, hprof1.symm,hprof2.symm, hpDiv,hdDiv,hR1nat,hR2nat,hEnat,hKnat',hEq]
 have hF : smallBad n s u r t1 t2=false := by
   have hh := no_small_bad_test (⟨n-14,by omega⟩ : Fin 34) (⟨s,by omega⟩ : Fin 4)
    (⟨u,by omega⟩ : Fin 3) (⟨r,by omega⟩ : Fin 3)
    (⟨t1,by omega⟩ : Fin 2) (⟨t2,by omega⟩ : Fin 2)
   simpa [Fin.val,Nat.sub_add_cancel hn] using hh
 rw [hBad] at hF
 contradiction

#print axioms no_small_numeric
end BB6.Agent43TwoShallowFinite
