import ThreeShallowFiniteBounds
import ThreeShallowIntegerAlgebra
namespace BB6.Agent43ThreeShallowFinite
open BB6.Agent43TwoShallowFinite
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

/-- For all n14..57, no first middle run of length >=3 is compatible
with the exact three-shallow terminal equation. -/
theorem num_three_small_u_bound
 (n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E : Nat)
 (hn : 14≤n) (hn58 : n<58) (hs : s≤3) (ht1 : t1≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+C3*(8^s*((2^alpha*8^u)*(2^beta*8^v))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*((2^gamma*8^r)*E+R3)+R2)+R1) : u≤2 := by
 have hmodP : 2^n % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨p,hP.symm⟩
 have hmodD : (14*n+92) % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨d,hD.symm⟩
 have hpDiv : 2^n / 8^s = p := by
   rw [←hP]
   exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
 have hdDiv : (14*n+92) / 8^s = d := by
   rw [←hD]
   exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
 have hN1 := BB6.Agent43ThreeShallowAlgebra.algebraic_first_three
   (2^n) (8^s) p d C1 C2 C3 L1 O1 K R1 R2 R3 E (n+6+3*s)
   (2^alpha*8^u) (2^beta*8^v) (2^gamma*8^r) hP hR1 hK hEq
 simp at hN1
 let X : Int := (C2:Int)*(2^n:Int)-(R2:Int)+
   ((2:Int)^beta)*(8:Int)^v*((C3:Int)*(2^n:Int)-(R3:Int)-((2:Int)^gamma)*(8:Int)^r*(E:Int))
 have hN1eq : 98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+(L1:Int)*(n+6+3*s:Int)-(O1:Int) =
     ((2:Int)^alpha)*(8:Int)^u*X := by
   simpa only [X,Int.natCast_mul,Int.natCast_pow,Int.mul_assoc] using hN1
 by_cases huBound : u≤2
 · exact huBound
 · exfalso
   have hu3 : 3≤u := by omega
   have h8 : (8:Int)^u=512*(8:Int)^(u-3) := by
     have he : u=3+(u-3) := by omega
     calc
       (8:Int)^u = (8:Int)^(3+(u-3)) := congrArg (fun x:Nat => (8:Int)^x) he
       _ = (8:Int)^3*(8:Int)^(u-3) := by rw [Int.pow_add]
       _ = 512*(8:Int)^(u-3) := by rw [show (8:Int)^3=512 by decide]
   have hDiv : ((2:Int)^alpha*512) ∣
      (98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+(L1:Int)*(n+6+3*s:Int)-(O1:Int)) := by
     rw [hN1eq]
     refine ⟨(8:Int)^(u-3)*X, ?_⟩
     rw [h8]
     ac_rfl
   have hDivP : let (a,c,l,o) := triple t1
      ((2:Int)^a*512) ∣
      (98*((↑((2:Nat)^n/8^s):Int))-(↑((14*n+92)/8^s):Int)-(c:Int)*(2^n:Int)+(l:Int)*(n+6+3*s:Int)-(o:Int)) := by
     simp only [hpDiv,hdDiv]
     simpa [←hprofile1] using hDiv
   have hN : let (a,c,l,o) := triple t1
      (98*((↑((2:Nat)^n/8^s):Int))-(↑((14*n+92)/8^s):Int)-(c:Int)*(2^n:Int)+(l:Int)*(n+6+3*s:Int)-(o:Int)) % ((2:Int)^a*512) = 0 :=
        Int.emod_eq_zero_of_dvd hDivP
   have hT : firstOverflow n s t1 = true := by
     simpa [firstOverflow,hmodP,hmodD,triple] using hN
   have hF : firstOverflow n s t1 = false := by
     have hh := first_overflow_false_58 (⟨n-14,by omega⟩ : Fin 44)
       (⟨s,by omega⟩ : Fin 4) (⟨t1,by omega⟩ : Fin 2)
     simpa [Fin.val,Nat.sub_add_cancel hn] using hh
   rw [hT] at hF
   contradiction

/-- The second middle run of a three-shallow terminal history has v<=2. -/
theorem num_three_small_v_bound
 (n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E : Nat)
 (hn : 14≤n) (hn58 : n<58) (hs : s≤3) (ht1 : t1≤1) (ht2 : t2≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hprofile2 : (beta,C2,L2,O2)=triple t2)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+C3*(8^s*((2^alpha*8^u)*(2^beta*8^v))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*((2^gamma*8^r)*E+R3)+R2)+R1) : v≤2 := by
 have hu := num_three_small_u_bound n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E
   hn hn58 hs ht1 hprofile1 hP hD hR1 hR2 hR3 hK hEq
 have hmodP : 2^n % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨p,hP.symm⟩
 have hmodD : (14*n+92) % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨d,hD.symm⟩
 have hpDiv : 2^n / 8^s = p := by
   rw [←hP]
   exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
 have hdDiv : (14*n+92) / 8^s = d := by
   rw [←hD]
   exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
 have hN1 := BB6.Agent43ThreeShallowAlgebra.algebraic_first_three
   (2^n) (8^s) p d C1 C2 C3 L1 O1 K R1 R2 R3 E (n+6+3*s)
   (2^alpha*8^u) (2^beta*8^v) (2^gamma*8^r) hP hR1 hK hEq
 simp at hN1
 let X : Int := (C2:Int)*(2^n:Int)-(R2:Int)+
   ((2:Int)^beta)*(8:Int)^v*((C3:Int)*(2^n:Int)-(R3:Int)-((2:Int)^gamma)*(8:Int)^r*(E:Int))
 let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+(L1:Int)*(n+6+3*s:Int)-(O1:Int)
 let Imid : Int := (N1/((2:Int)^alpha))/((8:Int)^u)
 let N2 : Int := Imid-(C2:Int)*(2^n:Int)+(L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int)
 have hN1eq : N1=((2:Int)^alpha)*(8:Int)^u*X := by
   simpa only [N1,X,Int.natCast_mul,Int.natCast_pow,Int.mul_assoc] using hN1
 have hapos : (2:Int)^alpha ≠ 0 := Int.pow_ne_zero (by decide)
 have huzpos : (8:Int)^u ≠ 0 := Int.pow_ne_zero (by decide)
 have hImid : Imid=X := by
   dsimp [Imid]
   rw [hN1eq]
   rw [Int.mul_assoc]
   rw [Int.mul_ediv_cancel_left _ hapos]
   exact Int.mul_ediv_cancel_left X huzpos
 have hR2int : (R2:Int)+(O2:Int)=(L2:Int)*(n+6+3*s+alpha+3*u:Int) := by
   have hh := congrArg (fun x : Nat => (x:Int)) hR2
   simpa using hh
 have hN2 : N2=((2:Int)^beta)*(8:Int)^v*((C3:Int)*(2^n:Int)-(R3:Int)-((2:Int)^gamma)*(8:Int)^r*(E:Int)) := by
   dsimp [N2,X] at *
   rw [hImid]
   omega
 by_cases hvBound : v≤2
 · exact hvBound
 · exfalso
   have hv3 : 3≤v := by omega
   have hv8 : (8:Int)^v=512*(8:Int)^(v-3) := by
     have he : v=3+(v-3) := by omega
     calc
       (8:Int)^v=(8:Int)^(3+(v-3)) := congrArg (fun x : Nat => (8:Int)^x) he
       _=(8:Int)^3*(8:Int)^(v-3) := by rw [Int.pow_add]
       _=512*(8:Int)^(v-3) := by rw [show (8:Int)^3=512 by decide]
   have hN1div : ((2:Int)^alpha) ∣ N1 := by
     rw [hN1eq]
     exact ⟨(8:Int)^u*X,by ac_rfl⟩
   have hN1zero : N1%((2:Int)^alpha)=0 := Int.emod_eq_zero_of_dvd hN1div
   have hI1mod : (N1/((2:Int)^alpha))%((8:Int)^u)=0 := by
     rw [hN1eq,Int.mul_assoc,Int.mul_ediv_cancel_left _ hapos]
     exact Int.emod_eq_zero_of_dvd ⟨X,by ac_rfl⟩
   have hN2div : ((2:Int)^beta*512) ∣ N2 := by
     rw [hN2,hv8]
     refine ⟨(8:Int)^(v-3)*((C3:Int)*(2^n:Int)-(R3:Int)-((2:Int)^gamma)*(8:Int)^r*(E:Int)), ?_⟩
     ac_rfl
   have hN2mod : N2%((2:Int)^beta*512)=0 := Int.emod_eq_zero_of_dvd hN2div
   have hsecond : secondOverflow n s u t1 t2=true := by
     have htt1 : triple t1=(alpha,C1,L1,O1) := hprofile1.symm
     have htt2 : triple t2=(beta,C2,L2,O2) := hprofile2.symm
     simp [secondOverflow,hmodP,hmodD,htt1,htt2,hpDiv,hdDiv,hN1zero,hI1mod,hN2mod,N1,N2,Imid]
   have hF : secondOverflow n s u t1 t2=false := by
     have hh := second_overflow_false_58 (⟨n-14,by omega⟩ : Fin 44) (⟨s,by omega⟩ : Fin 4)
       (⟨u,by omega⟩ : Fin 3) (⟨t1,by omega⟩ : Fin 2) (⟨t2,by omega⟩ : Fin 2)
     simpa [Fin.val,Nat.sub_add_cancel hn] using hh
   rw [hsecond] at hF
   contradiction

/-- Any final depth-two suffix of the three-shallow exact-wall equation has r<=2. -/
theorem num_three_small_r_bound
 (n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E : Nat)
 (hn : 14≤n) (hn58 : n<58) (hs : s≤3) (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hprofile2 : (beta,C2,L2,O2)=triple t2)
 (hprofile3 : (gamma,C3,L3,O3)=triple t3)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+C3*(8^s*((2^alpha*8^u)*(2^beta*8^v))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*((2^gamma*8^r)*E+R3)+R2)+R1) : r≤2 := by
 have hu := num_three_small_u_bound n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E
   hn hn58 hs ht1 hprofile1 hP hD hR1 hR2 hR3 hK hEq
 have hv := num_three_small_v_bound n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E
   hn hn58 hs ht1 ht2 hprofile1 hprofile2 hP hD hR1 hR2 hR3 hK hEq
 have hmodP : 2^n % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨p,hP.symm⟩
 have hmodD : (14*n+92) % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨d,hD.symm⟩
 have hpDiv : 2^n / 8^s = p := by
   rw [←hP]
   exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
 have hdDiv : (14*n+92) / 8^s = d := by
   rw [←hD]
   exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
 have hN1 := BB6.Agent43ThreeShallowAlgebra.algebraic_first_three
   (2^n) (8^s) p d C1 C2 C3 L1 O1 K R1 R2 R3 E (n+6+3*s)
   (2^alpha*8^u) (2^beta*8^v) (2^gamma*8^r) hP hR1 hK hEq
 simp at hN1
 let Y : Int := (C3:Int)*(2^n:Int)-(R3:Int)-((2:Int)^gamma)*(8:Int)^r*(E:Int)
 let X : Int := (C2:Int)*(2^n:Int)-(R2:Int)+((2:Int)^beta)*(8:Int)^v*Y
 let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+(L1:Int)*(n+6+3*s:Int)-(O1:Int)
 let Imid1 : Int := (N1/((2:Int)^alpha))/((8:Int)^u)
 let N2 : Int := Imid1-(C2:Int)*(2^n:Int)+(L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int)
 let Imid2 : Int := (N2/((2:Int)^beta))/((8:Int)^v)
 let N3 : Int := Imid2-(C3:Int)*(2^n:Int)+(L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int)-(O3:Int)
 have hN1eq : N1=((2:Int)^alpha)*(8:Int)^u*X := by
   simpa only [N1,X,Y,Int.natCast_mul,Int.natCast_pow,Int.mul_assoc] using hN1
 have hapos : (2:Int)^alpha ≠ 0 := Int.pow_ne_zero (by decide)
 have huzpos : (8:Int)^u ≠ 0 := Int.pow_ne_zero (by decide)
 have hbpos : (2:Int)^beta ≠ 0 := Int.pow_ne_zero (by decide)
 have hvzpos : (8:Int)^v ≠ 0 := Int.pow_ne_zero (by decide)
 have hImid1 : Imid1=X := by
   dsimp [Imid1]
   rw [hN1eq,Int.mul_assoc,Int.mul_ediv_cancel_left _ hapos]
   exact Int.mul_ediv_cancel_left X huzpos
 have hR2int : (R2:Int)+(O2:Int)=(L2:Int)*(n+6+3*s+alpha+3*u:Int) := by
   have hh := congrArg (fun x : Nat => (x:Int)) hR2
   simpa using hh
 have hN2 : N2=((2:Int)^beta)*(8:Int)^v*Y := by
   dsimp [N2,X] at *
   rw [hImid1]
   omega
 have hImid2 : Imid2=Y := by
   dsimp [Imid2]
   rw [hN2,Int.mul_assoc,Int.mul_ediv_cancel_left _ hbpos]
   exact Int.mul_ediv_cancel_left Y hvzpos
 have hR3int : (R3:Int)+(O3:Int)=(L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int) := by
   have hh := congrArg (fun x : Nat => (x:Int)) hR3
   simpa using hh
 have hN3 : N3=-((2:Int)^gamma*(8:Int)^r*(E:Int)) := by
   dsimp [N3,Y] at *
   rw [hImid2]
   omega
 by_cases hrBound : r≤2
 · exact hrBound
 · exfalso
   have hr3 : 3≤r := by omega
   have hr8 : (8:Int)^r=512*(8:Int)^(r-3) := by
     have he : r=3+(r-3) := by omega
     calc
       (8:Int)^r=(8:Int)^(3+(r-3)) := congrArg (fun x : Nat => (8:Int)^x) he
       _=(8:Int)^3*(8:Int)^(r-3) := by rw [Int.pow_add]
       _=512*(8:Int)^(r-3) := by rw [show (8:Int)^3=512 by decide]
   have hN1div : ((2:Int)^alpha) ∣ N1 := by
     rw [hN1eq]
     exact ⟨(8:Int)^u*X,by ac_rfl⟩
   have hN1mod : N1%((2:Int)^alpha)=0 := Int.emod_eq_zero_of_dvd hN1div
   have hJ1mod : (N1/((2:Int)^alpha))%((8:Int)^u)=0 := by
     rw [hN1eq,Int.mul_assoc,Int.mul_ediv_cancel_left _ hapos]
     exact Int.emod_eq_zero_of_dvd ⟨X,by ac_rfl⟩
   have hN2div : ((2:Int)^beta) ∣ N2 := by
     rw [hN2]
     exact ⟨(8:Int)^v*Y,by ac_rfl⟩
   have hN2mod : N2%((2:Int)^beta)=0 := Int.emod_eq_zero_of_dvd hN2div
   have hJ2mod : (N2/((2:Int)^beta))%((8:Int)^v)=0 := by
     rw [hN2,Int.mul_assoc,Int.mul_ediv_cancel_left _ hbpos]
     exact Int.emod_eq_zero_of_dvd ⟨Y,by ac_rfl⟩
   have hN3div : ((2:Int)^gamma*512) ∣ N3 := by
     rw [hN3,hr8]
     refine ⟨-((8:Int)^(r-3)*(E:Int)), ?_⟩
     simp only [Int.mul_neg,Int.neg_mul]
     ac_rfl
   have hN3mod : N3%((2:Int)^gamma*512)=0 := Int.emod_eq_zero_of_dvd hN3div
   have hthird : thirdOverflow n s u v t1 t2 t3=true := by
     have htt1 : triple t1=(alpha,C1,L1,O1) := hprofile1.symm
     have htt2 : triple t2=(beta,C2,L2,O2) := hprofile2.symm
     have htt3 : triple t3=(gamma,C3,L3,O3) := hprofile3.symm
     simp [thirdOverflow,hmodP,hmodD,htt1,htt2,htt3,hpDiv,hdDiv,hN1mod,hJ1mod,hN2mod,hJ2mod,hN3mod,N1,N2,N3,Imid1,Imid2]
   have hF : thirdOverflow n s u v t1 t2 t3=false := by
     have hh := third_overflow_false_58 (⟨n-14,by omega⟩ : Fin 44) (⟨s,by omega⟩ : Fin 4)
       (⟨u,by omega⟩ : Fin 3) (⟨v,by omega⟩ : Fin 3)
       (⟨t1,by omega⟩ : Fin 2) (⟨t2,by omega⟩ : Fin 2) (⟨t3,by omega⟩ : Fin 2)
     simpa [Fin.val,Nat.sub_add_cancel hn] using hh
   rw [hthird] at hF
   contradiction

/-- The fully quantified three-shallow terminal equation is impossible at
all remaining indices, with all runs unrestricted in the assumptions. -/
theorem no_three_small_numeric
 (n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E : Nat)
 (hn : 14≤n) (hn58 : n<58) (hs : s≤3) (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hprofile2 : (beta,C2,L2,O2)=triple t2)
 (hprofile3 : (gamma,C3,L3,O3)=triple t3)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*r))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+C3*(8^s*((2^alpha*8^u)*(2^beta*8^v))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*((2^gamma*8^r)*E+R3)+R2)+R1) : False := by
 have hu := num_three_small_u_bound n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E
   hn hn58 hs ht1 hprofile1 hP hD hR1 hR2 hR3 hK hEq
 have hv := num_three_small_v_bound n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E
   hn hn58 hs ht1 ht2 hprofile1 hprofile2 hP hD hR1 hR2 hR3 hK hEq
 have hr := num_three_small_r_bound n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E
   hn hn58 hs ht1 ht2 ht3 hprofile1 hprofile2 hprofile3 hP hD hR1 hR2 hR3 hK hEq
 have hmodP : 2^n % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨p,hP.symm⟩
 have hmodD : (14*n+92) % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨d,hD.symm⟩
 have hpDiv : 2^n / 8^s = p := by
   rw [←hP]
   exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
 have hdDiv : (14*n+92) / 8^s = d := by
   rw [←hD]
   exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
 have hR1nat : L1*(n+6+3*s)-O1-d=R1 := by omega
 have hR2nat : L2*(n+6+3*s+alpha+3*u)-O2=R2 := by omega
 have hR3nat : L3*(n+6+3*s+alpha+3*u+beta+3*v)-O3=R3 := by omega
 have hEnat : 112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*r)-384=E := by omega
 have hKnat : C1*8^s+C2*8^s*(2^alpha*8^u)+C3*8^s*(2^alpha*8^u)*(2^beta*8^v)-98=K := by
   have hh : K+98=C1*8^s+C2*8^s*(2^alpha*8^u)+C3*8^s*(2^alpha*8^u)*(2^beta*8^v) := by
     simpa only [Nat.mul_assoc] using hK
   omega
 have hBad : threeBad n s u v r t1 t2 t3=true := by
   simp [threeBad,hmodP,hmodD,hprofile1.symm,hprofile2.symm,hprofile3.symm,
     hpDiv,hdDiv,hR1nat,hR2nat,hR3nat,hEnat,hKnat,hEq]
 have hF : threeBad n s u v r t1 t2 t3=false := by
   have hh := no_three_small_bad_58 (⟨n-14,by omega⟩ : Fin 44) (⟨s,by omega⟩ : Fin 4)
     (⟨u,by omega⟩ : Fin 3) (⟨v,by omega⟩ : Fin 3) (⟨r,by omega⟩ : Fin 3)
     (⟨t1,by omega⟩ : Fin 2) (⟨t2,by omega⟩ : Fin 2) (⟨t3,by omega⟩ : Fin 2)
   simpa [Fin.val,Nat.sub_add_cancel hn] using hh
 rw [hBad] at hF
 contradiction

#print axioms num_three_small_u_bound
#print axioms num_three_small_v_bound
#print axioms num_three_small_r_bound
#print axioms no_three_small_numeric
end BB6.Agent43ThreeShallowFinite
