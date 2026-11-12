import FourShallowFiniteBounds
import FourShallowIntegerAlgebra
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43FourShallowFiniteBridge

open BB6.Agent43TwoShallowFinite
open BB6.Agent43FourShallowFinite

set_option maxRecDepth 4096
set_option maxHeartbeats 12000000

/-- The first depth-two run after the first shallow edge has length at most
two in every small-index four-shallow wall equation. -/
theorem num_four_small_u_bound
 (n s u v w r t1 t2 t3 t4 p d alpha beta gamma delta
  C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4 K R1 R2 R3 R4 E : Nat)
 (hn14 : 14≤n) (hn76 : n<76) (hs : s≤3) (ht1 : t1≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*
   ((2^gamma*8^w)*((2^delta*8^r)*E+R4)+R3)+R2)+R1) : u≤2 := by
 have hmodP : 2^n % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨p,hP.symm⟩
 have hmodD : (14*n+92) % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨d,hD.symm⟩
 have hpDiv : 2^n / 8^s = p := by
   rw [←hP]
   exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
 have hdDiv : (14*n+92) / 8^s = d := by
   rw [←hD]
   exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
 have hN1 := BB6.Agent43FourShallowAlgebra.algebraic_first_four
   (2^n) (8^s) p d C1 C2 C3 C4 L1 O1 K R1 R2 R3 R4 E (n+6+3*s)
   (2^alpha*8^u) (2^beta*8^v) (2^gamma*8^w) (2^delta*8^r)
   hP hR1 hK hEq
 simp at hN1
 let X : Int := (C2:Int)*(2^n:Int)-(R2:Int)+
   ((2:Int)^beta)*(8:Int)^v*((C3:Int)*(2^n:Int)-(R3:Int)+
     ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)-
       ((2:Int)^delta)*(8:Int)^r*(E:Int)))
 let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
   (L1:Int)*(n+6+3*s:Int)-(O1:Int)
 have hN1eq : N1=((2:Int)^alpha)*(8:Int)^u*X := by
   simpa only [N1,X,Int.natCast_mul,Int.natCast_pow,Int.mul_assoc] using hN1
 by_cases huBound : u≤2
 · exact huBound
 · exfalso
   have hu3 : 3≤u := by omega
   have hu8 : (8:Int)^u=512*(8:Int)^(u-3) := by
     have he : u=3+(u-3) := by omega
     calc
       (8:Int)^u=(8:Int)^(3+(u-3)) := congrArg (fun x:Nat=>(8:Int)^x) he
       _=(8:Int)^3*(8:Int)^(u-3) := by rw [Int.pow_add]
       _=512*(8:Int)^(u-3) := by rw [show (8:Int)^3=512 by decide]
   have hDiv : ((2:Int)^alpha*512) ∣ N1 := by
     rw [hN1eq]
     refine ⟨(8:Int)^(u-3)*X, ?_⟩
     rw [hu8]
     ac_rfl
   have hDivP : let (a,c,l,o) := triple t1
      ((2:Int)^a*512) ∣
      (98*((↑((2:Nat)^n/8^s):Int))-(↑((14*n+92)/8^s):Int)-
        (c:Int)*(2^n:Int)+(l:Int)*(n+6+3*s:Int)-(o:Int)) := by
     simp only [hpDiv,hdDiv]
     simpa [←hprofile1] using hDiv
   have hN : let (a,c,l,o) := triple t1
      (98*((↑((2:Nat)^n/8^s):Int))-(↑((14*n+92)/8^s):Int)-
        (c:Int)*(2^n:Int)+(l:Int)*(n+6+3*s:Int)-(o:Int)) % ((2:Int)^a*512) = 0 :=
     Int.emod_eq_zero_of_dvd hDivP
   have hT : BB6.Agent43TwoShallowFinite.firstOverflow n s t1 = true := by
     simpa [BB6.Agent43TwoShallowFinite.firstOverflow,hmodP,hmodD,triple] using hN
   have hF : BB6.Agent43TwoShallowFinite.firstOverflow n s t1 = false := by
     have hh := four_first_overflow_false_76
       (⟨n-14,by omega⟩ : Fin 62) (⟨s,by omega⟩ : Fin 4) (⟨t1,by omega⟩ : Fin 2)
     simpa [Fin.val,Nat.sub_add_cancel hn14] using hh
   rw [hT] at hF
   contradiction

/-- The second depth-two run after the second shallow edge also has length
at most two. -/
theorem num_four_small_v_bound
 (n s u v w r t1 t2 t3 t4 p d alpha beta gamma delta
  C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4 K R1 R2 R3 R4 E : Nat)
 (hn14 : 14≤n) (hn76 : n<76) (hs : s≤3) (ht1 : t1≤1) (ht2 : t2≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hprofile2 : (beta,C2,L2,O2)=triple t2)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*
   ((2^gamma*8^w)*((2^delta*8^r)*E+R4)+R3)+R2)+R1) : v≤2 := by
 have hu := num_four_small_u_bound n s u v w r t1 t2 t3 t4 p d
   alpha beta gamma delta C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4
   K R1 R2 R3 R4 E hn14 hn76 hs ht1 hprofile1 hP hD hR1 hR2 hR3 hR4 hK hEq
 have hmodP : 2^n % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨p,hP.symm⟩
 have hmodD : (14*n+92) % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨d,hD.symm⟩
 have hpDiv : 2^n / 8^s = p := by
   rw [←hP]
   exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
 have hdDiv : (14*n+92) / 8^s = d := by
   rw [←hD]
   exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
 have hN1 := BB6.Agent43FourShallowAlgebra.algebraic_first_four
   (2^n) (8^s) p d C1 C2 C3 C4 L1 O1 K R1 R2 R3 R4 E (n+6+3*s)
   (2^alpha*8^u) (2^beta*8^v) (2^gamma*8^w) (2^delta*8^r)
   hP hR1 hK hEq
 simp at hN1
 let X : Int := (C2:Int)*(2^n:Int)-(R2:Int)+
   ((2:Int)^beta)*(8:Int)^v*((C3:Int)*(2^n:Int)-(R3:Int)+
     ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)-
       ((2:Int)^delta)*(8:Int)^r*(E:Int)))
 let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
   (L1:Int)*(n+6+3*s:Int)-(O1:Int)
 let Imid : Int := (N1/((2:Int)^alpha))/((8:Int)^u)
 let N2 : Int := Imid-(C2:Int)*(2^n:Int)+
   (L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int)
 let Y : Int := (C3:Int)*(2^n:Int)-(R3:Int)+
   ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)-
     ((2:Int)^delta)*(8:Int)^r*(E:Int))
 have hN1eq : N1=((2:Int)^alpha)*(8:Int)^u*X := by
   simpa only [N1,X,Int.natCast_mul,Int.natCast_pow,Int.mul_assoc] using hN1
 have hapos : (2:Int)^alpha ≠ 0 := Int.pow_ne_zero (by decide)
 have huzpos : (8:Int)^u ≠ 0 := Int.pow_ne_zero (by decide)
 have hImid : Imid=X := by
   dsimp [Imid]
   rw [hN1eq,Int.mul_assoc,Int.mul_ediv_cancel_left _ hapos]
   exact Int.mul_ediv_cancel_left X huzpos
 have hR2int : (R2:Int)+(O2:Int)=
     (L2:Int)*(n+6+3*s+alpha+3*u:Int) := by exact_mod_cast hR2
 have hN2 : N2=((2:Int)^beta)*(8:Int)^v*Y := by
   dsimp [N2,X,Y] at *
   rw [hImid]
   omega
 by_cases hvBound : v≤2
 · exact hvBound
 · exfalso
   have hv3 : 3≤v := by omega
   have hv8 : (8:Int)^v=512*(8:Int)^(v-3) := by
     have he : v=3+(v-3) := by omega
     calc
       (8:Int)^v=(8:Int)^(3+(v-3)) := congrArg (fun x:Nat=>(8:Int)^x) he
       _=(8:Int)^3*(8:Int)^(v-3) := by rw [Int.pow_add]
       _=512*(8:Int)^(v-3) := by rw [show (8:Int)^3=512 by decide]
   have hN1div : ((2:Int)^alpha) ∣ N1 := by
     rw [hN1eq]
     exact ⟨(8:Int)^u*X,by ac_rfl⟩
   have hN1mod : N1%((2:Int)^alpha)=0 := Int.emod_eq_zero_of_dvd hN1div
   have hI1mod : (N1/((2:Int)^alpha))%((8:Int)^u)=0 := by
     rw [hN1eq,Int.mul_assoc,Int.mul_ediv_cancel_left _ hapos]
     exact Int.emod_eq_zero_of_dvd ⟨X,by ac_rfl⟩
   have hN2div : ((2:Int)^beta*512) ∣ N2 := by
     rw [hN2,hv8]
     refine ⟨(8:Int)^(v-3)*Y, ?_⟩
     ac_rfl
   have hN2mod : N2%((2:Int)^beta*512)=0 := Int.emod_eq_zero_of_dvd hN2div
   have hsecond : BB6.Agent43TwoShallowFinite.secondOverflow n s u t1 t2 = true := by
     have htt1 : triple t1=(alpha,C1,L1,O1) := hprofile1.symm
     have htt2 : triple t2=(beta,C2,L2,O2) := hprofile2.symm
     simp [BB6.Agent43TwoShallowFinite.secondOverflow,hmodP,hmodD,
       htt1,htt2,hpDiv,hdDiv,hN1mod,hI1mod,hN2mod,N1,N2,Imid]
   have hF : BB6.Agent43TwoShallowFinite.secondOverflow n s u t1 t2 = false := by
     have hh := four_second_overflow_false_76
       (⟨n-14,by omega⟩ : Fin 62) (⟨s,by omega⟩ : Fin 4)
       (⟨u,by omega⟩ : Fin 3) (⟨t1,by omega⟩ : Fin 2) (⟨t2,by omega⟩ : Fin 2)
     simpa [Fin.val,Nat.sub_add_cancel hn14] using hh
   rw [hsecond] at hF
   contradiction

/-- The third depth-two run after the third shallow edge has length at most
two. -/
theorem num_four_small_w_bound
 (n s u v w r t1 t2 t3 t4 p d alpha beta gamma delta
  C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4 K R1 R2 R3 R4 E : Nat)
 (hn14 : 14≤n) (hn76 : n<76) (hs : s≤3)
 (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hprofile2 : (beta,C2,L2,O2)=triple t2)
 (hprofile3 : (gamma,C3,L3,O3)=triple t3)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*
   ((2^gamma*8^w)*((2^delta*8^r)*E+R4)+R3)+R2)+R1) : w≤2 := by
 have hu := num_four_small_u_bound n s u v w r t1 t2 t3 t4 p d
   alpha beta gamma delta C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4
   K R1 R2 R3 R4 E hn14 hn76 hs ht1 hprofile1 hP hD hR1 hR2 hR3 hR4 hK hEq
 have hv := num_four_small_v_bound n s u v w r t1 t2 t3 t4 p d
   alpha beta gamma delta C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4
   K R1 R2 R3 R4 E hn14 hn76 hs ht1 ht2 hprofile1 hprofile2
   hP hD hR1 hR2 hR3 hR4 hK hEq
 have hmodP : 2^n % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨p,hP.symm⟩
 have hmodD : (14*n+92) % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨d,hD.symm⟩
 have hpDiv : 2^n / 8^s = p := by
   rw [←hP]
   exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
 have hdDiv : (14*n+92) / 8^s = d := by
   rw [←hD]
   exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
 have hN1 := BB6.Agent43FourShallowAlgebra.algebraic_first_four
   (2^n) (8^s) p d C1 C2 C3 C4 L1 O1 K R1 R2 R3 R4 E (n+6+3*s)
   (2^alpha*8^u) (2^beta*8^v) (2^gamma*8^w) (2^delta*8^r)
   hP hR1 hK hEq
 simp at hN1
 let X : Int := (C2:Int)*(2^n:Int)-(R2:Int)+
   ((2:Int)^beta)*(8:Int)^v*((C3:Int)*(2^n:Int)-(R3:Int)+
     ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)-
       ((2:Int)^delta)*(8:Int)^r*(E:Int)))
 let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
   (L1:Int)*(n+6+3*s:Int)-(O1:Int)
 let Imid1 : Int := (N1/((2:Int)^alpha))/((8:Int)^u)
 let N2 : Int := Imid1-(C2:Int)*(2^n:Int)+
   (L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int)
 let Imid2 : Int := (N2/((2:Int)^beta))/((8:Int)^v)
 let N3 : Int := Imid2-(C3:Int)*(2^n:Int)+
   (L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int)-(O3:Int)
 let Y : Int := (C4:Int)*(2^n:Int)-(R4:Int)-
   ((2:Int)^delta)*(8:Int)^r*(E:Int)
 have hN1eq : N1=((2:Int)^alpha)*(8:Int)^u*X := by
   simpa only [N1,X,Int.natCast_mul,Int.natCast_pow,Int.mul_assoc] using hN1
 have hapos : (2:Int)^alpha ≠ 0 := Int.pow_ne_zero (by decide)
 have huzpos : (8:Int)^u ≠ 0 := Int.pow_ne_zero (by decide)
 have hbpos : (2:Int)^beta ≠ 0 := Int.pow_ne_zero (by decide)
 have hvzpos : (8:Int)^v ≠ 0 := Int.pow_ne_zero (by decide)
 have hImid1 : Imid1=X := by
   dsimp [Imid1]
   rw [hN1eq,Int.mul_assoc,Int.mul_ediv_cancel_left _ hapos]
   exact Int.mul_ediv_cancel_left X huzpos
 have hR2int : (R2:Int)+(O2:Int)=
     (L2:Int)*(n+6+3*s+alpha+3*u:Int) := by exact_mod_cast hR2
 have hN2 : N2=((2:Int)^beta)*(8:Int)^v*
     ((C3:Int)*(2^n:Int)-(R3:Int)+
       ((2:Int)^gamma)*(8:Int)^w*Y) := by
   dsimp [N2,X,Y] at *
   rw [hImid1]
   omega
 have hImid2 : Imid2=((C3:Int)*(2^n:Int)-(R3:Int)+
     ((2:Int)^gamma)*(8:Int)^w*Y) := by
   dsimp [Imid2]
   rw [hN2,Int.mul_assoc,Int.mul_ediv_cancel_left _ hbpos]
   exact Int.mul_ediv_cancel_left _ hvzpos
 have hR3int : (R3:Int)+(O3:Int)=
     (L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int) := by exact_mod_cast hR3
 have hN3 : N3=((2:Int)^gamma)*(8:Int)^w*Y := by
   dsimp [N3,Y] at *
   rw [hImid2]
   omega
 by_cases hwBound : w≤2
 · exact hwBound
 · exfalso
   have hw3 : 3≤w := by omega
   have hw8 : (8:Int)^w=512*(8:Int)^(w-3) := by
     have he : w=3+(w-3) := by omega
     calc
       (8:Int)^w=(8:Int)^(3+(w-3)) := congrArg (fun x:Nat=>(8:Int)^x) he
       _=(8:Int)^3*(8:Int)^(w-3) := by rw [Int.pow_add]
       _=512*(8:Int)^(w-3) := by rw [show (8:Int)^3=512 by decide]
   have hN1div : ((2:Int)^alpha) ∣ N1 := by
     rw [hN1eq]
     exact ⟨(8:Int)^u*X,by ac_rfl⟩
   have hN1mod : N1%((2:Int)^alpha)=0 := Int.emod_eq_zero_of_dvd hN1div
   have hJ1mod : (N1/((2:Int)^alpha))%((8:Int)^u)=0 := by
     rw [hN1eq,Int.mul_assoc,Int.mul_ediv_cancel_left _ hapos]
     exact Int.emod_eq_zero_of_dvd ⟨X,by ac_rfl⟩
   have hN2div : ((2:Int)^beta) ∣ N2 := by
     rw [hN2]
     exact ⟨(8:Int)^v*((C3:Int)*(2^n:Int)-(R3:Int)+
       ((2:Int)^gamma)*(8:Int)^w*Y),by ac_rfl⟩
   have hN2mod : N2%((2:Int)^beta)=0 := Int.emod_eq_zero_of_dvd hN2div
   have hJ2mod : (N2/((2:Int)^beta))%((8:Int)^v)=0 := by
     rw [hN2,Int.mul_assoc,Int.mul_ediv_cancel_left _ hbpos]
     exact Int.emod_eq_zero_of_dvd ⟨(C3:Int)*(2^n:Int)-(R3:Int)+
       ((2:Int)^gamma)*(8:Int)^w*Y,by ac_rfl⟩
   have hN3div : ((2:Int)^gamma*512) ∣ N3 := by
     rw [hN3,hw8]
     refine ⟨(8:Int)^(w-3)*Y, ?_⟩
     ac_rfl
   have hN3mod : N3%((2:Int)^gamma*512)=0 := Int.emod_eq_zero_of_dvd hN3div
   have hthird : BB6.Agent43ThreeShallowFinite.thirdOverflow n s u v t1 t2 t3 = true := by
     have htt1 : triple t1=(alpha,C1,L1,O1) := hprofile1.symm
     have htt2 : triple t2=(beta,C2,L2,O2) := hprofile2.symm
     have htt3 : triple t3=(gamma,C3,L3,O3) := hprofile3.symm
     simp [BB6.Agent43ThreeShallowFinite.thirdOverflow,hmodP,hmodD,
       htt1,htt2,htt3,hpDiv,hdDiv,hN1mod,hJ1mod,hN2mod,hJ2mod,hN3mod,
       N1,N2,N3,Imid1,Imid2]
   have hF : BB6.Agent43ThreeShallowFinite.thirdOverflow n s u v t1 t2 t3 = false := by
     have hh := four_third_overflow_false_76
       (⟨n-14,by omega⟩ : Fin 62) (⟨s,by omega⟩ : Fin 4)
       (⟨u,by omega⟩ : Fin 3) (⟨v,by omega⟩ : Fin 3)
       (⟨t1,by omega⟩ : Fin 2) (⟨t2,by omega⟩ : Fin 2) (⟨t3,by omega⟩ : Fin 2)
     simpa [Fin.val,Nat.sub_add_cancel hn14] using hh
   rw [hthird] at hF
   contradiction

/-- The last depth-two run in the four-shallow terminal history has length
at most two. -/
theorem num_four_small_r_bound
 (n s u v w r t1 t2 t3 t4 p d alpha beta gamma delta
  C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4 K R1 R2 R3 R4 E : Nat)
 (hn14 : 14≤n) (hn76 : n<76) (hs : s≤3)
 (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1) (ht4 : t4≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hprofile2 : (beta,C2,L2,O2)=triple t2)
 (hprofile3 : (gamma,C3,L3,O3)=triple t3)
 (hprofile4 : (delta,C4,L4,O4)=triple t4)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*r))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*
   ((2^gamma*8^w)*((2^delta*8^r)*E+R4)+R3)+R2)+R1) : r≤2 := by
 have hu := num_four_small_u_bound n s u v w r t1 t2 t3 t4 p d
   alpha beta gamma delta C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4
   K R1 R2 R3 R4 E hn14 hn76 hs ht1 hprofile1 hP hD hR1 hR2 hR3 hR4 hK hEq
 have hv := num_four_small_v_bound n s u v w r t1 t2 t3 t4 p d
   alpha beta gamma delta C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4
   K R1 R2 R3 R4 E hn14 hn76 hs ht1 ht2 hprofile1 hprofile2
   hP hD hR1 hR2 hR3 hR4 hK hEq
 have hw := num_four_small_w_bound n s u v w r t1 t2 t3 t4 p d
   alpha beta gamma delta C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4
   K R1 R2 R3 R4 E hn14 hn76 hs ht1 ht2 ht3 hprofile1 hprofile2 hprofile3
   hP hD hR1 hR2 hR3 hR4 hK hEq
 have hmodP : 2^n % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨p,hP.symm⟩
 have hmodD : (14*n+92) % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨d,hD.symm⟩
 have hpDiv : 2^n / 8^s = p := by
   rw [←hP]
   exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
 have hdDiv : (14*n+92) / 8^s = d := by
   rw [←hD]
   exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
 have hN1 := BB6.Agent43FourShallowAlgebra.algebraic_first_four
   (2^n) (8^s) p d C1 C2 C3 C4 L1 O1 K R1 R2 R3 R4 E (n+6+3*s)
   (2^alpha*8^u) (2^beta*8^v) (2^gamma*8^w) (2^delta*8^r)
   hP hR1 hK hEq
 simp at hN1
 let X : Int := (C2:Int)*(2^n:Int)-(R2:Int)+
   ((2:Int)^beta)*(8:Int)^v*((C3:Int)*(2^n:Int)-(R3:Int)+
     ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)-
       ((2:Int)^delta)*(8:Int)^r*(E:Int)))
 let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
   (L1:Int)*(n+6+3*s:Int)-(O1:Int)
 let Imid1 : Int := (N1/((2:Int)^alpha))/((8:Int)^u)
 let N2 : Int := Imid1-(C2:Int)*(2^n:Int)+
   (L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int)
 let Imid2 : Int := (N2/((2:Int)^beta))/((8:Int)^v)
 let N3 : Int := Imid2-(C3:Int)*(2^n:Int)+
   (L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int)-(O3:Int)
 let Imid3 : Int := (N3/((2:Int)^gamma))/((8:Int)^w)
 let N4 : Int := Imid3-(C4:Int)*(2^n:Int)+
   (L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int)-(O4:Int)
 let Y : Int := -(((2:Int)^delta)*(8:Int)^r*(E:Int))
 have hN1eq : N1=((2:Int)^alpha)*(8:Int)^u*X := by
   simpa only [N1,X,Int.natCast_mul,Int.natCast_pow,Int.mul_assoc] using hN1
 have hapos : (2:Int)^alpha ≠ 0 := Int.pow_ne_zero (by decide)
 have huzpos : (8:Int)^u ≠ 0 := Int.pow_ne_zero (by decide)
 have hbpos : (2:Int)^beta ≠ 0 := Int.pow_ne_zero (by decide)
 have hvzpos : (8:Int)^v ≠ 0 := Int.pow_ne_zero (by decide)
 have hImid1 : Imid1=X := by
   dsimp [Imid1]
   rw [hN1eq,Int.mul_assoc,Int.mul_ediv_cancel_left _ hapos]
   exact Int.mul_ediv_cancel_left X huzpos
 have hR2int : (R2:Int)+(O2:Int)=
     (L2:Int)*(n+6+3*s+alpha+3*u:Int) := by exact_mod_cast hR2
 have hN2 : N2=((2:Int)^beta)*(8:Int)^v*
     ((C3:Int)*(2^n:Int)-(R3:Int)+
       ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)-
         ((2:Int)^delta)*(8:Int)^r*(E:Int))) := by
   dsimp [N2,X] at *
   rw [hImid1]
   omega
 have hImid2 : Imid2=((C3:Int)*(2^n:Int)-(R3:Int)+
     ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)-
       ((2:Int)^delta)*(8:Int)^r*(E:Int))) := by
   dsimp [Imid2]
   rw [hN2,Int.mul_assoc,Int.mul_ediv_cancel_left _ hbpos]
   exact Int.mul_ediv_cancel_left _ hvzpos
 have hR3int : (R3:Int)+(O3:Int)=
     (L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int) := by exact_mod_cast hR3
 have hN3 : N3=((2:Int)^gamma)*(8:Int)^w*
     ((C4:Int)*(2^n:Int)-(R4:Int)-((2:Int)^delta)*(8:Int)^r*(E:Int)) := by
   dsimp [N3] at *
   rw [hImid2]
   omega
 have hImid3 : Imid3=(C4:Int)*(2^n:Int)-(R4:Int)-
     ((2:Int)^delta)*(8:Int)^r*(E:Int) := by
   dsimp [Imid3]
   rw [hN3,Int.mul_assoc,Int.mul_ediv_cancel_left _ (Int.pow_ne_zero (by decide : (2:Int)≠0))]
   exact Int.mul_ediv_cancel_left _ (Int.pow_ne_zero (by decide : (8:Int)≠0))
 have hR4int : (R4:Int)+(O4:Int)=
     (L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int) := by exact_mod_cast hR4
 have hN4 : N4=-(((2:Int)^delta)*(8:Int)^r*(E:Int)) := by
    dsimp [N4,Y] at *
    rw [hImid3]
    rw [←hR4int]
    omega
 by_cases hrBound : r≤2
 · exact hrBound
 · exfalso
   have hr3 : 3≤r := by omega
   have hr8 : (8:Int)^r=512*(8:Int)^(r-3) := by
     have he : r=3+(r-3) := by omega
     calc
       (8:Int)^r=(8:Int)^(3+(r-3)) := congrArg (fun x:Nat=>(8:Int)^x) he
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
     exact ⟨(8:Int)^v*((C3:Int)*(2^n:Int)-(R3:Int)+
       ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)-
         ((2:Int)^delta)*(8:Int)^r*(E:Int))),by ac_rfl⟩
   have hN2mod : N2%((2:Int)^beta)=0 := Int.emod_eq_zero_of_dvd hN2div
   have hJ2mod : (N2/((2:Int)^beta))%((8:Int)^v)=0 := by
     rw [hN2,Int.mul_assoc,Int.mul_ediv_cancel_left _ hbpos]
     exact Int.emod_eq_zero_of_dvd ⟨(C3:Int)*(2^n:Int)-(R3:Int)+
       ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)-
         ((2:Int)^delta)*(8:Int)^r*(E:Int)),by ac_rfl⟩
   have hN3div : ((2:Int)^gamma) ∣ N3 := by
     rw [hN3]
     exact ⟨(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)-
       ((2:Int)^delta)*(8:Int)^r*(E:Int)),by ac_rfl⟩
   have hN3mod : N3%((2:Int)^gamma)=0 := Int.emod_eq_zero_of_dvd hN3div
   have hJ3mod : (N3/((2:Int)^gamma))%((8:Int)^w)=0 := by
     rw [hN3,Int.mul_assoc,Int.mul_ediv_cancel_left _ (Int.pow_ne_zero (by decide : (2:Int)≠0))]
     exact Int.emod_eq_zero_of_dvd ⟨(C4:Int)*(2^n:Int)-(R4:Int)-
       ((2:Int)^delta)*(8:Int)^r*(E:Int),by ac_rfl⟩
   have hN4div : ((2:Int)^delta*512) ∣ N4 := by
     rw [hN4,hr8]
     refine ⟨-((8:Int)^(r-3)*(E:Int)), ?_⟩
     simp only [Int.mul_neg,Int.neg_mul]
     ac_rfl
   have hN4mod : N4%((2:Int)^delta*512)=0 := Int.emod_eq_zero_of_dvd hN4div
   have hfourth : fourthOverflow n s u v w t1 t2 t3 t4 = true := by
     have htt1 : triple t1=(alpha,C1,L1,O1) := hprofile1.symm
     have htt2 : triple t2=(beta,C2,L2,O2) := hprofile2.symm
     have htt3 : triple t3=(gamma,C3,L3,O3) := hprofile3.symm
     have htt4 : triple t4=(delta,C4,L4,O4) := hprofile4.symm
     simp [fourthOverflow,hmodP,hmodD,htt1,htt2,htt3,htt4,
       hpDiv,hdDiv,hN1mod,hJ1mod,hN2mod,hJ2mod,hN3mod,hJ3mod,hN4mod,
       N1,N2,N3,N4,Imid1,Imid2,Imid3]
   have hF : fourthOverflow n s u v w t1 t2 t3 t4 = false := by
     have hh := four_fourth_overflow_false_76
       (⟨n-14,by omega⟩ : Fin 62) (⟨s,by omega⟩ : Fin 4)
       (⟨u,by omega⟩ : Fin 3) (⟨v,by omega⟩ : Fin 3) (⟨w,by omega⟩ : Fin 3)
       (⟨t1,by omega⟩ : Fin 2) (⟨t2,by omega⟩ : Fin 2)
       (⟨t3,by omega⟩ : Fin 2) (⟨t4,by omega⟩ : Fin 2)
     simpa [Fin.val,Nat.sub_add_cancel hn14] using hh
   rw [hfourth] at hF
   contradiction

/-- The exact four-shallow terminal wall equation is impossible throughout
the remaining finite range 14<=n<76, with all five depth-two runs initially
unrestricted. -/
theorem no_four_small_numeric
 (n s u v w r t1 t2 t3 t4 p d alpha beta gamma delta
  C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4 K R1 R2 R3 R4 E : Nat)
 (hn14 : 14≤n) (hn76 : n<76) (hs : s≤3)
 (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1) (ht4 : t4≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hprofile2 : (beta,C2,L2,O2)=triple t2)
 (hprofile3 : (gamma,C3,L3,O3)=triple t3)
 (hprofile4 : (delta,C4,L4,O4)=triple t4)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*r))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*
   ((2^gamma*8^w)*((2^delta*8^r)*E+R4)+R3)+R2)+R1) : False := by
 have hu := num_four_small_u_bound n s u v w r t1 t2 t3 t4 p d
   alpha beta gamma delta C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4
   K R1 R2 R3 R4 E hn14 hn76 hs ht1 hprofile1 hP hD hR1 hR2 hR3 hR4 hK hEq
 have hv := num_four_small_v_bound n s u v w r t1 t2 t3 t4 p d
   alpha beta gamma delta C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4
   K R1 R2 R3 R4 E hn14 hn76 hs ht1 ht2 hprofile1 hprofile2
   hP hD hR1 hR2 hR3 hR4 hK hEq
 have hw := num_four_small_w_bound n s u v w r t1 t2 t3 t4 p d
   alpha beta gamma delta C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4
   K R1 R2 R3 R4 E hn14 hn76 hs ht1 ht2 ht3 hprofile1 hprofile2 hprofile3
   hP hD hR1 hR2 hR3 hR4 hK hEq
 have hr := num_four_small_r_bound n s u v w r t1 t2 t3 t4 p d
   alpha beta gamma delta C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4
   K R1 R2 R3 R4 E hn14 hn76 hs ht1 ht2 ht3 ht4
   hprofile1 hprofile2 hprofile3 hprofile4 hP hD hR1 hR2 hR3 hR4 hE hK hEq
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
 have hR4nat : L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w)-O4=R4 := by omega
 have hEnat : 112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*r)-384=E := by omega
 have hKnat : C1*8^s+C2*8^s*(2^alpha*8^u)+
     C3*8^s*(2^alpha*8^u)*(2^beta*8^v)+
     C4*8^s*(2^alpha*8^u)*(2^beta*8^v)*(2^gamma*8^w)-98=K := by
   have hh : K+98=C1*8^s+C2*8^s*(2^alpha*8^u)+
       C3*8^s*(2^alpha*8^u)*(2^beta*8^v)+
       C4*8^s*(2^alpha*8^u)*(2^beta*8^v)*(2^gamma*8^w) := by
     simpa only [Nat.mul_assoc] using hK
   omega
 have hBad : fourBad n s u v w r t1 t2 t3 t4 = true := by
   simp [fourBad,hmodP,hmodD,hprofile1.symm,hprofile2.symm,
     hprofile3.symm,hprofile4.symm,hpDiv,hdDiv,hR1nat,hR2nat,hR3nat,
     hR4nat,hEnat,hKnat,hEq]
 have hF : fourBad n s u v w r t1 t2 t3 t4 = false := by
   have hh := no_four_small_bad_76
     (⟨n-14,by omega⟩ : Fin 62) (⟨s,by omega⟩ : Fin 4)
     (⟨u,by omega⟩ : Fin 3) (⟨v,by omega⟩ : Fin 3)
     (⟨w,by omega⟩ : Fin 3) (⟨r,by omega⟩ : Fin 3)
     (⟨t1,by omega⟩ : Fin 2) (⟨t2,by omega⟩ : Fin 2)
     (⟨t3,by omega⟩ : Fin 2) (⟨t4,by omega⟩ : Fin 2)
   simpa [Fin.val,Nat.sub_add_cancel hn14] using hh
 rw [hBad] at hF
 contradiction

#print axioms num_four_small_u_bound
#print axioms num_four_small_v_bound
#print axioms num_four_small_w_bound
#print axioms num_four_small_r_bound
#print axioms no_four_small_numeric

end BB6.Agent43FourShallowFiniteBridge
