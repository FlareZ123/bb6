import FiveShallowIntegerAlgebra
import FiveShallowOverflowBounds
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43FiveShallowFiniteBridge

open BB6.Agent43TwoShallowFinite
open BB6.Agent43ThreeShallowFinite
open BB6.Agent43FourShallowFinite
open BB6.Agent43FiveShallowFinite
open BB6.Agent43FiveShallowOverflow

set_option maxRecDepth 4096
set_option maxHeartbeats 12000000

/-- The five exact source numerators factor successively by the five
shallow factors. This packages the algebraic telescoping identity together
with the five source remainder equations. -/
theorem five_numerator_factorizations
 (n s u v w x r alpha beta gamma delta epsilon p d
  C1 C2 C3 C4 C5 L1 L2 L3 L4 L5 O1 O2 O3 O4 O5
  K R1 R2 R3 R4 R5 E : Nat)
 (hP : (8:Nat)^s*p=2^n)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hR5 : R5+O5=L5*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w)))+
   C5*(8^s*((((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))*(2^delta*8^x))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*
   ((2^gamma*8^w)*((2^delta*8^x)*((2^epsilon*8^r)*E+R5)+R4)+R3)+R2)+R1) :
 ∃ N1 N2 N3 N4 N5 X1 X2 X3 X4 : Int,
   N1=98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
       (L1:Int)*(n+6+3*s:Int)-(O1:Int) ∧
   N2=(N1/((2:Int)^alpha))/((8:Int)^u)-(C2:Int)*(2^n:Int)+
       (L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int) ∧
   N3=(N2/((2:Int)^beta))/((8:Int)^v)-(C3:Int)*(2^n:Int)+
       (L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int)-(O3:Int) ∧
   N4=(N3/((2:Int)^gamma))/((8:Int)^w)-(C4:Int)*(2^n:Int)+
       (L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int)-(O4:Int) ∧
   N5=(N4/((2:Int)^delta))/((8:Int)^x)-(C5:Int)*(2^n:Int)+
       (L5:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x:Int)-(O5:Int) ∧
   N1=(2:Int)^alpha*(8:Int)^u*X1 ∧
   N2=(2:Int)^beta*(8:Int)^v*X2 ∧
   N3=(2:Int)^gamma*(8:Int)^w*X3 ∧
   N4=(2:Int)^delta*(8:Int)^x*X4 ∧
   N5=-((2:Int)^epsilon*(8:Int)^r*(E:Int)) := by
  let A1 : Int := (2:Int)^alpha*(8:Int)^u
  let A2 : Int := (2:Int)^beta*(8:Int)^v
  let A3 : Int := (2:Int)^gamma*(8:Int)^w
  let A4 : Int := (2:Int)^delta*(8:Int)^x
  let A5 : Int := (2:Int)^epsilon*(8:Int)^r
  let X1 : Int := (C2:Int)*(2^n:Int)-(R2:Int)+
    ((2:Int)^beta)*(8:Int)^v*((C3:Int)*(2^n:Int)-(R3:Int)+
      ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)+
        ((2:Int)^delta)*(8:Int)^x*((C5:Int)*(2^n:Int)-(R5:Int)-
          ((2:Int)^epsilon)*(8:Int)^r*(E:Int))))
  let X2 : Int := (C3:Int)*(2^n:Int)-(R3:Int)+
    ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)+
      ((2:Int)^delta)*(8:Int)^x*((C5:Int)*(2^n:Int)-(R5:Int)-
        ((2:Int)^epsilon)*(8:Int)^r*(E:Int)))
  let X3 : Int := (C4:Int)*(2^n:Int)-(R4:Int)+
    ((2:Int)^delta)*(8:Int)^x*((C5:Int)*(2^n:Int)-(R5:Int)-
      ((2:Int)^epsilon)*(8:Int)^r*(E:Int))
  let X4 : Int := (C5:Int)*(2^n:Int)-(R5:Int)-
    ((2:Int)^epsilon)*(8:Int)^r*(E:Int)
  let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
    (L1:Int)*(n+6+3*s:Int)-(O1:Int)
  let N2 : Int := (N1/((2:Int)^alpha))/((8:Int)^u)-
    (C2:Int)*(2^n:Int)+(L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int)
  let N3 : Int := (N2/((2:Int)^beta))/((8:Int)^v)-
    (C3:Int)*(2^n:Int)+(L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int)-(O3:Int)
  let N4 : Int := (N3/((2:Int)^gamma))/((8:Int)^w)-
    (C4:Int)*(2^n:Int)+(L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int)-(O4:Int)
  let N5 : Int := (N4/((2:Int)^delta))/((8:Int)^x)-
    (C5:Int)*(2^n:Int)+
      (L5:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x:Int)-(O5:Int)
  have hAlg := BB6.Agent43FiveShallowAlgebra.algebraic_first_five
    (2^n) (8^s) p d C1 C2 C3 C4 C5 L1 O1 K R1 R2 R3 R4 R5 E
    (n+6+3*s)
    (2^alpha*8^u) (2^beta*8^v) (2^gamma*8^w) (2^delta*8^x)
    (2^epsilon*8^r) hP hR1 hK hEq
  simp at hAlg
  have hN1 : N1=A1*X1 := by
    simpa only [N1,X1,A1,A2,A3,A4,A5,Int.natCast_mul,
      Int.natCast_pow,Int.mul_assoc] using hAlg
  have hapos : (2:Int)^alpha ≠ 0 := Int.pow_ne_zero (by decide)
  have huzpos : (8:Int)^u ≠ 0 := Int.pow_ne_zero (by decide)
  have hbpos : (2:Int)^beta ≠ 0 := Int.pow_ne_zero (by decide)
  have hvzpos : (8:Int)^v ≠ 0 := Int.pow_ne_zero (by decide)
  have hcpos : (2:Int)^gamma ≠ 0 := Int.pow_ne_zero (by decide)
  have hwzpos : (8:Int)^w ≠ 0 := Int.pow_ne_zero (by decide)
  have hfpos : (2:Int)^delta ≠ 0 := Int.pow_ne_zero (by decide)
  have hxzpos : (8:Int)^x ≠ 0 := Int.pow_ne_zero (by decide)
  have hImid1 : (N1/((2:Int)^alpha))/((8:Int)^u)=X1 := by
    rw [hN1,Int.mul_assoc,Int.mul_ediv_cancel_left _ hapos]
    exact Int.mul_ediv_cancel_left X1 huzpos
  have hR2i : (R2:Int)+(O2:Int)=
      (L2:Int)*(n+6+3*s+alpha+3*u:Int) := by exact_mod_cast hR2
  have hN2 : N2=A2*X2 := by
    dsimp [N2]
    rw [hImid1]
    dsimp [X1,X2,A2,A3,A4,A5]
    rw [←hR2i]
    omega
  have hImid2 : (N2/((2:Int)^beta))/((8:Int)^v)=X2 := by
    rw [hN2,Int.mul_assoc,Int.mul_ediv_cancel_left _ hbpos]
    exact Int.mul_ediv_cancel_left X2 hvzpos
  have hR3i : (R3:Int)+(O3:Int)=
      (L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int) := by exact_mod_cast hR3
  have hN3 : N3=A3*X3 := by
    dsimp [N3]
    rw [hImid2]
    dsimp [X2,X3,A3,A4,A5]
    rw [←hR3i]
    omega
  have hImid3 : (N3/((2:Int)^gamma))/((8:Int)^w)=X3 := by
    rw [hN3,Int.mul_assoc,Int.mul_ediv_cancel_left _ hcpos]
    exact Int.mul_ediv_cancel_left X3 hwzpos
  have hR4i : (R4:Int)+(O4:Int)=
      (L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int) := by
    exact_mod_cast hR4
  have hN4 : N4=A4*X4 := by
    dsimp [N4]
    rw [hImid3]
    dsimp [X3,X4,A4,A5]
    rw [←hR4i]
    omega
  have hImid4 : (N4/((2:Int)^delta))/((8:Int)^x)=X4 := by
    rw [hN4,Int.mul_assoc,Int.mul_ediv_cancel_left _ hfpos]
    exact Int.mul_ediv_cancel_left X4 hxzpos
  have hR5i : (R5:Int)+(O5:Int)=
      (L5:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x:Int) := by
    exact_mod_cast hR5
  have hN5 : N5=-((2:Int)^epsilon*(8:Int)^r*(E:Int)) := by
    dsimp [N5]
    rw [hImid4]
    dsimp [X4,A5]
    rw [←hR5i]
    omega
  refine ⟨N1,N2,N3,N4,N5,X1,X2,X3,X4,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simpa [A1] using hN1
  · simpa [A2] using hN2
  · simpa [A3] using hN3
  · simpa [A4] using hN4
  · exact hN5

end BB6.Agent43FiveShallowFiniteBridge


/-- On 14<=n<83, the exact first-through-fifth overflow tables force all
five depth-two runs between the five shallow transitions to have length at
most two. -/
theorem num_five_small_run_bounds
 (n s u v w x r t1 t2 t3 t4 t5 p d
  alpha beta gamma delta epsilon
  C1 C2 C3 C4 C5 L1 L2 L3 L4 L5 O1 O2 O3 O4 O5
  K R1 R2 R3 R4 R5 E : Nat)
 (hn14 : 14≤n) (hn83 : n<83) (hs : s≤3)
 (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1)
 (ht4 : t4≤1) (ht5 : t5≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hprofile2 : (beta,C2,L2,O2)=triple t2)
 (hprofile3 : (gamma,C3,L3,O3)=triple t3)
 (hprofile4 : (delta,C4,L4,O4)=triple t4)
 (hprofile5 : (epsilon,C5,L5,O5)=triple t5)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hR5 : R5+O5=L5*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w)))+
   C5*(8^s*((((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))*(2^delta*8^x))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*
   ((2^gamma*8^w)*((2^delta*8^x)*((2^epsilon*8^r)*E+R5)+R4)+R3)+R2)+R1) :
   u≤2 ∧ v≤2 ∧ w≤2 ∧ x≤2 ∧ r≤2 := by
  have hmodP : 2^n % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨p,hP.symm⟩
  have hmodD : (14*n+92) % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨d,hD.symm⟩
  have hpDiv : 2^n / 8^s = p := by
    rw [←hP]
    exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
  have hdDiv : (14*n+92) / 8^s = d := by
    rw [←hD]
    exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
  have hroot : (n,s) ∈ rootPairs := by
    have hh := rootPairs_complete
      (⟨n-14,by omega⟩ : Fin 69) (⟨s,by omega⟩ : Fin 4)
    simpa [Fin.val,Nat.sub_add_cancel hn14] using hh hmodD
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hroot
  obtain ⟨N1,N2,N3,N4,N5,X1,X2,X3,X4,
    hN1def,hN2def,hN3def,hN4def,hN5def,
    hN1fac,hN2fac,hN3fac,hN4fac,hN5fac⟩ :=
    five_numerator_factorizations n s u v w x r alpha beta gamma delta epsilon
      p d C1 C2 C3 C4 C5 L1 L2 L3 L4 L5 O1 O2 O3 O4 O5
      K R1 R2 R3 R4 R5 E hP hR1 hR2 hR3 hR4 hR5 hK hEq
  have hapos : (2:Int)^alpha ≠ 0 := Int.pow_ne_zero (by decide)
  have huzpos : (8:Int)^u ≠ 0 := Int.pow_ne_zero (by decide)
  have hbpos : (2:Int)^beta ≠ 0 := Int.pow_ne_zero (by decide)
  have hvzpos : (8:Int)^v ≠ 0 := Int.pow_ne_zero (by decide)
  have hcpos : (2:Int)^gamma ≠ 0 := Int.pow_ne_zero (by decide)
  have hwzpos : (8:Int)^w ≠ 0 := Int.pow_ne_zero (by decide)
  have hfpos : (2:Int)^delta ≠ 0 := Int.pow_ne_zero (by decide)
  have hxzpos : (8:Int)^x ≠ 0 := Int.pow_ne_zero (by decide)
  have hN1mod : N1 % ((2:Int)^alpha) = 0 := by
    rw [hN1fac]
    exact Int.emod_eq_zero_of_dvd ⟨(8:Int)^u*X1,by ac_rfl⟩
  have hJ1mod : (N1/((2:Int)^alpha)) % ((8:Int)^u) = 0 := by
    rw [hN1fac,Int.mul_assoc,Int.mul_ediv_cancel_left _ hapos]
    exact Int.emod_eq_zero_of_dvd ⟨X1,by ac_rfl⟩
  have hN2mod : N2 % ((2:Int)^beta) = 0 := by
    rw [hN2fac]
    exact Int.emod_eq_zero_of_dvd ⟨(8:Int)^v*X2,by ac_rfl⟩
  have hJ2mod : (N2/((2:Int)^beta)) % ((8:Int)^v) = 0 := by
    rw [hN2fac,Int.mul_assoc,Int.mul_ediv_cancel_left _ hbpos]
    exact Int.emod_eq_zero_of_dvd ⟨X2,by ac_rfl⟩
  have hN3mod : N3 % ((2:Int)^gamma) = 0 := by
    rw [hN3fac]
    exact Int.emod_eq_zero_of_dvd ⟨(8:Int)^w*X3,by ac_rfl⟩
  have hJ3mod : (N3/((2:Int)^gamma)) % ((8:Int)^w) = 0 := by
    rw [hN3fac,Int.mul_assoc,Int.mul_ediv_cancel_left _ hcpos]
    exact Int.emod_eq_zero_of_dvd ⟨X3,by ac_rfl⟩
  have hN4mod : N4 % ((2:Int)^delta) = 0 := by
    rw [hN4fac]
    exact Int.emod_eq_zero_of_dvd ⟨(8:Int)^x*X4,by ac_rfl⟩
  have hJ4mod : (N4/((2:Int)^delta)) % ((8:Int)^x) = 0 := by
    rw [hN4fac,Int.mul_assoc,Int.mul_ediv_cancel_left _ hfpos]
    exact Int.emod_eq_zero_of_dvd ⟨X4,by ac_rfl⟩

  have huBound : u≤2 := by
    by_contra h
    have hu3 : 3≤u := by omega
    have hu8 : (8:Int)^u=512*(8:Int)^(u-3) := by
      have he : u=3+(u-3) := by omega
      calc
        (8:Int)^u=(8:Int)^(3+(u-3)) := congrArg (fun z:Nat=>(8:Int)^z) he
        _=(8:Int)^3*(8:Int)^(u-3) := by rw [Int.pow_add]
        _=512*(8:Int)^(u-3) := by rw [show (8:Int)^3=512 by decide]
    have hDiv : ((2:Int)^alpha*512) ∣ N1 := by
      rw [hN1fac,hu8]
      refine ⟨(8:Int)^(u-3)*X1,?_⟩
      ac_rfl
    have hN1overflow : N1 % ((2:Int)^alpha*512)=0 :=
      Int.emod_eq_zero_of_dvd hDiv
    have hfirst : BB6.Agent43TwoShallowFinite.firstOverflow n s t1 = true := by
      have htt1 : triple t1=(alpha,C1,L1,O1) := hprofile1.symm
      simp [BB6.Agent43TwoShallowFinite.firstOverflow,hmodP,hmodD,
        htt1,hpDiv,hdDiv,←hN1def,hN1overflow]
    have hF : BB6.Agent43TwoShallowFinite.firstOverflow n s t1 = false := by
      have hh := five_first_overflow_false i ⟨t1,by omega⟩
      simpa [hi] using hh
    rw [hfirst] at hF
    contradiction

  have hvBound : v≤2 := by
    by_contra h
    have hv3 : 3≤v := by omega
    have hv8 : (8:Int)^v=512*(8:Int)^(v-3) := by
      have he : v=3+(v-3) := by omega
      calc
        (8:Int)^v=(8:Int)^(3+(v-3)) := congrArg (fun z:Nat=>(8:Int)^z) he
        _=(8:Int)^3*(8:Int)^(v-3) := by rw [Int.pow_add]
        _=512*(8:Int)^(v-3) := by rw [show (8:Int)^3=512 by decide]
    have hDiv : ((2:Int)^beta*512) ∣ N2 := by
      rw [hN2fac,hv8]
      refine ⟨(8:Int)^(v-3)*X2,?_⟩
      ac_rfl
    have hN2overflow : N2 % ((2:Int)^beta*512)=0 :=
      Int.emod_eq_zero_of_dvd hDiv
    have hsecond : BB6.Agent43TwoShallowFinite.secondOverflow n s u t1 t2 = true := by
      have htt1 : triple t1=(alpha,C1,L1,O1) := hprofile1.symm
      have htt2 : triple t2=(beta,C2,L2,O2) := hprofile2.symm
      simp [BB6.Agent43TwoShallowFinite.secondOverflow,hmodP,hmodD,
        htt1,htt2,hpDiv,hdDiv,hN1mod,hJ1mod,hN2overflow,
        ←hN1def,←hN2def]
    have hF : BB6.Agent43TwoShallowFinite.secondOverflow n s u t1 t2 = false := by
      have hh := five_second_overflow_false i ⟨u,huBound⟩
        ⟨t1,by omega⟩ ⟨t2,by omega⟩
      simpa [hi] using hh
    rw [hsecond] at hF
    contradiction

  have hwBound : w≤2 := by
    by_contra h
    have hw3 : 3≤w := by omega
    have hw8 : (8:Int)^w=512*(8:Int)^(w-3) := by
      have he : w=3+(w-3) := by omega
      calc
        (8:Int)^w=(8:Int)^(3+(w-3)) := congrArg (fun z:Nat=>(8:Int)^z) he
        _=(8:Int)^3*(8:Int)^(w-3) := by rw [Int.pow_add]
        _=512*(8:Int)^(w-3) := by rw [show (8:Int)^3=512 by decide]
    have hDiv : ((2:Int)^gamma*512) ∣ N3 := by
      rw [hN3fac,hw8]
      refine ⟨(8:Int)^(w-3)*X3,?_⟩
      ac_rfl
    have hN3overflow : N3 % ((2:Int)^gamma*512)=0 :=
      Int.emod_eq_zero_of_dvd hDiv
    have hthird : BB6.Agent43ThreeShallowFinite.thirdOverflow n s u v t1 t2 t3 = true := by
      have htt1 : triple t1=(alpha,C1,L1,O1) := hprofile1.symm
      have htt2 : triple t2=(beta,C2,L2,O2) := hprofile2.symm
      have htt3 : triple t3=(gamma,C3,L3,O3) := hprofile3.symm
      simp [BB6.Agent43ThreeShallowFinite.thirdOverflow,hmodP,hmodD,
        htt1,htt2,htt3,hpDiv,hdDiv,hN1mod,hJ1mod,hN2mod,hJ2mod,
        hN3overflow,←hN1def,←hN2def,←hN3def]
    have hF : BB6.Agent43ThreeShallowFinite.thirdOverflow n s u v t1 t2 t3 = false := by
      have hh := five_third_overflow_false i ⟨u,huBound⟩ ⟨v,hvBound⟩
        ⟨t1,by omega⟩ ⟨t2,by omega⟩ ⟨t3,by omega⟩
      simpa [hi] using hh
    rw [hthird] at hF
    contradiction

  have hxBound : x≤2 := by
    by_contra h
    have hx3 : 3≤x := by omega
    have hx8 : (8:Int)^x=512*(8:Int)^(x-3) := by
      have he : x=3+(x-3) := by omega
      calc
        (8:Int)^x=(8:Int)^(3+(x-3)) := congrArg (fun z:Nat=>(8:Int)^z) he
        _=(8:Int)^3*(8:Int)^(x-3) := by rw [Int.pow_add]
        _=512*(8:Int)^(x-3) := by rw [show (8:Int)^3=512 by decide]
    have hDiv : ((2:Int)^delta*512) ∣ N4 := by
      rw [hN4fac,hx8]
      refine ⟨(8:Int)^(x-3)*X4,?_⟩
      ac_rfl
    have hN4overflow : N4 % ((2:Int)^delta*512)=0 :=
      Int.emod_eq_zero_of_dvd hDiv
    have hfourth : BB6.Agent43FourShallowFinite.fourthOverflow n s u v w t1 t2 t3 t4 = true := by
      have htt1 : triple t1=(alpha,C1,L1,O1) := hprofile1.symm
      have htt2 : triple t2=(beta,C2,L2,O2) := hprofile2.symm
      have htt3 : triple t3=(gamma,C3,L3,O3) := hprofile3.symm
      have htt4 : triple t4=(delta,C4,L4,O4) := hprofile4.symm
      simp [BB6.Agent43FourShallowFinite.fourthOverflow,hmodP,hmodD,
        htt1,htt2,htt3,htt4,hpDiv,hdDiv,hN1mod,hJ1mod,hN2mod,hJ2mod,
        hN3mod,hJ3mod,hN4overflow,←hN1def,←hN2def,←hN3def,←hN4def]
    have hF : BB6.Agent43FourShallowFinite.fourthOverflow n s u v w t1 t2 t3 t4 = false := by
      have hh := five_fourth_overflow_false i ⟨u,huBound⟩ ⟨v,hvBound⟩
        ⟨w,hwBound⟩ ⟨t1,by omega⟩ ⟨t2,by omega⟩
        ⟨t3,by omega⟩ ⟨t4,by omega⟩
      simpa [hi] using hh
    rw [hfourth] at hF
    contradiction

  have hrBound : r≤2 := by
    by_contra h
    have hr3 : 3≤r := by omega
    have hr8 : (8:Int)^r=512*(8:Int)^(r-3) := by
      have he : r=3+(r-3) := by omega
      calc
        (8:Int)^r=(8:Int)^(3+(r-3)) := congrArg (fun z:Nat=>(8:Int)^z) he
        _=(8:Int)^3*(8:Int)^(r-3) := by rw [Int.pow_add]
        _=512*(8:Int)^(r-3) := by rw [show (8:Int)^3=512 by decide]
    have hDiv : ((2:Int)^epsilon*512) ∣ N5 := by
      rw [hN5fac,hr8]
      refine ⟨-((8:Int)^(r-3)*(E:Int)),?_⟩
      simp only [Int.mul_neg,Int.neg_mul]
      ac_rfl
    have hN5overflow : N5 % ((2:Int)^epsilon*512)=0 :=
      Int.emod_eq_zero_of_dvd hDiv
    have hfifth : fifthOverflow n s u v w x t1 t2 t3 t4 t5 = true := by
      have htt1 : triple t1=(alpha,C1,L1,O1) := hprofile1.symm
      have htt2 : triple t2=(beta,C2,L2,O2) := hprofile2.symm
      have htt3 : triple t3=(gamma,C3,L3,O3) := hprofile3.symm
      have htt4 : triple t4=(delta,C4,L4,O4) := hprofile4.symm
      have htt5 : triple t5=(epsilon,C5,L5,O5) := hprofile5.symm
      simp [fifthOverflow,hmodP,hmodD,htt1,htt2,htt3,htt4,htt5,
        hpDiv,hdDiv,hN1mod,hJ1mod,hN2mod,hJ2mod,hN3mod,hJ3mod,
        hN4mod,hJ4mod,hN5overflow,
        ←hN1def,←hN2def,←hN3def,←hN4def,←hN5def]
    have hF : fifthOverflow n s u v w x t1 t2 t3 t4 t5 = false := by
      have hh := five_fifth_overflow_false i
        ⟨u,huBound⟩ ⟨v,hvBound⟩ ⟨w,hwBound⟩ ⟨x,hxBound⟩
        ⟨t1,by omega⟩ ⟨t2,by omega⟩ ⟨t3,by omega⟩
        ⟨t4,by omega⟩ ⟨t5,by omega⟩
      simpa [hi] using hh
    rw [hfifth] at hF
    contradiction

  exact ⟨huBound,hvBound,hwBound,hxBound,hrBound⟩


/-- The source scalar equation forces the recurrence predicate used
by the finite certificate. The numerator factorizations are precisely the
successive shallow and depth-two divisibility conditions. -/
theorem fiveBad_true_of_scalar_equation
 (n s u v w x r t1 t2 t3 t4 t5 p d
  alpha beta gamma delta epsilon
  C1 C2 C3 C4 C5 L1 L2 L3 L4 L5 O1 O2 O3 O4 O5
  K R1 R2 R3 R4 R5 E : Nat)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1)
 (ht4 : t4≤1) (ht5 : t5≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hprofile2 : (beta,C2,L2,O2)=triple t2)
 (hprofile3 : (gamma,C3,L3,O3)=triple t3)
 (hprofile4 : (delta,C4,L4,O4)=triple t4)
 (hprofile5 : (epsilon,C5,L5,O5)=triple t5)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hR5 : R5+O5=L5*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x))
 (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x+epsilon+3*r))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w)))+
   C5*(8^s*((((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))*(2^delta*8^x))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*
   ((2^gamma*8^w)*((2^delta*8^x)*((2^epsilon*8^r)*E+R5)+R4)+R3)+R2)+R1) :
   fiveBad n s u v w x r t1 t2 t3 t4 t5 = true := by
  have hmodP : 2^n % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨p,hP.symm⟩
  have hmodD : (14*n+92) % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨d,hD.symm⟩
  have hpDiv : 2^n / 8^s = p := by
    rw [←hP]
    exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
  have hdDiv : (14*n+92) / 8^s = d := by
    rw [←hD]
    exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
  obtain ⟨N1,N2,N3,N4,N5,X1,X2,X3,X4,
    hN1def,hN2def,hN3def,hN4def,hN5def,
    hN1fac,hN2fac,hN3fac,hN4fac,hN5fac⟩ :=
    five_numerator_factorizations n s u v w x r alpha beta gamma delta epsilon
      p d C1 C2 C3 C4 C5 L1 L2 L3 L4 L5 O1 O2 O3 O4 O5
      K R1 R2 R3 R4 R5 E hP hR1 hR2 hR3 hR4 hR5 hK hEq
  have hapos : (2:Int)^alpha ≠ 0 := Int.pow_ne_zero (by decide)
  have huzpos : (8:Int)^u ≠ 0 := Int.pow_ne_zero (by decide)
  have hbpos : (2:Int)^beta ≠ 0 := Int.pow_ne_zero (by decide)
  have hvzpos : (8:Int)^v ≠ 0 := Int.pow_ne_zero (by decide)
  have hcpos : (2:Int)^gamma ≠ 0 := Int.pow_ne_zero (by decide)
  have hwzpos : (8:Int)^w ≠ 0 := Int.pow_ne_zero (by decide)
  have hfpos : (2:Int)^delta ≠ 0 := Int.pow_ne_zero (by decide)
  have hxzpos : (8:Int)^x ≠ 0 := Int.pow_ne_zero (by decide)
  have hepos : (2:Int)^epsilon ≠ 0 := Int.pow_ne_zero (by decide)
  have hrpos : (8:Int)^r ≠ 0 := Int.pow_ne_zero (by decide)
  have hN1mod : N1 % ((2:Int)^alpha)=0 := by
    rw [hN1fac]
    exact Int.emod_eq_zero_of_dvd ⟨(8:Int)^u*X1,by ac_rfl⟩
  have hJ1mod : (N1/((2:Int)^alpha)) % ((8:Int)^u)=0 := by
    rw [hN1fac,Int.mul_assoc,Int.mul_ediv_cancel_left _ hapos]
    exact Int.emod_eq_zero_of_dvd ⟨X1,by ac_rfl⟩
  have hN2mod : N2 % ((2:Int)^beta)=0 := by
    rw [hN2fac]
    exact Int.emod_eq_zero_of_dvd ⟨(8:Int)^v*X2,by ac_rfl⟩
  have hJ2mod : (N2/((2:Int)^beta)) % ((8:Int)^v)=0 := by
    rw [hN2fac,Int.mul_assoc,Int.mul_ediv_cancel_left _ hbpos]
    exact Int.emod_eq_zero_of_dvd ⟨X2,by ac_rfl⟩
  have hN3mod : N3 % ((2:Int)^gamma)=0 := by
    rw [hN3fac]
    exact Int.emod_eq_zero_of_dvd ⟨(8:Int)^w*X3,by ac_rfl⟩
  have hJ3mod : (N3/((2:Int)^gamma)) % ((8:Int)^w)=0 := by
    rw [hN3fac,Int.mul_assoc,Int.mul_ediv_cancel_left _ hcpos]
    exact Int.emod_eq_zero_of_dvd ⟨X3,by ac_rfl⟩
  have hN4mod : N4 % ((2:Int)^delta)=0 := by
    rw [hN4fac]
    exact Int.emod_eq_zero_of_dvd ⟨(8:Int)^x*X4,by ac_rfl⟩
  have hJ4mod : (N4/((2:Int)^delta)) % ((8:Int)^x)=0 := by
    rw [hN4fac,Int.mul_assoc,Int.mul_ediv_cancel_left _ hfpos]
    exact Int.emod_eq_zero_of_dvd ⟨X4,by ac_rfl⟩
  have hN5prod : N5=(2:Int)^epsilon*(-((8:Int)^r*(E:Int))) := by
    rw [hN5fac]
    rw [Int.mul_neg,Int.mul_assoc]
  have hN5mod : N5 % ((2:Int)^epsilon)=0 := by
    have hdiv : (2:Int)^epsilon ∣ N5 :=
      ⟨-((8:Int)^r*(E:Int)),hN5prod⟩
    exact Int.emod_eq_zero_of_dvd hdiv
  have hJ5eq : N5/((2:Int)^epsilon)=-((8:Int)^r*(E:Int)) := by
    rw [hN5prod,Int.mul_ediv_cancel_left _ hepos]
  have hJ5eq' : N5/((2:Int)^epsilon)=(8:Int)^r*(-(E:Int)) := by
    rw [hJ5eq,←Int.mul_neg]
  have hJ5mod : (N5/((2:Int)^epsilon)) % ((8:Int)^r)=0 := by
    rw [hJ5eq']
    exact Int.emod_eq_zero_of_dvd ⟨-(E:Int),by ac_rfl⟩
  have hJ5div : ((N5/((2:Int)^epsilon))/((8:Int)^r))=-(E:Int) := by
    rw [hJ5eq',Int.mul_ediv_cancel_left _ hrpos]
  have hEnat :
      112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x+epsilon+3*r)-384=E := by
    omega
  have htt1 : triple t1=(alpha,C1,L1,O1) := hprofile1.symm
  have htt2 : triple t2=(beta,C2,L2,O2) := hprofile2.symm
  have htt3 : triple t3=(gamma,C3,L3,O3) := hprofile3.symm
  have htt4 : triple t4=(delta,C4,L4,O4) := hprofile4.symm
  have htt5 : triple t5=(epsilon,C5,L5,O5) := hprofile5.symm
  simp [fiveBad,hmodP,hmodD,hpDiv,hdDiv,htt1,htt2,htt3,htt4,htt5,
    ←hN1def,←hN2def,←hN3def,←hN4def,←hN5def,
    hN1mod,hJ1mod,hN2mod,hJ2mod,hN3mod,hJ3mod,
    hN4mod,hJ4mod,hN5mod,hJ5mod,hJ5div,hEnat]

/-- No exact five-shallow source-wall equation exists in the finite
index range 14<=n<83. The overflow certificates bound every intervening
depth-two run by two, after which the residual finite table applies. -/
theorem no_five_small_numeric
 (n s u v w x r t1 t2 t3 t4 t5 p d
  alpha beta gamma delta epsilon
  C1 C2 C3 C4 C5 L1 L2 L3 L4 L5 O1 O2 O3 O4 O5
  K R1 R2 R3 R4 R5 E : Nat)
 (hn14 : 14≤n) (hn83 : n<83) (hs : s≤3)
 (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1)
 (ht4 : t4≤1) (ht5 : t5≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hprofile2 : (beta,C2,L2,O2)=triple t2)
 (hprofile3 : (gamma,C3,L3,O3)=triple t3)
 (hprofile4 : (delta,C4,L4,O4)=triple t4)
 (hprofile5 : (epsilon,C5,L5,O5)=triple t5)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hR5 : R5+O5=L5*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x))
 (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x+epsilon+3*r))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w)))+
   C5*(8^s*((((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))*(2^delta*8^x))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*
   ((2^gamma*8^w)*((2^delta*8^x)*((2^epsilon*8^r)*E+R5)+R4)+R3)+R2)+R1) :
   False := by
  have hbounds := num_five_small_run_bounds
    n s u v w x r t1 t2 t3 t4 t5 p d
    alpha beta gamma delta epsilon
    C1 C2 C3 C4 C5 L1 L2 L3 L4 L5 O1 O2 O3 O4 O5
    K R1 R2 R3 R4 R5 E hn14 hn83 hs ht1 ht2 ht3 ht4 ht5
    hprofile1 hprofile2 hprofile3 hprofile4 hprofile5
    hP hD hR1 hR2 hR3 hR4 hR5 hK hEq
  rcases hbounds with ⟨hu,hv,hw,hx,hr⟩
  have hmodP : 2^n % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨p,hP.symm⟩
  have hmodD : (14*n+92) % 8^s = 0 := Nat.mod_eq_zero_of_dvd ⟨d,hD.symm⟩
  have hpDiv : 2^n / 8^s = p := by
    rw [←hP]
    exact Nat.mul_div_cancel_left p (Nat.pow_pos (by decide))
  have hdDiv : (14*n+92) / 8^s = d := by
    rw [←hD]
    exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))
  have hroot : (n,s) ∈ rootPairs := by
    have hh := rootPairs_complete
      (⟨n-14,by omega⟩ : Fin 69) (⟨s,by omega⟩ : Fin 4)
    simpa [Fin.val,Nat.sub_add_cancel hn14] using hh hmodD
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hroot
  have hBad := fiveBad_true_of_scalar_equation
    n s u v w x r t1 t2 t3 t4 t5 p d
    alpha beta gamma delta epsilon
    C1 C2 C3 C4 C5 L1 L2 L3 L4 L5 O1 O2 O3 O4 O5
    K R1 R2 R3 R4 R5 E hP hD
    ht1 ht2 ht3 ht4 ht5 hprofile1 hprofile2 hprofile3 hprofile4 hprofile5
    hR1 hR2 hR3 hR4 hR5 hE hK hEq
  have hF : fiveBad n s u v w x r t1 t2 t3 t4 t5 = false := by
    have hh := no_five_bad_rootPairs i
      ⟨t1,by omega⟩ ⟨t2,by omega⟩ ⟨t3,by omega⟩
      ⟨t4,by omega⟩ ⟨t5,by omega⟩
      ⟨u,hu⟩ ⟨v,hv⟩ ⟨w,hw⟩ ⟨x,hx⟩ ⟨r,hr⟩
    simpa [hi] using hh
  rw [hBad] at hF
  contradiction

#print axioms five_numerator_factorizations
#print axioms num_five_small_run_bounds
#print axioms no_five_small_numeric
