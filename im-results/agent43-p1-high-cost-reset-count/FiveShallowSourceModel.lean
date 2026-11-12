import FiveShallowAbstractBridge
import FiveShallowProfileBounds
import RootTwoDivisor
import TwoRunModel
import SourceOneShallowLift
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43FiveShallowSourceModel

open BB6.Agent43TwoRun BB6.Agent43FiveShallowAbstract BB6.Agent43TwoShallowFinite
open BB6.Agent43FiveLayer

set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

private theorem profile_bounds (t alpha C L O : Nat)
    (ht : t≤1) (h : (alpha,C,L,O)=triple t) :
    1≤alpha ∧ 392≤C ∧ 56≤L ∧ L≤84 ∧ O≤232 := by
  have ht' : t=0 ∨ t=1 := by omega
  rcases ht' with he|he <;> subst t <;> simp [triple] at h <;> omega

/-- Five genuine shallow transitions are connected to the original source
by six actual depth-two TwoRun segments. The theorem transports the five
affine source profiles into the five-layer scalar barrier. -/
theorem no_five_shallow_model_from_source_coefficients
 (n s u v w x r t1 t2 t3 t4 t5 alpha beta gamma delta epsilon
  C1 C2 C3 C4 C5 L1 L2 L3 L4 L5 O1 O2 O3 O4 O5 : Nat)
 (hn14 : 14≤n)
 (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1) (ht4 : t4≤1) (ht5 : t5≤1)
 (hpr1 : (alpha,C1,L1,O1)=triple t1)
 (hpr2 : (beta,C2,L2,O2)=triple t2)
 (hpr3 : (gamma,C3,L3,O3)=triple t3)
 (hpr4 : (delta,C4,L4,O4)=triple t4)
 (hpr5 : (epsilon,C5,L5,O5)=triple t5)
 (Wa Ba Wb Wc Bc Wd We Be Wf Wg Bg Wh Wi Bi Wk Wj Bj : Int)
 (hpre : TwoRun ((2:Int)^n) (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s Wa Ba)
 (hSh1 : ((2:Int)^alpha)*I ((2:Int)^n) Wb (Ba+(alpha:Int)) =
     I ((2:Int)^n) Wa Ba-(C1:Int)*(2:Int)^n+
       (L1:Int)*Ba-(O1:Int))
 (hmid1 : TwoRun ((2:Int)^n) Wb (Ba+(alpha:Int)) u Wc Bc)
 (hSh2 : ((2:Int)^beta)*I ((2:Int)^n) Wd (Bc+(beta:Int)) =
     I ((2:Int)^n) Wc Bc-(C2:Int)*(2:Int)^n+
       (L2:Int)*Bc-(O2:Int))
 (hmid2 : TwoRun ((2:Int)^n) Wd (Bc+(beta:Int)) v We Be)
 (hSh3 : ((2:Int)^gamma)*I ((2:Int)^n) Wf (Be+(gamma:Int)) =
     I ((2:Int)^n) We Be-(C3:Int)*(2:Int)^n+
       (L3:Int)*Be-(O3:Int))
 (hmid3 : TwoRun ((2:Int)^n) Wf (Be+(gamma:Int)) w Wg Bg)
 (hSh4 : ((2:Int)^delta)*I ((2:Int)^n) Wh (Bg+(delta:Int)) =
     I ((2:Int)^n) Wg Bg-(C4:Int)*(2:Int)^n+
       (L4:Int)*Bg-(O4:Int))
 (hmid4 : TwoRun ((2:Int)^n) Wh (Bg+(delta:Int)) x Wi Bi)
 (hSh5 : ((2:Int)^epsilon)*I ((2:Int)^n) Wk (Bi+(epsilon:Int)) =
     I ((2:Int)^n) Wi Bi-(C5:Int)*(2:Int)^n+
       (L5:Int)*Bi-(O5:Int))
 (hsuf : TwoRun ((2:Int)^n) Wk (Bi+(epsilon:Int)) r Wj Bj)
 (hwall : Wj=12*(2:Int)^n) : False := by
  obtain ⟨hs,hDdiv⟩ := root_two_prefix_divisor n s Wa Ba hn14 hpre
  have hpow : (8:Nat)^s=2^(3*s) := by
    simpa only [show (8:Nat)=2^3 by decide] using (Nat.pow_mul 2 3 s).symm
  have hPdiv : (8:Nat)^s ∣ 2^n := by
    rw [hpow]
    exact Nat.pow_dvd_pow 2 hs
  obtain ⟨p,hPd⟩ := hPdiv
  obtain ⟨d,hDd⟩ := hDdiv
  have hP : (8:Nat)^s*p=2^n := by simpa [Nat.mul_comm] using hPd.symm
  have hD : (8:Nat)^s*d=14*n+92 := by simpa [Nat.mul_comm] using hDd.symm
  have hqge : 1≤(8:Nat)^s := Nat.one_le_pow s 8 (by decide)
  have hdBound : d≤14*n+92 := by
    have hh := Nat.mul_le_mul_right d hqge
    rw [hD] at hh
    omega

  let T1 : Nat := n+6+3*s
  let T2 : Nat := T1+alpha+3*u
  let T3 : Nat := T2+beta+3*v
  let T4 : Nat := T3+gamma+3*w
  let T5 : Nat := T4+delta+3*x
  let T6 : Nat := T5+epsilon+3*r
  let R1 : Nat := L1*T1-O1-d
  let R2 : Nat := L2*T2-O2
  let R3 : Nat := L3*T3-O3
  let R4 : Nat := L4*T4-O4
  let R5 : Nat := L5*T5-O5
  let E : Nat := 112*T6-384
  let A1 : Nat := 2^alpha*8^u
  let A2 : Nat := 2^beta*8^v
  let A3 : Nat := 2^gamma*8^w
  let A4 : Nat := 2^delta*8^x
  let q : Nat := 8^s
  let K : Nat :=
    C1*q+C2*(q*A1)+C3*(q*(A1*A2))+C4*(q*(A1*A2*A3))+
      C5*(q*(A1*A2*A3*A4))-98

  have hR1eq : R1+O1+d=L1*T1 := by
    have hL1 := profile_bounds t1 alpha C1 L1 O1 ht1 hpr1
    have hT1 : n+6≤T1 := by dsimp [T1]; omega
    have hprod : 56*(n+6)≤L1*T1 := Nat.mul_le_mul hL1.2.2.1 hT1
    dsimp [R1]
    omega
  have hR2eq : R2+O2=L2*T2 := by
    have hL2 := profile_bounds t2 beta C2 L2 O2 ht2 hpr2
    have hT2 : n+6≤T2 := by dsimp [T2,T1]; omega
    have hprod : 56*(n+6)≤L2*T2 := Nat.mul_le_mul hL2.2.2.1 hT2
    dsimp [R2]
    omega
  have hR3eq : R3+O3=L3*T3 := by
    have hL3 := profile_bounds t3 gamma C3 L3 O3 ht3 hpr3
    have hT3 : n+6≤T3 := by dsimp [T3,T2,T1]; omega
    have hprod : 56*(n+6)≤L3*T3 := Nat.mul_le_mul hL3.2.2.1 hT3
    dsimp [R3]
    omega
  have hR4eq : R4+O4=L4*T4 := by
    have hL4 := profile_bounds t4 delta C4 L4 O4 ht4 hpr4
    have hT4 : n+6≤T4 := by dsimp [T4,T3,T2,T1]; omega
    have hprod : 56*(n+6)≤L4*T4 := Nat.mul_le_mul hL4.2.2.1 hT4
    dsimp [R4]
    omega
  have hR5eq : R5+O5=L5*T5 := by
    have hL5 := profile_bounds t5 epsilon C5 L5 O5 ht5 hpr5
    have hT5 : n+6≤T5 := by dsimp [T5,T4,T3,T2,T1]; omega
    have hprod : 56*(n+6)≤L5*T5 := Nat.mul_le_mul hL5.2.2.1 hT5
    dsimp [R5]
    omega
  have hEeq : E+384=112*T6 := by
    have hT6 : 384≤112*T6 := by dsimp [T6,T5,T4,T3,T2,T1]; omega
    dsimp [E]
    omega
  have hK : K+98 =
      C1*q+C2*(q*A1)+C3*(q*(A1*A2))+C4*(q*(A1*A2*A3))+
        C5*(q*(A1*A2*A3*A4)) := by
    have hfirst : 98≤C1*q := by
      have hC1 := profile_bounds t1 alpha C1 L1 O1 ht1 hpr1
      have hh := Nat.mul_le_mul_right q hC1.2.1
      have hq : 1≤q := by dsimp [q]; exact Nat.one_le_pow s 8 (by decide)
      omega
    dsimp [K]
    omega

  have hBa0 := run_cost _ _ _ _ _ s hpre
  have hBc0 := run_cost _ _ _ _ _ u hmid1
  have hBe0 := run_cost _ _ _ _ _ v hmid2
  have hBg0 := run_cost _ _ _ _ _ w hmid3
  have hBi0 := run_cost _ _ _ _ _ x hmid4
  have hBj0 := run_cost _ _ _ _ _ r hsuf
  have hBa : Ba=(n:Int)+6+3*(s:Int) := by omega
  have hBc : Bc=(n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int) := by omega
  have hBe : Be=(n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int) := by omega
  have hBg : Bg=(n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int)+(gamma:Int)+3*(w:Int) := by omega
  have hBi : Bi=(n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int)+(gamma:Int)+3*(w:Int)+
      (delta:Int)+3*(x:Int) := by omega
  have hBj : Bj=(n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int)+(gamma:Int)+3*(w:Int)+
      (delta:Int)+3*(x:Int)+(epsilon:Int)+3*(r:Int) := by omega

  have hpi : (8:Int)^s*(p:Int)=(2:Int)^n := by exact_mod_cast hP
  have hdi : (8:Int)^s*(d:Int)=14*(n:Int)+92 := by exact_mod_cast hD
  have hrootI : I ((2:Int)^n) (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6)=
      98*(2:Int)^n-(14*(n:Int)+92) := by
    unfold I
    omega
  have henergy1 := run_energy _ _ _ _ _ s hpre
  have hscaled : (8:Int)^s*I ((2:Int)^n) Wa Ba =
      (8:Int)^s*(98*(p:Int)-(d:Int)) := by
    calc
      _ = 98*(2:Int)^n-(14*(n:Int)+92) := henergy1.symm.trans hrootI
      _ = (8:Int)^s*(98*(p:Int)-(d:Int)) := by
        rw [Int.mul_sub]
        calc
          98*(2:Int)^n-(14*(n:Int)+92) =
              98*((8:Int)^s*(p:Int))-((8:Int)^s*(d:Int)) := by rw [hpi,hdi]
          _ = (8:Int)^s*(98*(p:Int))-(8:Int)^s*(d:Int) := by congr 1 <;> ac_rfl
  have hqpos : 0<(8:Int)^s := Int.pow_pos (by decide)
  have hIpre : I ((2:Int)^n) Wa Ba=98*(p:Int)-(d:Int) :=
    Int.eq_of_mul_eq_mul_left (by omega) hscaled

  have hT1i : (T1:Int)= (n:Int)+6+3*(s:Int) := by simp [T1]
  have hT2i : (T2:Int)= (n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int) := by
    simp [T2,T1]
  have hT3i : (T3:Int)= (n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int) := by simp [T3,T2,T1]
  have hT4i : (T4:Int)= (n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int)+(gamma:Int)+3*(w:Int) := by
    simp [T4,T3,T2,T1]
  have hT5i : (T5:Int)= (n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int)+(gamma:Int)+3*(w:Int)+
      (delta:Int)+3*(x:Int) := by
    simp [T5,T4,T3,T2,T1]
  have hT6i : (T6:Int)= (n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int)+(gamma:Int)+3*(w:Int)+
      (delta:Int)+3*(x:Int)+(epsilon:Int)+3*(r:Int) := by
    simp [T6,T5,T4,T3,T2,T1]

  have hcoef1 : (L1:Int)*Ba=(L1:Int)*(T1:Int) := by rw [hBa,hT1i]
  have hcoef2 : (L2:Int)*Bc=(L2:Int)*(T2:Int) := by rw [hBc,hT2i]
  have hcoef3 : (L3:Int)*Be=(L3:Int)*(T3:Int) := by rw [hBe,hT3i]
  have hcoef4 : (L4:Int)*Bg=(L4:Int)*(T4:Int) := by rw [hBg,hT4i]
  have hcoef5 : (L5:Int)*Bi=(L5:Int)*(T5:Int) := by rw [hBi,hT5i]
  have hSh1' : ((2:Int)^alpha)*I ((2:Int)^n) Wb (Ba+(alpha:Int)) =
      (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
        (L1:Int)*(T1:Int)-(O1:Int) := by
    rw [hIpre,hcoef1] at hSh1
    exact hSh1
  have hSh2' : ((2:Int)^beta)*I ((2:Int)^n) Wd (Bc+(beta:Int)) =
      I ((2:Int)^n) Wc Bc-(C2:Int)*(2^n:Int)+
        (L2:Int)*(T2:Int)-(O2:Int) := by
    rw [hcoef2] at hSh2
    exact hSh2
  have hSh3' : ((2:Int)^gamma)*I ((2:Int)^n) Wf (Be+(gamma:Int)) =
      I ((2:Int)^n) We Be-(C3:Int)*(2^n:Int)+
        (L3:Int)*(T3:Int)-(O3:Int) := by
    rw [hcoef3] at hSh3
    exact hSh3
  have hSh4' : ((2:Int)^delta)*I ((2:Int)^n) Wh (Bg+(delta:Int)) =
      I ((2:Int)^n) Wg Bg-(C4:Int)*(2:Int)^n+
        (L4:Int)*(T4:Int)-(O4:Int) := by
    rw [hcoef4] at hSh4
    exact hSh4
  have hSh5' : ((2:Int)^epsilon)*I ((2:Int)^n) Wk (Bi+(epsilon:Int)) =
      I ((2:Int)^n) Wi Bi-(C5:Int)*(2:Int)^n+
        (L5:Int)*(T5:Int)-(O5:Int) := by
    rw [hcoef5] at hSh5
    exact hSh5

  have hEi : (E:Int)+384=112*Bj := by
    have hh : (E:Int)+384=112*(T6:Int) := by exact_mod_cast hEeq
    rw [hT6i,←hBj] at hh
    exact hh
  have hIend : I ((2:Int)^n) Wj Bj=-(E:Int) := by
    rw [hwall]
    unfold I
    omega
  have hlastEnergy := run_energy _ _ _ _ _ r hsuf
  have hLast : I ((2:Int)^n) Wk (Bi+(epsilon:Int)) =
      -((8:Int)^r*(E:Int)) := by
    rw [hIend] at hlastEnergy
    simpa only [Int.mul_neg] using hlastEnergy

  let J1 : Int := I ((2:Int)^n) Wb (Ba+(alpha:Int))
  let I1 : Int := I ((2:Int)^n) Wc Bc
  let J2 : Int := I ((2:Int)^n) Wd (Bc+(beta:Int))
  let I2 : Int := I ((2:Int)^n) We Be
  let J3 : Int := I ((2:Int)^n) Wf (Be+(gamma:Int))
  let I3 : Int := I ((2:Int)^n) Wg Bg
  let J4 : Int := I ((2:Int)^n) Wh (Bg+(delta:Int))
  let I4 : Int := I ((2:Int)^n) Wi Bi
  let J5 : Int := I ((2:Int)^n) Wk (Bi+(epsilon:Int))
  have hMid1 : J1=(8:Int)^u*I1 := by
    dsimp [J1,I1]
    exact run_energy _ _ _ _ _ u hmid1
  have hMid2 : J2=(8:Int)^v*I2 := by
    dsimp [J2,I2]
    exact run_energy _ _ _ _ _ v hmid2
  have hMid3 : J3=(8:Int)^w*I3 := by
    dsimp [J3,I3]
    exact run_energy _ _ _ _ _ w hmid3
  have hMid4 : J4=(8:Int)^x*I4 := by
    dsimp [J4,I4]
    exact run_energy _ _ _ _ _ x hmid4
  have hSh1J : ((2:Int)^alpha)*J1 =
      (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
        (L1:Int)*(T1:Int)-(O1:Int) := by simpa only [J1] using hSh1'
  have hSh2J : ((2:Int)^beta)*J2 =
      I1-(C2:Int)*(2^n:Int)+(L2:Int)*(T2:Int)-(O2:Int) := by
    simpa only [J2,I1] using hSh2'
  have hSh3J : ((2:Int)^gamma)*J3 =
      I2-(C3:Int)*(2^n:Int)+(L3:Int)*(T3:Int)-(O3:Int) := by
    simpa only [J3,I2] using hSh3'
  have hSh4J : ((2:Int)^delta)*J4 =
      I3-(C4:Int)*(2:Int)^n+(L4:Int)*(T4:Int)-(O4:Int) := by
    simpa only [J4,I3] using hSh4'
  have hSh5J : ((2:Int)^epsilon)*J5 =
      I4-(C5:Int)*(2:Int)^n+(L5:Int)*(T5:Int)-(O5:Int) := by
    simpa only [J5,I4] using hSh5'
  have hLastJ : J5=-((8:Int)^r*(E:Int)) := by
    simpa only [J5] using hLast

  have hT1lo : n+6≤T1 := by dsimp [T1]; omega
  have hT1hi : T1≤2*n+6 := by dsimp [T1]; omega
  have hT2lo : n+6≤T2 := by dsimp [T2,T1]; omega
  have hT3lo : n+6≤T3 := by dsimp [T3,T2,T1]; omega
  have hT4lo : n+6≤T4 := by dsimp [T4,T3,T2,T1]; omega
  have hT5lo : n+6≤T5 := by dsimp [T5,T4,T3,T2,T1]; omega
  have hT2hi : alpha+3*u≤n-3*s → T2≤2*n+6 := by
    intro h
    dsimp [T2,T1]
    omega
  have hT3hi : alpha+3*u+beta+3*v≤n-3*s → T3≤2*n+6 := by
    intro h
    dsimp [T3,T2,T1]
    omega
  have hT4hi : alpha+3*u+beta+3*v+gamma+3*w≤n-3*s → T4≤2*n+6 := by
    intro h
    dsimp [T4,T3,T2,T1]
    omega
  have hT5hi : alpha+3*u+beta+3*v+gamma+3*w+delta+3*x≤n-3*s →
      T5≤2*n+6 := by
    intro h
    dsimp [T5,T4,T3,T2,T1]
    omega
  have hT6hi : alpha+3*u+beta+3*v+gamma+3*w+delta+3*x+epsilon+3*r≤n-3*s →
      T6≤2*n+6 := by
    intro h
    dsimp [T6,T5,T4,T3,T2,T1]
    omega

  have hprof1 := profile_bounds t1 alpha C1 L1 O1 ht1 hpr1
  have hprof2 := profile_bounds t2 beta C2 L2 O2 ht2 hpr2
  have hprof3 := profile_bounds t3 gamma C3 L3 O3 ht3 hpr3
  have hprof4 := profile_bounds t4 delta C4 L4 O4 ht4 hpr4
  have hprof5 := profile_bounds t5 epsilon C5 L5 O5 ht5 hpr5
  have htime1 := profile_time_bounds t1 alpha C1 L1 O1 n T1 ht1 hpr1 hT1lo hT1hi
  have hR1pos : 0<R1 := by
    have hprod : 56*(n+6)≤L1*T1 := Nat.mul_le_mul hprof1.2.2.1 hT1lo
    omega
  have hR1bound : R1≤168*(n+2) := by
    dsimp [R1]
    have hh := htime1.2.2
    omega
  have hR2pos : 0<R2 := by
    have hprod : 56*(n+6)≤L2*T2 := Nat.mul_le_mul hprof2.2.2.1 hT2lo
    omega
  have hR2bound : alpha+3*u≤n-3*s → R2≤168*(n+2) := by
    intro h
    have htime := profile_time_bounds t2 beta C2 L2 O2 n T2 ht2 hpr2 hT2lo (hT2hi h)
    dsimp [R2]
    exact htime.2.2
  have hR3pos : 0<R3 := by
    have hprod : 56*(n+6)≤L3*T3 := Nat.mul_le_mul hprof3.2.2.1 hT3lo
    omega
  have hR3bound : alpha+3*u+beta+3*v≤n-3*s → R3≤168*(n+2) := by
    intro h
    have htime := profile_time_bounds t3 gamma C3 L3 O3 n T3 ht3 hpr3 hT3lo (hT3hi h)
    dsimp [R3]
    exact htime.2.2
  have hR4pos : 0<R4 := by
    have hprod : 56*(n+6)≤L4*T4 := Nat.mul_le_mul hprof4.2.2.1 hT4lo
    omega
  have hR4bound : alpha+3*u+beta+3*v+gamma+3*w≤n-3*s → R4≤168*(n+2) := by
    intro h
    have htime := profile_time_bounds t4 delta C4 L4 O4 n T4 ht4 hpr4 hT4lo (hT4hi h)
    dsimp [R4]
    exact htime.2.2
  have hR5pos : 0<R5 := by
    have hprod : 56*(n+6)≤L5*T5 := Nat.mul_le_mul hprof5.2.2.1 hT5lo
    omega
  have hR5bound :
      alpha+3*u+beta+3*v+gamma+3*w+delta+3*x≤n-3*s →
        R5≤168*(n+2) := by
    intro h
    have htime := profile_time_bounds t5 epsilon C5 L5 O5 n T5 ht5 hpr5 hT5lo (hT5hi h)
    dsimp [R5]
    exact htime.2.2
  have hEbound :
      alpha+3*u+beta+3*v+gamma+3*w+delta+3*x+epsilon+3*r≤n-3*s →
        E+1≤224*(n+2) := by
    intro h
    have hT := hT6hi h
    have hprod : 112*T6≤112*(2*n+6) := Nat.mul_le_mul_left 112 hT
    dsimp [E]
    omega

  have hKlower :
      392*(8^s*((2^alpha*8^u)*
        ((2^beta*8^v)*((2^gamma*8^w)*(2^delta*8^x)))))≤K := by
    have hC1 := profile_bounds t1 alpha C1 L1 O1 ht1 hpr1
    have hC5 := profile_bounds t5 epsilon C5 L5 O5 ht5 hpr5
    have hq : 1≤8^s := Nat.one_le_pow s 8 (by decide)
    have hfirst : 98≤C1*(8^s) := by
      have hh := Nat.mul_le_mul_right (8^s) hC1.2.1
      omega
    have hlast :
        392*(8^s*(A1*(A2*(A3*A4))))≤
          C5*(8^s*(A1*(A2*(A3*A4)))) :=
      Nat.mul_le_mul_right _ hC5.2.1
    have hassoc : 8^s*(A1*(A2*(A3*A4)))=
        8^s*(A1*A2*A3*A4) := by ac_rfl
    have hlast' :
        392*(8^s*(A1*A2*A3*A4))≤
          C5*(8^s*(A1*A2*A3*A4)) := by
      simpa only [hassoc] using hlast
    have hK' : K+98 =
      C1*(8^s)+C2*(8^s*A1)+C3*(8^s*(A1*A2))+
        C4*(8^s*(A1*A2*A3))+C5*(8^s*(A1*A2*A3*A4)) := by
      simpa [q,A1,A2,A3,A4,Nat.mul_assoc] using hK
    have hKlower' : 392*(8^s*(A1*A2*A3*A4))≤K := by
      omega
    have hKlower'' : 392*(8^s*(A1*(A2*(A3*A4))))≤K := by
      rw [hassoc]
      exact hKlower'
    simpa [A1,A2,A3,A4] using hKlower''

  exact no_five_shallow_energies
    n s u v w x r t1 t2 t3 t4 t5 alpha beta gamma delta epsilon
    p d C1 C2 C3 C4 C5 L1 L2 L3 L4 L5 O1 O2 O3 O4 O5
    K R1 R2 R3 R4 R5 E hn14 hs
    hprof1.1 hprof2.1 hprof3.1 hprof4.1 hprof5.1
    ht1 ht2 ht3 ht4 ht5 hpr1 hpr2 hpr3 hpr4 hpr5
    hP hD
    (by simpa [T1] using hR1eq)
    (by simpa [T2,T1] using hR2eq)
    (by simpa [T3,T2,T1] using hR3eq)
    (by simpa [T4,T3,T2,T1] using hR4eq)
    (by simpa [T5,T4,T3,T2,T1] using hR5eq)
    (by simpa [T6,T5,T4,T3,T2,T1] using hEeq)
    (by simpa [q,A1,A2,A3,A4] using hK)
    hKlower hR1pos hR1bound hR2pos hR2bound hR3pos hR3bound
    hR4pos hR4bound hR5pos hR5bound hEbound
    J1 I1 J2 I2 J3 I3 J4 I4 J5
    hSh1J hMid1 hSh2J hMid2 hSh3J hMid3 hSh4J hMid4 hSh5J hLastJ

#print axioms no_five_shallow_model_from_source_coefficients

end BB6.Agent43FiveShallowSourceModel
