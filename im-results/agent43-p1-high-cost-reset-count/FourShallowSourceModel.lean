import FourShallowAbstractBridge
import RootTwoDivisor
import TwoRunModel
import SourceOneShallowLift
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43FourShallowSourceModel

open BB6.Agent43TwoRun BB6.Agent43FourShallowAbstract BB6.Agent43TwoShallowFinite
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

private theorem profile_bounds (t alpha C L O : Nat)
    (ht : t≤1) (h : (alpha,C,L,O)=triple t) :
    1≤alpha ∧ 392≤C ∧ 56≤L ∧ L≤84 ∧ O≤232 := by
  have ht' : t=0 ∨ t=1 := by omega
  rcases ht' with he|he <;> subst t <;> simp [triple] at h <;> omega

/-- Exact source-shaped model theorem for four genuine shallow transitions.
The only transition-specific inputs are the four affine energy profiles;
the five intervening depth-two runs are the original TwoRun relations. -/
theorem no_four_shallow_model_from_source_coefficients
 (n s u v w r t1 t2 t3 t4 alpha beta gamma delta
  C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4 : Nat)
 (hn : 76≤n) (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1) (ht4 : t4≤1)
 (hpr1 : (alpha,C1,L1,O1)=triple t1)
 (hpr2 : (beta,C2,L2,O2)=triple t2)
 (hpr3 : (gamma,C3,L3,O3)=triple t3)
 (hpr4 : (delta,C4,L4,O4)=triple t4)
 (Wa Ba Wb Wc Bc Wd We Be Wf Wg Bg Wh Wj Bj : Int)
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
 (hsuf : TwoRun ((2:Int)^n) Wh (Bg+(delta:Int)) r Wj Bj)
 (hwall : Wj=12*(2:Int)^n) : False := by
  obtain ⟨hs,hDdiv⟩ := root_two_prefix_divisor n s Wa Ba hn hpre
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
  let T5 : Nat := T4+delta+3*r
  let R1 : Nat := L1*T1-O1-d
  let R2 : Nat := L2*T2-O2
  let R3 : Nat := L3*T3-O3
  let R4 : Nat := L4*T4-O4
  let E : Nat := 112*T5-384
  let A1 : Nat := 2^alpha*8^u
  let A2 : Nat := 2^beta*8^v
  let A3 : Nat := 2^gamma*8^w
  let q : Nat := 8^s
  let K : Nat := C1*q+C2*(q*A1)+C3*(q*(A1*A2))+C4*(q*(A1*A2*A3))-98

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
  have hEeq : E+384=112*T5 := by
    have hT5 : 384≤112*T5 := by dsimp [T5,T4,T3,T2,T1]; omega
    dsimp [E]
    omega
  have hK : K+98 =
      C1*q+C2*(q*A1)+C3*(q*(A1*A2))+C4*(q*(A1*A2*A3)) := by
    have hfirst : 98≤C1*q := by
      have hC1 := profile_bounds t1 alpha C1 L1 O1 ht1 hpr1
      have hh := Nat.mul_le_mul_right q hC1.2.1
      have hq : 1≤q := by dsimp [q]; exact Nat.one_le_pow s 8 (by decide)
      dsimp [K]
      omega
    dsimp [K]
    omega

  have hBa0 := run_cost _ _ _ _ _ s hpre
  have hBc0 := run_cost _ _ _ _ _ u hmid1
  have hBe0 := run_cost _ _ _ _ _ v hmid2
  have hBg0 := run_cost _ _ _ _ _ w hmid3
  have hBj0 := run_cost _ _ _ _ _ r hsuf
  have hBa : Ba=(n:Int)+6+3*(s:Int) := by omega
  have hBc : Bc=(n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int) := by omega
  have hBe : Be=(n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int) := by omega
  have hBg : Bg=(n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int)+(gamma:Int)+3*(w:Int) := by omega
  have hBj : Bj=(n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int)+(gamma:Int)+3*(w:Int)+(delta:Int)+3*(r:Int) := by omega

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
    Int.eq_of_mul_eq_mul_left hqpos hscaled

  have hT1i : (T1:Int)= (n:Int)+6+3*(s:Int) := by dsimp [T1]; omega
  have hT2i : (T2:Int)= (n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int) := by
    dsimp [T2,T1]; omega
  have hT3i : (T3:Int)= (n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int) := by dsimp [T3,T2,T1]; omega
  have hT4i : (T4:Int)= (n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int)+(gamma:Int)+3*(w:Int) := by dsimp [T4,T3,T2,T1]; omega
  have hT5i : (T5:Int)= (n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+
      (beta:Int)+3*(v:Int)+(gamma:Int)+3*(w:Int)+(delta:Int)+3*(r:Int) := by
    dsimp [T5,T4,T3,T2,T1]
    omega

  have hSh1' : ((2:Int)^alpha)*I ((2:Int)^n) Wb (Ba+(alpha:Int)) =
      (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
        (L1:Int)*(T1:Int)-(O1:Int) := by
    rw [hIpre,hBa] at hSh1
    simpa only [←hT1i] using hSh1
  have hSh2' : ((2:Int)^beta)*I ((2:Int)^n) Wd (Bc+(beta:Int)) =
      I ((2:Int)^n) Wc Bc-(C2:Int)*(2^n:Int)+
        (L2:Int)*(T2:Int)-(O2:Int) := by
    rw [hBc] at hSh2
    simpa only [←hT2i] using hSh2
  have hSh3' : ((2:Int)^gamma)*I ((2:Int)^n) Wf (Be+(gamma:Int)) =
      I ((2:Int)^n) We Be-(C3:Int)*(2^n:Int)+
        (L3:Int)*(T3:Int)-(O3:Int) := by
    rw [hBe] at hSh3
    simpa only [←hT3i] using hSh3
  have hSh4' : ((2:Int)^delta)*I ((2:Int)^n) Wh (Bg+(delta:Int)) =
      I ((2:Int)^n) Wg Bg-(C4:Int)*(2^n:Int)+
        (L4:Int)*(T4:Int)-(O4:Int) := by
    rw [hBg] at hSh4
    simpa only [←hT4i] using hSh4

  have hEi : (E:Int)+384=112*Bj := by
    have hh : (E:Int)+384=112*(T5:Int) := by exact_mod_cast hEeq
    rw [hT5i] at hh
    exact hh
  have hIend : I ((2:Int)^n) Wj Bj=-(E:Int) := by
    rw [hwall]
    unfold I
    omega
  have hlastEnergy := run_energy _ _ _ _ _ r hsuf
  have hLast : I ((2:Int)^n) Wh (Bg+(delta:Int)) =
      -((8:Int)^r*(E:Int)) := by
    rw [hIend] at hlastEnergy
    simpa only [Int.mul_neg] using hlastEnergy

  have J1 : Int := I ((2:Int)^n) Wb (Ba+(alpha:Int))
  have I1 : Int := I ((2:Int)^n) Wc Bc
  have J2 : Int := I ((2:Int)^n) Wd (Bc+(beta:Int))
  have I2 : Int := I ((2:Int)^n) We Be
  have J3 : Int := I ((2:Int)^n) Wf (Be+(gamma:Int))
  have I3 : Int := I ((2:Int)^n) Wg Bg
  have J4 : Int := I ((2:Int)^n) Wh (Bg+(delta:Int))
  have hMid1 : J1=(8:Int)^u*I1 := by
    dsimp [J1,I1]
    exact run_energy _ _ _ _ _ u hmid1
  have hMid2 : J2=(8:Int)^v*I2 := by
    dsimp [J2,I2]
    exact run_energy _ _ _ _ _ v hmid2
  have hMid3 : J3=(8:Int)^w*I3 := by
    dsimp [J3,I3]
    exact run_energy _ _ _ _ _ w hmid3
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
      I3-(C4:Int)*(2^n:Int)+(L4:Int)*(T4:Int)-(O4:Int) := by
    simpa only [J4,I3] using hSh4'

  have hT1lo : n+6≤T1 := by dsimp [T1]; omega
  have hT1hi : T1≤2*n+6 := by dsimp [T1]; omega
  have hT2lo : n+6≤T2 := by dsimp [T2,T1]; omega
  have hT3lo : n+6≤T3 := by dsimp [T3,T2,T1]; omega
  have hT4lo : n+6≤T4 := by dsimp [T4,T3,T2,T1]; omega
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
  have hT5hi : alpha+3*u+beta+3*v+gamma+3*w+delta+3*r≤n-3*s →
      T5≤2*n+6 := by
    intro h
    dsimp [T5,T4,T3,T2,T1]
    omega

  have hprof1 := profile_bounds t1 alpha C1 L1 O1 ht1 hpr1
  have hprof2 := profile_bounds t2 beta C2 L2 O2 ht2 hpr2
  have hprof3 := profile_bounds t3 gamma C3 L3 O3 ht3 hpr3
  have hprof4 := profile_bounds t4 delta C4 L4 O4 ht4 hpr4
  have hR1pos : 0<R1 := by
    have hprod : 56*(n+6)≤L1*T1 := Nat.mul_le_mul hprof1.2.2.1 hT1lo
    omega
  have hR1bound : R1≤400*(n+2) := by
    have hprod : L1*T1≤84*(2*n+6) := Nat.mul_le_mul hprof1.2.2.2.1 hT1hi
    omega
  have hR2pos : 0<R2 := by
    have hprod : 56*(n+6)≤L2*T2 := Nat.mul_le_mul hprof2.2.2.1 hT2lo
    omega
  have hR2bound : alpha+3*u≤n-3*s → R2≤600*(n+2) := by
    intro h
    have hprod : L2*T2≤84*(2*n+6) :=
      Nat.mul_le_mul hprof2.2.2.2.1 (hT2hi h)
    omega
  have hR3pos : 0<R3 := by
    have hprod : 56*(n+6)≤L3*T3 := Nat.mul_le_mul hprof3.2.2.1 hT3lo
    omega
  have hR3bound : alpha+3*u+beta+3*v≤n-3*s → R3≤600*(n+2) := by
    intro h
    have hprod : L3*T3≤84*(2*n+6) :=
      Nat.mul_le_mul hprof3.2.2.2.1 (hT3hi h)
    omega
  have hR4pos : 0<R4 := by
    have hprod : 56*(n+6)≤L4*T4 := Nat.mul_le_mul hprof4.2.2.1 hT4lo
    omega
  have hR4bound :
      alpha+3*u+beta+3*v+gamma+3*w≤n-3*s → R4≤600*(n+2) := by
    intro h
    have hprod : L4*T4≤84*(2*n+6) :=
      Nat.mul_le_mul hprof4.2.2.2.1 (hT4hi h)
    omega
  have hEbound :
      alpha+3*u+beta+3*v+gamma+3*w+delta+3*r≤n-3*s →
      E≤2000*(n+2) := by
    intro h
    have hT := hT5hi h
    have hprod : 112*T5≤112*(2*n+6) := Nat.mul_le_mul_left 112 hT
    omega

  have hKlower :
      392*(8^s*((2^alpha*8^u)*((2^beta*8^v)*(2^gamma*8^w))))≤K := by
    have hC1 := profile_bounds t1 alpha C1 L1 O1 ht1 hpr1
    have hC4 := profile_bounds t4 delta C4 L4 O4 ht4 hpr4
    have hq : 1≤8^s := Nat.one_le_pow s 8 (by decide)
    have hfirst : 98≤C1*(8^s) := by
      have hh := Nat.mul_le_mul_right (8^s) hC1.2.1
      omega
    have hlast : 392*(8^s*((2^alpha*8^u)*((2^beta*8^v)*(2^gamma*8^w)))) ≤
        C4*(8^s*((2^alpha*8^u)*((2^beta*8^v)*(2^gamma*8^w)))) :=
      Nat.mul_le_mul_right _ hC4.2.1
    have hlast' : 392*(8^s*((2^alpha*8^u)*((2^beta*8^v)*(2^gamma*8^w)))) ≤
        C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))) := by
      simpa [Nat.mul_assoc] using hlast
    have hK' : K+98 =
      C1*(8^s)+C2*(8^s*(2^alpha*8^u))+
      C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
      C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))) := by
      simpa [q,A1,A2,A3] using hK
    omega

  exact no_four_shallow_energies n s u v w r t1 t2 t3 t4 p d
    alpha beta gamma delta C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4
    K R1 R2 R3 R4 E hn hs ht1 ht2 ht3 ht4 hpr1 hpr2 hpr3 hpr4
    hP hD
    (by simpa [T1] using hR1eq)
    (by simpa [T2,T1] using hR2eq)
    (by simpa [T3,T2,T1] using hR3eq)
    (by simpa [T4,T3,T2,T1] using hR4eq)
    (by simpa [T5,T4,T3,T2,T1] using hEeq)
    (by simpa [q,A1,A2,A3] using hK)
    hKlower hR1pos hR1bound hR2pos hR2bound hR3pos hR3bound
    hR4pos hR4bound hEbound
    J1 I1 J2 I2 J3 I3 J4 hSh1J hMid1 hSh2J hMid2 hSh3J hMid3 hSh4J hLast

#print axioms no_four_shallow_model_from_source_coefficients

end BB6.Agent43FourShallowSourceModel
