import ThreeShallowAbstractBridge
import RootTwoDivisor
import TwoRunModel
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43ThreeShallowSourceModel
open BB6.Agent43TwoRun BB6.Agent43ThreeShallowAbstract BB6.Agent43TwoShallowFinite
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Exact scalar contradiction from four original-source-compatible depth-two
runs and three shallow energy cocycles. No bounded history-length assumption. -/
theorem no_three_shallow_model_from_source_coefficients
 (n s u v r t1 t2 t3 alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 : Nat)
 (hn : 14≤n) (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1)
 (hpr1 : (alpha,C1,L1,O1)=triple t1)
 (hpr2 : (beta,C2,L2,O2)=triple t2)
 (hpr3 : (gamma,C3,L3,O3)=triple t3)
 (hC1 : 392≤C1) (hL1 : 56≤L1) (hO1 : O1≤232)
 (hC2 : 392≤C2) (hL2 : 56≤L2) (hO2 : O2≤232)
 (hC3 : 392≤C3) (hL3 : 56≤L3) (hO3 : O3≤232)
 (Wa Ba Wb Wc Bc Wd We Be Wf Wg Bg : Int)
 (hpre : TwoRun ((2:Int)^n) (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s Wa Ba)
 (hSh1 : ((2:Int)^alpha)*I ((2:Int)^n) Wb (Ba+(alpha:Int)) =
     I ((2:Int)^n) Wa Ba-(C1:Int)*(2:Int)^n+(L1:Int)*Ba-(O1:Int))
 (hmid1 : TwoRun ((2:Int)^n) Wb (Ba+(alpha:Int)) u Wc Bc)
 (hSh2 : ((2:Int)^beta)*I ((2:Int)^n) Wd (Bc+(beta:Int)) =
     I ((2:Int)^n) Wc Bc-(C2:Int)*(2:Int)^n+(L2:Int)*Bc-(O2:Int))
 (hmid2 : TwoRun ((2:Int)^n) Wd (Bc+(beta:Int)) v We Be)
 (hSh3 : ((2:Int)^gamma)*I ((2:Int)^n) Wf (Be+(gamma:Int)) =
     I ((2:Int)^n) We Be-(C3:Int)*(2:Int)^n+(L3:Int)*Be-(O3:Int))
 (hsuf : TwoRun ((2:Int)^n) Wf (Be+(gamma:Int)) r Wg Bg)
 (hwall : Wg=12*(2:Int)^n) : False := by
  obtain ⟨hs, hDdiv⟩ := root_two_prefix_divisor n s Wa Ba hn hpre
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
    omega
  let T1 : Nat := n+6+3*s
  let T2 : Nat := T1+alpha+3*u
  let T3 : Nat := T2+beta+3*v
  let T4 : Nat := T3+gamma+3*r
  let R1 : Nat := L1*T1-O1-d
  let R2 : Nat := L2*T2-O2
  let R3 : Nat := L3*T3-O3
  let E : Nat := 112*T4-384
  let K : Nat := C1*8^s+C2*(8^s*(2^alpha*8^u))+C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))-98
  have hR1 : R1+O1+d=L1*T1 := by
    have hh : 56*(n+6) ≤ L1*T1 := by
      dsimp [T1]
      exact Nat.mul_le_mul hL1 (by omega)
    dsimp [R1]
    omega
  have hR2 : R2+O2=L2*T2 := by
    have hh : 56*(n+6) ≤ L2*T2 := by
      dsimp [T2,T1]
      exact Nat.mul_le_mul hL2 (by omega)
    dsimp [R2]
    omega
  have hR3 : R3+O3=L3*T3 := by
    have hh : 56*(n+6) ≤ L3*T3 := by
      dsimp [T3,T2,T1]
      exact Nat.mul_le_mul hL3 (by omega)
    dsimp [R3]
    omega
  have hE : E+384=112*T4 := by
    dsimp [E]
    dsimp [T4,T3,T2,T1]
    omega
  have hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+C3*(8^s*((2^alpha*8^u)*(2^beta*8^v))) := by
    have hh : 392 ≤ C1*8^s := by
      have h := Nat.mul_le_mul hC1 hqge
      simpa using h
    dsimp [K]
    omega
  have hCost1 := run_cost _ _ _ _ _ s hpre
  have hCost2 := run_cost _ _ _ _ _ u hmid1
  have hCost3 := run_cost _ _ _ _ _ v hmid2
  have hCost4 := run_cost _ _ _ _ _ r hsuf
  have hBa : Ba=(n:Int)+6+3*(s:Int) := by omega
  have hBc : Bc=(n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int) := by omega
  have hBe : Be=(n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+(beta:Int)+3*(v:Int) := by omega
  have hBg : Bg=(n:Int)+6+3*(s:Int)+(alpha:Int)+3*(u:Int)+(beta:Int)+3*(v:Int)+(gamma:Int)+3*(r:Int) := by omega
  have hpi : (8:Int)^s*(p:Int)=(2:Int)^n := by exact_mod_cast hP
  have hdi : (8:Int)^s*(d:Int)=14*(n:Int)+92 := by exact_mod_cast hD
  have hrootI : I ((2:Int)^n) (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6)=
      98*(2:Int)^n-(14*(n:Int)+92) := by
    unfold I
    omega
  have henergy1 := run_energy _ _ _ _ _ s hpre
  rw [hrootI] at henergy1
  have hscaled : (8:Int)^s * I ((2:Int)^n) Wa Ba =
     (8:Int)^s * (98*(p:Int)-(d:Int)) := by
    calc
      _ = 98*(2:Int)^n-(14*(n:Int)+92) := henergy1.symm
      _ = (8:Int)^s*(98*(p:Int)-(d:Int)) := by
        rw [Int.mul_sub]
        calc
          98*(2:Int)^n-(14*(n:Int)+92) = 98*((8:Int)^s*(p:Int))-((8:Int)^s*(d:Int)) := by rw [hpi,hdi]
          _ = (8:Int)^s*(98*(p:Int)) - (8:Int)^s*(d:Int) := by
            congr 1
            ac_rfl
  have hqpos : 0<(8:Int)^s := Int.pow_pos (by decide)
  have hIpre : I ((2:Int)^n) Wa Ba=98*(p:Int)-(d:Int) :=
    Int.eq_of_mul_eq_mul_left (by omega) hscaled
  have hSh1' : ((2:Int)^alpha)*I ((2:Int)^n) Wb (Ba+(alpha:Int)) =
      98*(p:Int)-(d:Int)-(C1:Int)*(2:Int)^n+(L1:Int)*(n+6+3*s:Int)-(O1:Int) := by
    rw [hIpre] at hSh1
    simpa only [hBa] using hSh1
  have hSh2' : ((2:Int)^beta)*I ((2:Int)^n) Wd (Bc+(beta:Int)) =
      I ((2:Int)^n) Wc Bc-(C2:Int)*(2:Int)^n+(L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int) := by
    simpa only [hBc] using hSh2
  have hSh3' : ((2:Int)^gamma)*I ((2:Int)^n) Wf (Be+(gamma:Int)) =
      I ((2:Int)^n) We Be-(C3:Int)*(2:Int)^n+(L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int)-(O3:Int) := by
    simpa only [hBe] using hSh3
  have hEi : (E:Int)+384=112*Bg := by
    have hh : (E:Int)+384=112*(T4:Int) := by exact_mod_cast hE
    have hT4 : (T4:Int)=Bg := by dsimp [T4,T3,T2,T1]; omega
    rw [hT4] at hh
    exact hh
  have hIend : I ((2:Int)^n) Wg Bg=-(E:Int) := by
    rw [hwall]
    unfold I
    omega
  have hlastEnergy := run_energy _ _ _ _ _ r hsuf
  have hlast : I ((2:Int)^n) Wf (Be+(gamma:Int)) = -((8:Int)^r*(E:Int)) := by
    rw [hIend] at hlastEnergy
    simpa only [Int.mul_neg] using hlastEnergy
  exact no_three_shallow_energies n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E
    hn hs ht1 ht2 ht3 hpr1 hpr2 hpr3 hP hD
    (by simpa only [T1] using hR1)
    (by simpa only [T2,T1] using hR2)
    (by simpa only [T3,T2,T1] using hR3)
    (by simpa only [T4,T3,T2,T1] using hE)
    hK
    (I ((2:Int)^n) Wb (Ba+(alpha:Int))) (I ((2:Int)^n) Wc Bc)
    (I ((2:Int)^n) Wd (Bc+(beta:Int))) (I ((2:Int)^n) We Be)
    (I ((2:Int)^n) Wf (Be+(gamma:Int)))
    hSh1' (run_energy _ _ _ _ _ u hmid1)
    hSh2' (run_energy _ _ _ _ _ v hmid2)
    hSh3' hlast

#print axioms no_three_shallow_model_from_source_coefficients
end BB6.Agent43ThreeShallowSourceModel
