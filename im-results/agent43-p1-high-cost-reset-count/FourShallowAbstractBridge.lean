import FourLayerBarrier
import TwoShallowFiniteBounds
import Lean.Elab.Tactic.Omega


namespace BB6.Agent43FourShallowAbstract

open BB6.Agent43TwoShallowFinite BB6.Agent43FourLayer

/-- The first four dyadic remainders in the source-profiled four-shallow
terminal equation. -/
def fourProfileAlpha (t : Nat) : Nat := if t=0 then 1 else 2

def fourProfileStep (x t : Nat) : Prop :=
  fourProfileAlpha t ≤ x ∧ (x-fourProfileAlpha t)%3=0

def fourRootDivides (n s : Nat) : Prop :=
  2^n % 8^s = 0 ∧ (14*n+92)%8^s=0

def fourRootRem (n s t1 : Nat) : Nat := Id.run do
  let (_,_,L,O) := triple t1
  let q := 8^s
  return L*(n+6+3*s)-O-(14*n+92)/q

def fourSecondRem (n s t1 x1 t2 : Nat) : Nat := Id.run do
  let (_,_,L2,O2) := triple t2
  let R1 := fourRootRem n s t1
  let d1 := R1/2^x1
  return L2*(n+6+3*s+x1)-O2+d1

def fourThirdRem (n s t1 x1 t2 x2 t3 : Nat) : Nat := Id.run do
  let (_,_,L3,O3) := triple t3
  let S2 := fourSecondRem n s t1 x1 t2
  let d2 := S2/2^x2
  return L3*(n+6+3*s+x1+x2)-O3+d2

def fourFourthRem (n s t1 x1 t2 x2 t3 x3 t4 : Nat) : Nat := Id.run do
  let (_,_,L4,O4) := triple t4
  let S3 := fourThirdRem n s t1 x1 t2 x2 t3
  let d3 := S3/2^x3
  return L4*(n+6+3*s+x1+x2+x3)-O4+d3

def fourCoeff (s t1 x1 t2 x2 t3 x3 t4 : Nat) : Nat := Id.run do
  let (_,C1,_,_) := triple t1
  let (_,C2,_,_) := triple t2
  let (_,C3,_,_) := triple t3
  let (_,C4,_,_) := triple t4
  let q := 8^s
  return q*(C1+C2*2^x1+C3*2^(x1+x2)+C4*2^(x1+x2+x3))-98

def fourEmax (n s x1 x2 x3 : Nat) : Nat :=
  112*(n+6+3*s+x1+x2+x3+15)-384

set_option maxRecDepth 8192
set_option maxHeartbeats 50000000

/-- Exact finite nondivisibility at the root, for every source profile and
every possible root prefix with 14 <= n <= 75. -/
theorem four_root_no_overflow :
  ∀ n : Fin 62, ∀ s : Fin 4, ∀ t1 : Fin 2,
    fourRootDivides (n.val+14) s.val →
    fourRootRem (n.val+14) s.val t1.val %
      2^(n.val+14-3*s.val) ≠ 0 := by decide

/-- The second shallow remainder is not divisible by the remaining
root-power after any legal first shallow exponent. -/
theorem four_second_no_overflow :
  ∀ n : Fin 62, ∀ s : Fin 4, ∀ t1 : Fin 2,
    ∀ x1 : Fin 13, ∀ t2 : Fin 2,
    fourRootDivides (n.val+14) s.val →
    fourRootRem (n.val+14) s.val t1.val %
      2^(n.val+14-3*s.val) ≠ 0 →
    x1.val ≤ n.val+14-3*s.val →
    fourProfileStep x1.val t1.val →
    fourRootRem (n.val+14) s.val t1.val % 2^x1.val = 0 →
    fourSecondRem (n.val+14) s.val t1.val x1.val t2.val %
      2^(n.val+14-3*s.val-x1.val) ≠ 0 := by decide

/-- The third shallow remainder is not divisible by the remaining
root-power after any legal first two shallow exponents. -/
theorem four_third_no_overflow :
  ∀ n : Fin 62, ∀ s : Fin 4, ∀ t1 : Fin 2,
    ∀ x1 : Fin 13, ∀ t2 : Fin 2, ∀ x2 : Fin 14, ∀ t3 : Fin 2,
    fourRootDivides (n.val+14) s.val →
    fourRootRem (n.val+14) s.val t1.val %
      2^(n.val+14-3*s.val) ≠ 0 →
    x1.val ≤ n.val+14-3*s.val →
    fourProfileStep x1.val t1.val →
    fourRootRem (n.val+14) s.val t1.val % 2^x1.val = 0 →
    fourSecondRem (n.val+14) s.val t1.val x1.val t2.val %
      2^(n.val+14-3*s.val-x1.val) ≠ 0 →
    x2.val ≤ n.val+14-3*s.val-x1.val →
    fourProfileStep x2.val t2.val →
    fourSecondRem (n.val+14) s.val t1.val x1.val t2.val % 2^x2.val = 0 →
    fourThirdRem (n.val+14) s.val t1.val x1.val t2.val x2.val t3.val %
      2^(n.val+14-3*s.val-x1.val-x2.val) ≠ 0 := by decide

/-- Final finite certificate for the 14..75 four-shallow sector.  Once the
first three remainders have been peeled, the fourth remainder is not divisible
by the remaining power, and the exact coefficient exceeds the largest
possible fourth-remainder terminal contribution (using x4 <= 15). -/
theorem four_fourth_finite_audit :
  ∀ n : Fin 62, ∀ s : Fin 4, ∀ t1 : Fin 2,
    ∀ x1 : Fin 13, ∀ t2 : Fin 2, ∀ x2 : Fin 14,
    ∀ t3 : Fin 2, ∀ x3 : Fin 15, ∀ t4 : Fin 2,
    fourRootDivides (n.val+14) s.val →
    fourRootRem (n.val+14) s.val t1.val %
      2^(n.val+14-3*s.val) ≠ 0 →
    x1.val ≤ n.val+14-3*s.val →
    fourProfileStep x1.val t1.val →
    fourRootRem (n.val+14) s.val t1.val % 2^x1.val = 0 →
    fourSecondRem (n.val+14) s.val t1.val x1.val t2.val %
      2^(n.val+14-3*s.val-x1.val) ≠ 0 →
    x2.val ≤ n.val+14-3*s.val-x1.val →
    fourProfileStep x2.val t2.val →
    fourSecondRem (n.val+14) s.val t1.val x1.val t2.val % 2^x2.val = 0 →
    fourThirdRem (n.val+14) s.val t1.val x1.val t2.val x2.val t3.val %
      2^(n.val+14-3*s.val-x1.val-x2.val) ≠ 0 →
    x3.val ≤ n.val+14-3*s.val-x1.val-x2.val →
    fourProfileStep x3.val t3.val →
    fourThirdRem (n.val+14) s.val t1.val x1.val t2.val x2.val t3.val %
      2^x3.val = 0 →
    (fourFourthRem (n.val+14) s.val t1.val x1.val t2.val x2.val
        t3.val x3.val t4.val %
        2^(n.val+14-3*s.val-x1.val-x2.val-x3.val) ≠ 0 ∧
      fourCoeff s.val t1.val x1.val t2.val x2.val t3.val x3.val t4.val *
        2^(n.val+14-3*s.val-x1.val-x2.val-x3.val) >
        fourFourthRem (n.val+14) s.val t1.val x1.val t2.val x2.val
          t3.val x3.val t4.val *
          (fourEmax (n.val+14) s.val x1.val x2.val x3.val+1)) := by
  native_decide

#print axioms four_root_no_overflow
#print axioms four_second_no_overflow
#print axioms four_third_no_overflow
#print axioms four_fourth_finite_audit

/-- Four source-profiled shallow cocycles, separated by depth-two energy
divisions, imply an impossible terminal shifted-wall equation. -/
theorem no_four_shallow_energies
 (n s u v w r t1 t2 t3 t4 p d alpha beta gamma delta
  C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4 K R1 R2 R3 R4 E : Nat)
 (hn : 76≤n) (hs : 3*s≤n)
 (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1) (ht4 : t4≤1)
 (hp1 : (alpha,C1,L1,O1)=triple t1)
 (hp2 : (beta,C2,L2,O2)=triple t2)
 (hp3 : (gamma,C3,L3,O3)=triple t3)
 (hp4 : (delta,C4,L4,O4)=triple t4)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*r))
 (hK : K+98 =
   C1*8^s+C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))))
 (hKlower : 392*(8^s*((2^alpha*8^u)*((2^beta*8^v)*(2^gamma*8^w))))≤K)
 (hR1pos : 0<R1) (hR1bound : R1≤400*(n+2))
 (hR2pos : 0<R2)
 (hR2bound : alpha+3*u≤n-3*s → R2≤600*(n+2))
 (hR3pos : 0<R3)
 (hR3bound : alpha+3*u+beta+3*v≤n-3*s → R3≤600*(n+2))
 (hR4pos : 0<R4)
 (hR4bound : alpha+3*u+beta+3*v+gamma+3*w≤n-3*s → R4≤600*(n+2))
 (hEbound : alpha+3*u+beta+3*v+gamma+3*w+delta+3*r≤n-3*s →
   E≤2000*(n+2))
 (J1 I1 J2 I2 J3 I3 J4 : Int)
 (hSh1 : ((2:Int)^alpha)*J1=
   (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
     (L1:Int)*(n+6+3*s:Int)-(O1:Int))
 (hMid1 : J1=(8:Int)^u*I1)
 (hSh2 : ((2:Int)^beta)*J2=
   I1-(C2:Int)*(2^n:Int)+(L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int))
 (hMid2 : J2=(8:Int)^v*I2)
 (hSh3 : ((2:Int)^gamma)*J3=
   I2-(C3:Int)*(2^n:Int)+
     (L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int)-(O3:Int))
 (hMid3 : J3=(8:Int)^w*I3)
 (hSh4 : ((2:Int)^delta)*J4=
   I3-(C4:Int)*(2:Int)^n+
     (L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int)-(O4:Int))
 (hLast : J4=-((8:Int)^r*(E:Int))) : False := by
 let a : Int := (2:Int)^alpha*(8:Int)^u
 let b : Int := (2:Int)^beta*(8:Int)^v
 let c : Int := (2:Int)^gamma*(8:Int)^w
 let f : Int := (2:Int)^delta*(8:Int)^r
 have hPi : ((8:Nat)^s:Int)*(p:Int)=(2:Int)^n := by exact_mod_cast hP
 have hR1i : (R1:Int)+(O1:Int)+(d:Int)=(L1:Int)*(n+6+3*s:Int) := by exact_mod_cast hR1
 have hR2i : (R2:Int)+(O2:Int)=(L2:Int)*(n+6+3*s+alpha+3*u:Int) := by exact_mod_cast hR2
 have hR3i : (R3:Int)+(O3:Int)=(L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int) := by exact_mod_cast hR3
 have hR4i : (R4:Int)+(O4:Int)=
     (L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int) := by exact_mod_cast hR4
 have hKi : (K:Int)+98 =
   (C1:Int)*((8:Nat)^s:Int)+(C2:Int)*(((8:Nat)^s:Int)*a)+
   (C3:Int)*(((8:Nat)^s:Int)*(a*b))+
   (C4:Int)*(((8:Nat)^s:Int)*((a*b)*c)) := by
   have hh := congrArg (fun x:Nat=>(x:Int)) hK
   simpa [a,b,c,Int.natCast_add,Int.natCast_mul,Int.natCast_pow] using hh
 have h1 : a*I1 =
   (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
     (L1:Int)*(n+6+3*s:Int)-(O1:Int) := by
   rw [hMid1] at hSh1
   simpa only [a,Int.mul_assoc] using hSh1
 have h2 : b*I2=I1-(C2:Int)*(2^n:Int)+(R2:Int) := by
   rw [hMid2] at hSh2
   have hx : ((2:Int)^beta)*((8:Int)^v*I2)=b*I2 := by
     dsimp [b]
     rw [Int.mul_assoc]
   rw [hx] at hSh2
   omega
 have h3 : c*I3=I2-(C3:Int)*(2^n:Int)+(R3:Int) := by
   rw [hMid3] at hSh3
   have hx : ((2:Int)^gamma)*((8:Int)^w*I3)=c*I3 := by
     dsimp [c]
     rw [Int.mul_assoc]
   rw [hx] at hSh3
   omega
 have hlast : ((2:Int)^delta)*J4=-(f*(E:Int)) := by
   rw [hLast]
   dsimp [f]
   simp only [Int.mul_neg,Int.neg_mul]
   ac_rfl
 have hR4shift :
     (L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int)-(O4:Int)=(R4:Int) := by
   omega
 have hSh4' : ((2:Int)^delta)*J4=
     I3-(C4:Int)*(2:Int)^n+(R4:Int) := by
   omega
 have hneg4 : -(f*(E:Int))=I3-(C4:Int)*(2:Int)^n+(R4:Int) := by
   calc
     -(f*(E:Int))=((2:Int)^delta)*J4 := hlast.symm
     _=I3-(C4:Int)*(2:Int)^n+(R4:Int) := hSh4'
 have h4 : f*(E:Int)=(C4:Int)*(2:Int)^n-(R4:Int)-I3 := by
   omega
 have h2' : I1=(C2:Int)*(2^n:Int)-(R2:Int)+b*I2 := by omega
 have h3' : I2=(C3:Int)*(2^n:Int)-(R3:Int)+c*I3 := by omega
 have h4' : I3=(C4:Int)*(2:Int)^n-(R4:Int)-f*(E:Int) := by omega
 have hraw :
   (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
       (L1:Int)*(n+6+3*s:Int)-(O1:Int) =
   a*((C2:Int)*(2^n:Int)-(R2:Int)+
     b*((C3:Int)*(2^n:Int)-(R3:Int)+
       c*((C4:Int)*(2:Int)^n-(R4:Int)-f*(E:Int)))) := by
   rw [h2'] at h1
   rw [h3'] at h1
   rw [h4'] at h1
   exact h1.symm
 have hR1root : (L1:Int)*(n+6+3*s:Int)-(O1:Int)-(d:Int)=(R1:Int) := by omega
 have hM1 : (C1:Int)*((8:Nat)^s:Int)*(p:Int)=(C1:Int)*(2^n:Int) := by
   rw [Int.mul_assoc,hPi]
 have hM2 : (C2:Int)*(((8:Nat)^s:Int)*a)*(p:Int)=a*((C2:Int)*(2^n:Int)) := by
   rw [←hPi]
   ac_rfl
 have hM3 : (C3:Int)*(((8:Nat)^s:Int)*(a*b))*(p:Int)=
     a*(b*((C3:Int)*(2^n:Int))) := by
   rw [←hPi]
   ac_rfl
 have hM4 : (C4:Int)*(((8:Nat)^s:Int)*((a*b)*c))*(p:Int)=
     a*(b*(c*((C4:Int)*(2^n:Int)))) := by
   rw [←hPi]
   ac_rfl
 have hKprod : ((K:Int)+98)*(p:Int)=
   (C1:Int)*(2^n:Int)+a*((C2:Int)*(2^n:Int))+
     a*(b*((C3:Int)*(2^n:Int)))+
     a*(b*(c*((C4:Int)*(2^n:Int)))) := by
   have hh := congrArg (fun x:Int=>x*(p:Int)) hKi
   simp only [Int.add_mul] at hh
   rw [hM1,hM2,hM3,hM4] at hh
   simpa only [Int.add_mul] using hh
 have hrawExpand :
   (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
       (L1:Int)*(n+6+3*s:Int)-(O1:Int) =
     a*((C2:Int)*(2^n:Int))-a*(R2:Int)+
     a*(b*((C3:Int)*(2^n:Int)))-a*(b*(R3:Int))+
     a*(b*(c*((C4:Int)*(2^n:Int))))-a*(b*(c*(R4:Int)))-
     a*(b*(c*(f*(E:Int)))) := by
   rw [hraw]
   simp only [Int.mul_add,Int.mul_sub]
   omega
 have hrootExpand :
   (98:Int)*(p:Int)-(C1:Int)*(2^n:Int)+(R1:Int) =
     a*((C2:Int)*(2^n:Int))-a*(R2:Int)+
     a*(b*((C3:Int)*(2^n:Int)))-a*(b*(R3:Int))+
     a*(b*(c*((C4:Int)*(2^n:Int))))-a*(b*(c*(R4:Int)))-
     a*(b*(c*(f*(E:Int)))) := by
   omega
 have hexp :
   a*(b*(c*(f*(E:Int)+(R4:Int))+(R3:Int))+(R2:Int)) =
     a*(b*(c*(f*(E:Int))))+a*(b*(c*(R4:Int)))+
       a*(b*(R3:Int))+a*(R2:Int) := by
   simp only [Int.mul_add]
 have hKprod' : (K:Int)*(p:Int)+98*(p:Int)=
   (C1:Int)*(2^n:Int)+a*((C2:Int)*(2^n:Int))+
     a*(b*((C3:Int)*(2^n:Int)))+
     a*(b*(c*((C4:Int)*(2^n:Int)))) := by
   simpa only [Int.add_mul] using hKprod
 have hEqI : (K:Int)*(p:Int)=
   a*(b*(c*(f*(E:Int)+(R4:Int))+(R3:Int))+(R2:Int))+(R1:Int) := by
   rw [hexp]
   omega
 have hEqNat : K*p=
   (2^alpha*8^u)*((2^beta*8^v)*
     ((2^gamma*8^w)*((2^delta*8^r)*E+R4)+R3)+R2)+R1 := by
   apply Int.ofNat_inj.mp
   simpa [a,b,c,f,Int.natCast_add,Int.natCast_mul,Int.natCast_pow] using hEqI
 have hExp : p=2^(n-3*s) := by
   have h8 : (8:Nat)^s=2^(3*s) := by
     simpa only [show (8:Nat)=2^3 by decide] using
       (Nat.pow_mul 2 3 s).symm
   have hq : 1≤(8:Nat)^s := Nat.one_le_pow s 8 (by decide)
   have hcomp : (8:Nat)^s*2^(n-3*s)=2^n := by
     rw [h8,←Nat.pow_add]
     congr 1
     omega
   exact Nat.eq_of_mul_eq_mul_left (by omega : 0<(8:Nat)^s) (by
     rw [hP,hcomp])
 exact four_layer_abstract_barrier n s u v w r alpha beta gamma delta
   (8^s) p (2^alpha) (2^beta) (2^gamma) (2^delta)
   K R1 R2 R3 R4 E hn hP ⟨d,hD⟩ rfl hExp rfl rfl rfl rfl
   hKlower hR1pos hR1bound hR2pos hR2bound hR3pos hR3bound
   hR4pos hR4bound hEbound hEqNat

#print axioms no_four_shallow_energies

end BB6.Agent43FourShallowAbstract
