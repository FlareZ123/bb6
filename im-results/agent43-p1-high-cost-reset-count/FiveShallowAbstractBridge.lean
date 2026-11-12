import FiveLayerBarrier
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43FiveShallowAbstract

open BB6.Agent43FiveLayer

set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

/-- Five source-profiled shallow cocycles, separated by six genuine
depth-two energy runs, force the five-layer scalar wall equation. -/
theorem no_five_shallow_energies
 (n s u v w x r alpha beta gamma delta epsilon
  p d C1 C2 C3 C4 C5 L1 L2 L3 L4 L5 O1 O2 O3 O4 O5
  K R1 R2 R3 R4 R5 E : Nat)
 (hn : 83≤n) (hs : 3*s≤n)
 (halpha : 1≤alpha) (hbeta : 1≤beta) (hgamma : 1≤gamma)
 (hdelta : 1≤delta) (hepsilon : 1≤epsilon)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hR5 : R5+O5=L5*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x))
 (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x+epsilon+3*r))
 (hK : K+98 =
   C1*8^s+
   C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w)))+
   C5*(8^s*((((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))*(2^delta*8^x))))
 (hKlower : 392*(8^s*((2^alpha*8^u)*
   ((2^beta*8^v)*((2^gamma*8^w)*(2^delta*8^x)))))≤K)
 (hR1pos : 0<R1) (hR1bound : R1≤168*(n+2))
 (hR2pos : 0<R2)
 (hR2bound : alpha+3*u≤n-3*s → R2≤168*(n+2))
 (hR3pos : 0<R3)
 (hR3bound : alpha+3*u+beta+3*v≤n-3*s → R3≤168*(n+2))
 (hR4pos : 0<R4)
 (hR4bound : alpha+3*u+beta+3*v+gamma+3*w≤n-3*s → R4≤168*(n+2))
 (hR5pos : 0<R5)
 (hR5bound : alpha+3*u+beta+3*v+gamma+3*w+delta+3*x≤n-3*s →
   R5≤168*(n+2))
 (hEbound : alpha+3*u+beta+3*v+gamma+3*w+delta+3*x+epsilon+3*r≤n-3*s →
   E+1≤224*(n+2))
 (J1 I1 J2 I2 J3 I3 J4 I4 J5 : Int)
 (hSh1 : ((2:Int)^alpha)*J1 =
   (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
     (L1:Int)*(n+6+3*s:Int)-(O1:Int))
 (hMid1 : J1=(8:Int)^u*I1)
 (hSh2 : ((2:Int)^beta)*J2 =
   I1-(C2:Int)*(2^n:Int)+
     (L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int))
 (hMid2 : J2=(8:Int)^v*I2)
 (hSh3 : ((2:Int)^gamma)*J3 =
   I2-(C3:Int)*(2^n:Int)+
     (L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int)-(O3:Int))
 (hMid3 : J3=(8:Int)^w*I3)
 (hSh4 : ((2:Int)^delta)*J4 =
   I3-(C4:Int)*(2:Int)^n+
     (L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int)-(O4:Int))
 (hMid4 : J4=(8:Int)^x*I4)
 (hSh5 : ((2:Int)^epsilon)*J5 =
   I4-(C5:Int)*(2:Int)^n+
     (L5:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x:Int)-(O5:Int))
 (hLast : J5=-((8:Int)^r*(E:Int))) : False := by
 let a : Int := (2:Int)^alpha*(8:Int)^u
 let b : Int := (2:Int)^beta*(8:Int)^v
 let c : Int := (2:Int)^gamma*(8:Int)^w
 let f : Int := (2:Int)^delta*(8:Int)^x
 let g : Int := (2:Int)^epsilon*(8:Int)^r
 have hPi : ((8:Nat)^s:Int)*(p:Int)=(2:Int)^n := by exact_mod_cast hP
 have hR1i : (R1:Int)+(O1:Int)+(d:Int)=(L1:Int)*(n+6+3*s:Int) := by
   exact_mod_cast hR1
 have hR2i : (R2:Int)+(O2:Int)=
     (L2:Int)*(n+6+3*s+alpha+3*u:Int) := by exact_mod_cast hR2
 have hR3i : (R3:Int)+(O3:Int)=
     (L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int) := by exact_mod_cast hR3
 have hR4i : (R4:Int)+(O4:Int)=
     (L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int) := by
   exact_mod_cast hR4
 have hR5i : (R5:Int)+(O5:Int)=
     (L5:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x:Int) := by
   exact_mod_cast hR5
 have hKi : (K:Int)+98 =
   (C1:Int)*((8:Nat)^s:Int)+(C2:Int)*(((8:Nat)^s:Int)*a)+
   (C3:Int)*(((8:Nat)^s:Int)*(a*b))+
   (C4:Int)*(((8:Nat)^s:Int)*((a*b)*c))+
   (C5:Int)*(((8:Nat)^s:Int)*(((a*b)*c)*f)) := by
   have hh := congrArg (fun x:Nat=>(x:Int)) hK
   simpa [a,b,c,f,Int.natCast_add,Int.natCast_mul,Int.natCast_pow] using hh
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
 have h4 : f*I4=I3-(C4:Int)*(2^n:Int)+(R4:Int) := by
   rw [hMid4] at hSh4
   have hx : ((2:Int)^delta)*((8:Int)^x*I4)=f*I4 := by
     dsimp [f]
     rw [Int.mul_assoc]
   rw [hx] at hSh4
   omega
 have hlast : ((2:Int)^epsilon)*J5=-(g*(E:Int)) := by
   rw [hLast]
   dsimp [g]
   simp only [Int.mul_neg,Int.neg_mul]
   ac_rfl
 have hR5shift :
     (L5:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x:Int)-
       (O5:Int)=(R5:Int) := by
   omega
 have hSh5' : ((2:Int)^epsilon)*J5 =
     I4-(C5:Int)*(2:Int)^n+(R5:Int) := by
   omega
 have hneg5 : -(g*(E:Int))=I4-(C5:Int)*(2:Int)^n+(R5:Int) := by
   calc
     -(g*(E:Int))=((2:Int)^epsilon)*J5 := hlast.symm
     _=I4-(C5:Int)*(2:Int)^n+(R5:Int) := hSh5'
 have h5 : g*(E:Int)=(C5:Int)*(2:Int)^n-(R5:Int)-I4 := by omega
 have h2' : I1=(C2:Int)*(2^n:Int)-(R2:Int)+b*I2 := by omega
 have h3' : I2=(C3:Int)*(2^n:Int)-(R3:Int)+c*I3 := by omega
 have h4' : I3=(C4:Int)*(2^n:Int)-(R4:Int)+f*I4 := by omega
 have h5' : I4=(C5:Int)*(2:Int)^n-(R5:Int)-g*(E:Int) := by omega
 have hraw :
   (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
       (L1:Int)*(n+6+3*s:Int)-(O1:Int) =
   a*((C2:Int)*(2^n:Int)-(R2:Int)+
     b*((C3:Int)*(2^n:Int)-(R3:Int)+
       c*((C4:Int)*(2:Int)^n-(R4:Int)+
         f*((C5:Int)*(2:Int)^n-(R5:Int)-g*(E:Int))))) := by
   rw [h2'] at h1
   rw [h3'] at h1
   rw [h4'] at h1
   rw [h5'] at h1
   exact h1.symm
 have hR1root : (L1:Int)*(n+6+3*s:Int)-(O1:Int)-(d:Int)=(R1:Int) := by
   omega
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
 have hM5 : (C5:Int)*(((8:Nat)^s:Int)*(((a*b)*c)*f))*(p:Int)=
     a*(b*(c*(f*((C5:Int)*(2^n:Int))))) := by
   rw [←hPi]
   ac_rfl
 have hKprod : ((K:Int)+98)*(p:Int)=
   (C1:Int)*(2^n:Int)+a*((C2:Int)*(2^n:Int))+
     a*(b*((C3:Int)*(2^n:Int)))+
     a*(b*(c*((C4:Int)*(2^n:Int))))+
     a*(b*(c*(f*((C5:Int)*(2^n:Int))))) := by
   have hh := congrArg (fun x:Int=>x*(p:Int)) hKi
   simp only [Int.add_mul] at hh
   rw [hM1,hM2,hM3,hM4,hM5] at hh
   simpa only [Int.add_mul] using hh
 have hrawExpand :
   (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
       (L1:Int)*(n+6+3*s:Int)-(O1:Int) =
     a*((C2:Int)*(2^n:Int))-a*(R2:Int)+
     a*(b*((C3:Int)*(2^n:Int)))-a*(b*(R3:Int))+
     a*(b*(c*((C4:Int)*(2^n:Int))))-a*(b*(c*(R4:Int)))+
     a*(b*(c*(f*((C5:Int)*(2^n:Int)))))-a*(b*(c*(f*(R5:Int))))-
     a*(b*(c*(f*(g*(E:Int))))) := by
   rw [hraw]
   simp only [Int.mul_add,Int.mul_sub]
   omega
 have hrootExpand :
   (98:Int)*(p:Int)-(C1:Int)*(2^n:Int)+(R1:Int) =
     a*((C2:Int)*(2^n:Int))-a*(R2:Int)+
     a*(b*((C3:Int)*(2^n:Int)))-a*(b*(R3:Int))+
     a*(b*(c*((C4:Int)*(2^n:Int))))-a*(b*(c*(R4:Int)))+
     a*(b*(c*(f*((C5:Int)*(2^n:Int)))))-a*(b*(c*(f*(R5:Int))))-
     a*(b*(c*(f*(g*(E:Int))))) := by
   omega
 have hexp :
   a*(b*(c*(f*(g*(E:Int)+(R5:Int))+(R4:Int))+(R3:Int))+(R2:Int)) =
     a*(b*(c*(f*(g*(E:Int)))+a*0)+0) := by
   simp only [Int.mul_add]
 have hKprod' : (K:Int)*(p:Int)+98*(p:Int)=
   (C1:Int)*(2^n:Int)+a*((C2:Int)*(2^n:Int))+
     a*(b*((C3:Int)*(2^n:Int)))+
     a*(b*(c*((C4:Int)*(2^n:Int))))+
     a*(b*(c*(f*((C5:Int)*(2^n:Int))))) := by
   simpa only [Int.add_mul] using hKprod
 have hEqI : (K:Int)*(p:Int)=
   a*(b*(c*(f*(g*(E:Int)+(R5:Int))+(R4:Int))+(R3:Int))+(R2:Int))+(R1:Int) := by
   rw [hexp]
   omega
 have hEqNat : K*p =
   (2^alpha*8^u)*((2^beta*8^v)*
     ((2^gamma*8^w)*((2^delta*8^x)*
       ((2^epsilon*8^r)*E+R5)+R4)+R3)+R2)+R1 := by
   apply Int.ofNat_inj.mp
   simpa [a,b,c,f,g,Int.natCast_add,Int.natCast_mul,Int.natCast_pow] using hEqI
 have hExp : p=2^(n-3*s) := by
   have h8 : (8:Nat)^s=2^(3*s) := by
     simpa only [show (8:Nat)=2^3 by decide] using
       (Nat.pow_mul 2 3 s).symm
   have hcomp : (8:Nat)^s*2^(n-3*s)=2^n := by
     rw [h8,←Nat.pow_add]
     congr 1
     omega
   exact Nat.eq_of_mul_eq_mul_left (by omega : 0<(8:Nat)^s) (by
     rw [hP,hcomp])
 exact five_layer_abstract_barrier
   n s u v w x r alpha beta gamma delta epsilon
   (8^s) p (2^alpha) (2^beta) (2^gamma) (2^delta) (2^epsilon)
   K R1 R2 R3 R4 R5 E hn hP ⟨d,hD⟩ rfl hExp rfl rfl rfl rfl rfl
   halpha hbeta hgamma hdelta hepsilon
   hKlower hR1pos hR1bound hR2pos hR2bound hR3pos hR3bound
   hR4pos hR4bound hR5pos hR5bound hEbound hEqNat

#print axioms no_five_shallow_energies

end BB6.Agent43FiveShallowAbstract
