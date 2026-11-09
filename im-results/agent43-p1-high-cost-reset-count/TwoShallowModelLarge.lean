import RootTwoDivisor
import TwoShallowNumeric
import TwoShallowFiniteBridge
import SmallIndexEnergyCutoff

namespace BB6.Agent43TwoShallowModel
open BB6.Agent43TwoRun BB6.Agent43TwoLayer

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- General two-shallow model bridge, using a cubic gap at large indices
and kernel-checked finite congruences for 14 <= n < 48. -/
theorem no_two_shallow_model_from_source_coefficients
    (n s u r alpha beta C1 C2 L1 L2 O1 O2 t1 t2 : Nat)
    (hn : 14≤n) (ht1 : t1≤1) (ht2 : t2≤1)
    (hprofile1 : (alpha,C1,L1,O1)=BB6.Agent43TwoShallowFinite.triple t1)
    (hprofile2 : (beta,C2,L2,O2)=BB6.Agent43TwoShallowFinite.triple t2)
    (ha1 : 1≤alpha) (ha2 : alpha≤2)
    (hb1 : 1≤beta) (hb2 : beta≤2)
    (hc1min : 392≤C1) (hc2min : 392≤C2)
    (hl1min : 56≤L1) (hl1max : L1≤84)
    (hl2min : 56≤L2) (hl2max : L2≤84)
    (ho1 : O1≤232) (ho2 : O2≤232)
    (Wa Ba Wb Wc Bc Wd We Be : Int)
    (hpre : TwoRun ((2:Int)^n)
      (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s Wa Ba)
    (hSh1 : ((2:Int)^alpha)*I ((2:Int)^n) Wb (Ba+(alpha:Int)) =
       I ((2:Int)^n) Wa Ba-(C1:Int)*(2:Int)^n+(L1:Int)*Ba-(O1:Int))
    (hmid : TwoRun ((2:Int)^n) Wb (Ba+(alpha:Int)) u Wc Bc)
    (hSh2 : ((2:Int)^beta)*I ((2:Int)^n) Wd (Bc+(beta:Int)) =
       I ((2:Int)^n) Wc Bc-(C2:Int)*(2:Int)^n+(L2:Int)*Bc-(O2:Int))
    (hsuffix : TwoRun ((2:Int)^n) Wd (Bc+(beta:Int)) r We Be)
    (hwall : We=12*(2:Int)^n) : False := by
  let P : Int := (2:Int)^n
  let N : Int := n
  let q : Nat := 8^s
  let a : Nat := 2^alpha
  let b : Nat := 2^beta
  let z : Nat := 8^u
  let v : Nat := 8^r
  let T1 : Nat := n+6+3*s
  let T2 : Nat := n+6+3*s+alpha+3*u
  let T3 : Nat := n+6+3*s+alpha+3*u+beta+3*r
  have hn14 :14≤n := by omega
  obtain ⟨hs,hqDdiv⟩ := root_two_prefix_divisor n s Wa Ba hn14 hpre
  have hqPdiv : (8:Nat)^s ∣ 2^n := by
    have hh : (8:Nat)^s=2^(3*s) := by
      simpa only [show (8:Nat)=2^3 by decide] using (Nat.pow_mul 2 3 s).symm
    rw [hh]
    exact Nat.pow_dvd_pow 2 hs
  obtain ⟨p,hp⟩ := hqPdiv
  obtain ⟨d,hd⟩ := hqDdiv
  have hpNat : q*p=2^n := by simpa [q,Nat.mul_comm] using hp.symm
  have hdNat : q*d=14*n+92 := by simpa [q,Nat.mul_comm] using hd.symm
  have hDle : d≤14*n+92 := by
    have hq1 : 1≤q := by dsimp [q]; exact Nat.one_le_pow s 8 (by decide)
    have hle : d ≤ q*d := by simpa using (Nat.mul_le_mul_right d hq1)
    omega
  have hpInt : (q:Int)*(p:Int)=P := by
    have hh := congrArg (fun x : Nat => (↑x:Int)) hpNat
    simpa [q,P,Int.natCast_mul,Int.natCast_pow] using hh
  have hdInt : (q:Int)*(d:Int)=14*N+92 := by
    have hh := congrArg (fun x : Nat => (↑x:Int)) hdNat
    simpa [q,N,Int.natCast_mul,Int.natCast_add,Int.natCast_pow] using hh
  have hqpos : 0<(q:Int) := by
    have h : 0<(8:Int)^s := Int.pow_pos (by decide)
    simpa [q] using h
  have henergyPre := run_energy P (14*P+2*N+4) (N+6) Wa Ba s hpre
  have hcostPre := run_cost P (14*P+2*N+4) (N+6) Wa Ba s hpre
  have hIroot : I P (14*P+2*N+4) (N+6) = 98*P-(14*N+92) := by
    unfold I
    omega
  rw [hIroot] at henergyPre
  have hIpre : I P Wa Ba=98*(p:Int)-(d:Int) := by
    have hh : (q:Int)*(98*(p:Int)-(d:Int))=98*P-(14*N+92) := by
      rw [Int.mul_sub]
      have hs2 : (q:Int)*(98*(p:Int))=98*P := by
        calc
          _=98*((q:Int)*(p:Int)) := by ac_rfl
          _=98*P := by rw [hpInt]
      omega
    have hqi : (q:Int)=(8:Int)^s := by rfl
    have hprod : (q:Int)*I P Wa Ba=98*P-(14*N+92) := by
      rw [hqi]
      exact henergyPre.symm
    have heq : (q:Int)*I P Wa Ba=(q:Int)*(98*(p:Int)-(d:Int)) := by
      omega
    exact Int.eq_of_mul_eq_mul_left (by omega : (q:Int) ≠ 0) heq
  have hcostMid := run_cost P Wb (Ba+(alpha:Int)) Wc Bc u hmid
  have hcostSuf := run_cost P Wd (Bc+(beta:Int)) We Be r hsuffix
  have hBa : Ba=(T1:Int) := by dsimp [T1]; omega
  have hBc : Bc=(T2:Int) := by dsimp [T1,T2]; omega
  have hBe : Be=(T3:Int) := by dsimp [T1,T2,T3]; omega
  let R1 : Nat := L1*T1-O1-d
  let R2 : Nat := L2*T2-O2
  let E : Nat := 112*T3-384
  let K : Nat := C1*q+C2*(q*(a*z))-98
  have hR1eq : R1+O1+d=L1*T1 := by
    dsimp [R1,T1]
    have hval : 56*(n+6)≤L1*(n+6+3*s) := Nat.mul_le_mul hl1min (by omega)
    omega
  have hR2eq : R2+O2=L2*T2 := by
    dsimp [R2,T2]
    have hval : 56*(n+6)≤L2*(n+6+3*s+alpha+3*u) :=
      Nat.mul_le_mul hl2min (by omega)
    omega
  have hEeq : E+384=112*T3 := by
    dsimp [E,T3]
    omega
  have hKeq : K+98=C1*q+C2*(q*(a*z)) := by
    dsimp [K]
    have hq1 : 1≤q := by dsimp [q]; exact Nat.one_le_pow s 8 (by decide)
    have hcLarge : 98≤C1*q := by
      have hmin := Nat.mul_le_mul_right q hc1min
      have hscale := Nat.mul_le_mul_left 392 hq1
      omega
    omega
  have hIntCost1 : I P Wb (Ba+(alpha:Int)) = (z:Int)*I P Wc Bc :=
    run_energy P Wb (Ba+(alpha:Int)) Wc Bc u hmid
  have hIntCost2 : I P Wd (Bc+(beta:Int)) = (v:Int)*I P We Be :=
    run_energy P Wd (Bc+(beta:Int)) We Be r hsuffix
  have hIE : I P We Be=-(E:Int) := by
    rw [hwall, hBe]
    dsimp [E,T3,I]
    have hEInt : (↑(112*T3-384):Int)=112*(T3:Int)-384 := by
      have hbound :384≤112*T3 := by dsimp [T3]; omega
      omega
    rw [hEInt]
    omega
  have hSh2' : I P Wc Bc = (C2:Int)*P -
      (((2:Int)^beta)*(v:Int)*(E:Int)+(L2:Int)*Bc-(O2:Int)) := by
    change ((2:Int)^beta)*I P Wd (Bc+(beta:Int)) =
        I P Wc Bc-(C2:Int)*P+(L2:Int)*Bc-(O2:Int) at hSh2
    rw [hIntCost2,hIE] at hSh2
    simp only [Int.mul_neg] at hSh2
    have hmul : ((2:Int)^beta)*((v:Int)*(E:Int)) =
        ((2:Int)^beta)*(v:Int)*(E:Int) := by ac_rfl
    rw [hmul] at hSh2
    omega
  have hSh1' : ((2:Int)^alpha)*(z:Int)*I P Wc Bc =
      98*(p:Int)-(d:Int)-(C1:Int)*P+(L1:Int)*Ba-(O1:Int) := by
    rw [hIntCost1] at hSh1
    rw [hIpre] at hSh1
    simpa only [Int.mul_assoc] using hSh1
  have hRaw : ((C1:Int)*P +
        ((2:Int)^alpha)*(z:Int)*((C2:Int)*P)-98*(p:Int)) =
      ((2:Int)^alpha)*(z:Int)*
        (((2:Int)^beta)*(v:Int)*(E:Int)+(L2:Int)*Bc-(O2:Int)) +
      (L1:Int)*Ba-(O1:Int)-(d:Int) := by
    rw [hSh2'] at hSh1'
    have hdistrib : ((2:Int)^alpha)*(z:Int)*
      ((C2:Int)*P-(((2:Int)^beta)*(v:Int)*(E:Int)+(L2:Int)*Bc-(O2:Int))) =
      ((2:Int)^alpha)*(z:Int)*((C2:Int)*P) -
      ((2:Int)^alpha)*(z:Int)*
        (((2:Int)^beta)*(v:Int)*(E:Int)+(L2:Int)*Bc-(O2:Int)) :=
      Int.mul_sub _ _ _
    rw [hdistrib] at hSh1'
    omega
  have haInt : (a:Int)=(2:Int)^alpha := by rfl
  have hbInt : (b:Int)=(2:Int)^beta := by rfl
  have hR1Int : (L1:Int)*Ba-(O1:Int)-(d:Int)=(R1:Int) := by
    have hh := congrArg (fun x:Nat => (↑x:Int)) hR1eq
    simp only [Int.natCast_add, Int.natCast_mul] at hh
    rw [hBa]
    omega
  have hR2Int : (L2:Int)*Bc-(O2:Int)=(R2:Int) := by
    have hh := congrArg (fun x:Nat => (↑x:Int)) hR2eq
    simp only [Int.natCast_add, Int.natCast_mul] at hh
    rw [hBc]
    omega
  have hKexpand : (K:Int)=(C1:Int)*(q:Int)+
      (C2:Int)*((q:Int)*((a:Int)*(z:Int)))-98 := by
    have hh := congrArg (fun x:Nat => (↑x:Int)) hKeq
    simp only [Int.natCast_add, Int.natCast_mul] at hh
    omega
  have hMul1 : ((C1:Int)*(q:Int))*(p:Int)=(C1:Int)*P := by
    calc
      _ = (C1:Int)*((q:Int)*(p:Int)) := by ac_rfl
      _ = (C1:Int)*P := by rw [hpInt]
  have hMul2 : ((C2:Int)*((q:Int)*((a:Int)*(z:Int))))*(p:Int) =
      ((2:Int)^alpha)*(z:Int)*((C2:Int)*P) := by
    rw [←hpInt,←haInt]
    ac_rfl
  have hKprod : (K:Int)*(p:Int) = ((C1:Int)*P +
        ((2:Int)^alpha)*(z:Int)*((C2:Int)*P)-98*(p:Int)) := by
    rw [hKexpand, Int.sub_mul, Int.add_mul, hMul1, hMul2]
  have hRaw2 : (K:Int)*(p:Int) =
      ((a:Int)*(z:Int))*((b:Int)*(v:Int)*(E:Int)+(R2:Int))+(R1:Int) := by
    rw [hKprod]
    rw [haInt,hbInt]
    have hRaw3 : ((C1:Int)*P +
        ((2:Int)^alpha)*(z:Int)*((C2:Int)*P)-98*(p:Int)) =
      ((2:Int)^alpha)*(z:Int)*
        (((2:Int)^beta)*(v:Int)*(E:Int)+(R2:Int)) +
      (L1:Int)*Ba-(O1:Int)-(d:Int) := by
      have hin : ((2:Int)^beta)*(v:Int)*(E:Int)+(L2:Int)*Bc-(O2:Int) =
          ((2:Int)^beta)*(v:Int)*(E:Int)+(R2:Int) := by omega
      simpa only [hin] using hRaw
    omega
  have hEqNat : K*p=(a*z)*(b*v*E+R2)+R1 := by
    have hh := congrArg (fun x :Nat => (↑x:Int))
      (show K*p=K*p from rfl)
    have hcast : (↑(K*p):Int)=(↑((a*z)*(b*v*E+R2)+R1):Int) := by
      simp only [Int.natCast_add, Int.natCast_mul]
      exact hRaw2
    exact Int.ofNat_inj.mp hcast
  by_cases h48 : 48≤n
  · exact no_two_shallow_numeric_48 n s u r p d alpha beta C1 C2 L1 L2 O1 O2
      K R1 R2 E h48 hs hpNat hdNat ha1 ha2 hb1 hb2 hc1min hc2min
      hl1min hl1max hl2min hl2max ho1 ho2
      (by simpa [T1] using hR1eq) (by simpa [T2] using hR2eq)
      (by simpa [T3] using hEeq)
      (by simpa [q,a,z] using hKeq) (by simpa [a,b,z,v] using hEqNat)
  · have hsSmall : s≤3 :=
      BB6.Agent43FiniteBridge.root_two_prefix_le_three n s Wa Ba hn (by omega) hpre
    exact BB6.Agent43TwoShallowFinite.no_small_numeric
      n s u r t1 t2 p d alpha beta C1 C2 L1 L2 O1 O2 K R1 R2 E
      hn (by omega) hsSmall ht1 ht2 hprofile1 hprofile2 hpNat hdNat
      (by simpa [T1] using hR1eq) (by simpa [T2] using hR2eq)
      (by simpa [T3] using hEeq)
      (by simpa [q,a,z] using hKeq) (by simpa [a,b,z,v] using hEqNat)

end BB6.Agent43TwoShallowModel