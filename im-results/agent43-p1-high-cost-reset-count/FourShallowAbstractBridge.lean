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


/-- A version of residue peeling that uses nondivisibility by the full
remaining power instead of a numerical smallness bound. -/
private theorem residue_peel_nodiv
 (e t K A R : Nat) (hpos : 0<R) (hnot : ¬ 2^e ∣ R)
 (heq : K*2^e = A*2^t+R) :
 ∃ d, t≤e ∧ R=2^t*d ∧ K*2^(e-t)=A+d ∧ d≤R ∧ 2^t≤R := by
 have htle : t≤e := by
   by_contra ht
   have hrev : e≤t := by omega
   have hdiv : 2^e ∣ 2^t := Nat.pow_dvd_pow 2 hrev
   have hleft : 2^e ∣ K*2^e := Nat.dvd_mul_left _ _
   have hright : 2^e ∣ A*2^t := by
     obtain ⟨w,hw⟩ := hdiv
     refine ⟨A*w, ?_⟩
     rw [hw]
     ac_rfl
   have hh := Nat.dvd_sub hleft hright
   have he : K*2^e-A*2^t=R := by omega
   rw [he] at hh
   exact hnot hh
 have hdiv : 2^t ∣ 2^e := Nat.pow_dvd_pow 2 htle
 have hleft : 2^t ∣ K*2^e := by
   obtain ⟨w,hw⟩ := hdiv
   refine ⟨K*w, ?_⟩
   rw [hw]
   ac_rfl
 have hright : 2^t ∣ A*2^t := Nat.dvd_mul_left _ _
 have hh := Nat.dvd_sub hleft hright
 have he : K*2^e-A*2^t=R := by omega
 rw [he] at hh
 obtain ⟨d,hd⟩ := hh
 have hpop : 2^t*2^(e-t)=2^e := by
   rw [←Nat.pow_add]
   congr 1
   omega
 have hq : K*2^(e-t)=A+d := by
   have htest : (2^t)*(K*2^(e-t))=(2^t)*(A+d) := by
     calc
       _ = K*2^e := by rw [←hpop]; ac_rfl
       _ = A*2^t+R := heq
       _ = (2^t)*(A+d) := by rw [hd]; simp [Nat.mul_add]; ac_rfl
   exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) htest
 have hle : d≤R := by
   have hpos2 : 1≤(2:Nat)^t := Nat.one_le_pow t 2 (by decide)
   have hv : d≤(2^t)*d := by simpa using (Nat.mul_le_mul_right d hpos2)
   rw [←hd] at hv
   exact hv
 exact ⟨d,htle,hd,hq,hle,Nat.le_of_dvd hpos ⟨d,hd⟩⟩

private theorem four_profile_alpha_eq
    (t alpha C L O : Nat) (ht : t≤1)
    (hpr : (alpha,C,L,O)=triple t) :
    fourProfileAlpha t=alpha := by
  rcases (show t=0 ∨ t=1 by omega) with h|h
  · subst t
    simp [fourProfileAlpha,triple] at hpr ⊢
    omega
  · subst t
    simp [fourProfileAlpha,triple] at hpr ⊢
    omega

private theorem four_profile_step_of_affine
    (t alpha u : Nat) (hα : fourProfileAlpha t=alpha) :
    fourProfileStep (alpha+3*u) t := by
  unfold fourProfileStep
  rw [hα]
  constructor
  · omega
  · have hsub : alpha+3*u-alpha=3*u := by omega
    rw [hsub]
    exact Nat.mod_eq_zero_of_dvd ⟨u,by omega⟩

private theorem four_exp_lt
    (x b k : Nat) (hpow : 2^x≤b) (hbound : b<2^k) : x<k := by
  by_contra hx
  have hk : k≤x := by omega
  have hp := Nat.pow_le_pow_right (show (2:Nat)>0 by decide) hk
  omega

/-- Finite four-shallow exclusion for 14 <= n <= 75.  The four finite
nondivisibility checks replace the large-n quintic estimate. -/
private theorem four_layer_finite_barrier
 (n s u v w r t1 t2 t3 t4 p d alpha beta gamma delta
  C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4 K R1 R2 R3 R4 E : Nat)
 (hn14 : 14≤n) (hn75 : n≤75) (hs : 3*s≤n)
 (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1) (ht4 : t4≤1)
 (hp1 : (alpha,C1,L1,O1)=triple t1)
 (hp2 : (beta,C2,L2,O2)=triple t2)
 (hp3 : (gamma,C3,L3,O3)=triple t3)
 (hp4 : (delta,C4,L4,O4)=triple t4)
 (hP : 8^s*p=2^n) (hD : 8^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*r))
 (hK : K+98 =
   C1*8^s+C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))))
 (hR1pos : 0<R1) (hR2pos : 0<R2) (hR3pos : 0<R3) (hR4pos : 0<R4)
 (heq : K*p =
   (2^alpha*8^u)*((2^beta*8^v)*
     ((2^gamma*8^w)*((2^delta*8^r)*E+R4)+R3)+R2)+R1) : False := by
  let x1 := alpha+3*u
  let x2 := beta+3*v
  let x3 := gamma+3*w
  let x4 := delta+3*r
  let e := n-3*s
  let A1 := 2^alpha*8^u
  let A2 := 2^beta*8^v
  let A3 := 2^gamma*8^w
  let A4 := 2^delta*8^r
  let T1 := n+6+3*s
  let T2 := T1+x1
  let T3 := T2+x2
  let T4 := T3+x3

  have h8 : (8:Nat)=2^3 := by decide
  have hpow8 : 8^s=2^(3*s) := by rw [h8,←Nat.pow_mul]
  have hExp : p=2^e := by
    have hcomp : 8^s*2^(n-3*s)=2^n := by
      rw [hpow8,←Nat.pow_add]
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) (by rw [hP,hcomp])
  have hDdiv : 8^s ∣ 14*n+92 := ⟨d,hD⟩
  have hqle : 8^s≤14*n+92 := Nat.le_of_dvd (by omega) hDdiv
  have hs3 : s≤3 := by
    by_contra h
    have hs4 : 4≤s := by omega
    have hpw := Nat.pow_le_pow_right (show (8:Nat)>0 by decide) hs4
    norm_num at hpw
    omega
  have hPmod : 2^n%8^s=0 := Nat.mod_eq_zero_of_dvd ⟨p,hP⟩
  have hDmod : (14*n+92)%8^s=0 := Nat.mod_eq_zero_of_dvd hDdiv
  have hrootDiv : fourRootDivides n s := ⟨hPmod,hDmod⟩
  have hdq : (14*n+92)/(8^s)=d := by
    rw [hD]
    exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))

  have hL1 : L1≤84 := by
    rcases (show t1=0 ∨ t1=1 by omega) with h|h
    · subst t1
      simp [triple] at hp1
      omega
    · subst t1
      simp [triple] at hp1
      omega
  have hL2 : L2≤84 := by
    rcases (show t2=0 ∨ t2=1 by omega) with h|h
    · subst t2
      simp [triple] at hp2
      omega
    · subst t2
      simp [triple] at hp2
      omega
  have hL3 : L3≤84 := by
    rcases (show t3=0 ∨ t3=1 by omega) with h|h
    · subst t3
      simp [triple] at hp3
      omega
    · subst t3
      simp [triple] at hp3
      omega
  have hL4 : L4≤84 := by
    rcases (show t4=0 ∨ t4=1 by omega) with h|h
    · subst t4
      simp [triple] at hp4
      omega
    · subst t4
      simp [triple] at hp4
      omega
  have hs3' : 3*s≤9 := Nat.mul_le_mul_left 3 hs3
  have hT1le : T1≤90 := by dsimp [T1]; omega
  have hR1formula : R1=L1*T1-O1-d := by
    dsimp [T1]
    omega
  have hR1bound : R1≤7560 := by
    have hprod : L1*T1≤84*90 := Nat.mul_le_mul hL1 hT1le
    omega
  have hrootEq : fourRootRem n s t1=R1 := by
    simp [fourRootRem,←hp1,hdq,T1]
    omega
  have hrootFin := four_root_no_overflow
    (⟨n-14,by omega⟩ : Fin 62) (⟨s,hs3⟩ : Fin 4)
    (⟨t1,ht1⟩ : Fin 2)
    (by simpa [Nat.sub_add_cancel hn14] using hrootDiv)
  have hrootMod : R1%2^e≠0 := by
    simpa [hrootEq,e,Nat.sub_add_cancel hn14] using hrootFin
  have hnot1 : ¬ 2^e∣R1 := by
    intro hdiv
    exact hrootMod (Nat.mod_eq_zero_of_dvd hdiv)

  have hA1 : A1=2^x1 := by
    dsimp [A1,x1]
    rw [h8,←Nat.pow_mul,Nat.pow_add]
  have hA2 : A2=2^x2 := by
    dsimp [A2,x2]
    rw [h8,←Nat.pow_mul,Nat.pow_add]
  have hA3 : A3=2^x3 := by
    dsimp [A3,x3]
    rw [h8,←Nat.pow_mul,Nat.pow_add]
  have hA4 : A4=2^x4 := by
    dsimp [A4,x4]
    rw [h8,←Nat.pow_mul,Nat.pow_add]
  have hEq0 : K*2^e=A1*(A2*(A3*(A4*E+R4)+R3)+R2)+R1 := by
    rw [hExp] at heq
    simpa [A1,A2,A3,A4] using heq
  have hEq1 : K*2^e=(A2*(A3*(A4*E+R4)+R3)+R2)*2^x1+R1 := by
    rw [hA1] at hEq0
    simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hEq0

  have hprof1 : fourProfileStep x1 t1 := by
    have hα := four_profile_alpha_eq t1 alpha C1 L1 O1 ht1 hp1
    simpa [x1] using four_profile_step_of_affine t1 alpha u hα
  obtain ⟨d1,hx1le,hR1div,hEq1',hd1le,hpow1le⟩ :=
    residue_peel_nodiv e x1 K (A2*(A3*(A4*E+R4)+R3)+R2) R1
      hR1pos hnot1 hEq1
  have hR1lt : R1<2^13 := by
    have hpow : 2^13=8192 := by norm_num
    omega
  have hx1lt : x1<13 := four_exp_lt x1 R1 13 hpow1le hR1lt
  have hx1bound : x1≤12 := by omega
  have hR1quot : fourRootRem n s t1/2^x1=d1 := by
    rw [hrootEq,hR1div]
    exact Nat.mul_div_cancel_left d1 (Nat.pow_pos (by decide))
  have hR1mod : R1%2^x1=0 := Nat.mod_eq_zero_of_dvd ⟨d1,hR1div⟩
  have hSecondFin := four_second_no_overflow
    (⟨n-14,by omega⟩ : Fin 62) (⟨s,hs3⟩ : Fin 4)
    (⟨t1,ht1⟩ : Fin 2) (⟨x1,hx1bound⟩ : Fin 13)
    (⟨t2,ht2⟩ : Fin 2)
    (by simpa [Nat.sub_add_cancel hn14] using hrootDiv)
    (by simpa [hrootEq,e,Nat.sub_add_cancel hn14] using hrootFin)
    (by simpa [e] using hx1le) hprof1 hR1mod
  let S2 := R2+d1
  have hR2formula : R2+O2=L2*(T1+x1) := by
    dsimp [T1,x1]
    exact hR2
  have hS2eq : fourSecondRem n s t1 x1 t2=S2 := by
    simp [fourSecondRem,S2,hR1quot,←hp2,hR2formula,T1]
    omega
  have hnot2mod : S2%2^(e-x1)≠0 := by
    simpa [hS2eq,e,Nat.sub_add_cancel hn14] using hSecondFin
  have hnot2 : ¬ 2^(e-x1)∣S2 := by
    intro hdiv
    exact hnot2mod (Nat.mod_eq_zero_of_dvd hdiv)
  have hEq2 : K*2^(e-x1)=(A3*(A4*E+R4)+R3)*2^x2+S2 := by
    calc
      K*2^(e-x1)=(A2*(A3*(A4*E+R4)+R3)+R2)+d1 := hEq1'
      _=(A3*(A4*E+R4)+R3)*2^x2+(R2+d1) := by
        rw [hA2]
        simp [Nat.mul_add]
        ac_rfl
      _=(A3*(A4*E+R4)+R3)*2^x2+S2 := by rfl
  have hS2pos : 0<S2 := by dsimp [S2]; omega
  obtain ⟨d2,hx2le,hS2div,hEq2',hd2le,hpow2le⟩ :=
    residue_peel_nodiv (e-x1) x2 K (A3*(A4*E+R4)+R3) S2
      hS2pos hnot2 hEq2
  have hT2le : T1+x1≤102 := by dsimp [T1]; omega
  have hR2le : R2≤8568 := by
    have hprod : L2*(T1+x1)≤84*102 := Nat.mul_le_mul hL2 hT2le
    omega
  have hS2le : S2≤16128 := by dsimp [S2]; omega
  have hS2lt : S2<2^14 := by
    have hpow : 2^14=16384 := by norm_num
    omega
  have hx2lt : x2<14 := four_exp_lt x2 S2 14 hpow2le hS2lt
  have hx2bound : x2≤13 := by omega
  have hS2quot : fourSecondRem n s t1 x1 t2/2^x2=d2 := by
    rw [hS2eq,hS2div]
    exact Nat.mul_div_cancel_left d2 (Nat.pow_pos (by decide))
  have hS2mod : S2%2^x2=0 := Nat.mod_eq_zero_of_dvd ⟨d2,hS2div⟩
  have hprof2 : fourProfileStep x2 t2 := by
    have hβ := four_profile_alpha_eq t2 beta C2 L2 O2 ht2 hp2
    simpa [x2] using four_profile_step_of_affine t2 beta v hβ
  have hThirdFin := four_third_no_overflow
    (⟨n-14,by omega⟩ : Fin 62) (⟨s,hs3⟩ : Fin 4)
    (⟨t1,ht1⟩ : Fin 2) (⟨x1,hx1bound⟩ : Fin 13)
    (⟨t2,ht2⟩ : Fin 2) (⟨x2,hx2bound⟩ : Fin 14)
    (⟨t3,ht3⟩ : Fin 2)
    (by simpa [Nat.sub_add_cancel hn14] using hrootDiv)
    (by simpa [hrootEq,e,Nat.sub_add_cancel hn14] using hrootFin)
    (by simpa [e] using hx1le) hprof1 hR1mod
    (by simpa [hS2eq,e,Nat.sub_add_cancel hn14] using hSecondFin)
    (by simpa [e] using hx2le) hprof2 hS2mod
  let S3 := R3+d2
  have hR3formula : R3+O3=L3*(T1+x1+x2) := by
    dsimp [T1,x1,x2]
    exact hR3
  have hS3eq : fourThirdRem n s t1 x1 t2 x2 t3=S3 := by
    simp [fourThirdRem,S3,hS2quot,←hp3,hR3formula,T1]
    omega
  have hnot3mod : S3%2^(e-x1-x2)≠0 := by
    simpa [hS3eq,e,Nat.sub_add_cancel hn14] using hThirdFin
  have hnot3 : ¬ 2^(e-x1-x2)∣S3 := by
    intro hdiv
    exact hnot3mod (Nat.mod_eq_zero_of_dvd hdiv)
  have hEq3 : K*2^(e-x1-x2)=(A4*E+R4)*2^x3+S3 := by
    calc
      K*2^(e-x1-x2)=(A3*(A4*E+R4)+R3)+d2 := hEq2'
      _=(A4*E+R4)*2^x3+(R3+d2) := by
        rw [hA3]
        simp [Nat.mul_add]
        ac_rfl
      _=(A4*E+R4)*2^x3+S3 := by rfl
  have hS3pos : 0<S3 := by dsimp [S3]; omega
  obtain ⟨d3,hx3le,hS3div,hEq3',hd3le,hpow3le⟩ :=
    residue_peel_nodiv (e-x1-x2) x3 K (A4*E+R4) S3
      hS3pos hnot3 hEq3
  have hT3le : T1+x1+x2≤115 := by dsimp [T1]; omega
  have hR3le : R3≤9660 := by
    have hprod : L3*(T1+x1+x2)≤84*115 := Nat.mul_le_mul hL3 hT3le
    omega
  have hS3le : S3≤25788 := by dsimp [S3]; omega
  have hS3lt : S3<2^15 := by
    have hpow : 2^15=32768 := by norm_num
    omega
  have hx3lt : x3<15 := four_exp_lt x3 S3 15 hpow3le hS3lt
  have hx3bound : x3≤14 := by omega
  have hS3quot : fourThirdRem n s t1 x1 t2 x2 t3/2^x3=d3 := by
    rw [hS3eq,hS3div]
    exact Nat.mul_div_cancel_left d3 (Nat.pow_pos (by decide))
  have hS3mod : S3%2^x3=0 := Nat.mod_eq_zero_of_dvd ⟨d3,hS3div⟩
  have hprof3 : fourProfileStep x3 t3 := by
    have hγ := four_profile_alpha_eq t3 gamma C3 L3 O3 ht3 hp3
    simpa [x3] using four_profile_step_of_affine t3 gamma w hγ
  have hFourthFin := four_fourth_finite_audit
    (⟨n-14,by omega⟩ : Fin 62) (⟨s,hs3⟩ : Fin 4)
    (⟨t1,ht1⟩ : Fin 2) (⟨x1,hx1bound⟩ : Fin 13)
    (⟨t2,ht2⟩ : Fin 2) (⟨x2,hx2bound⟩ : Fin 14)
    (⟨t3,ht3⟩ : Fin 2) (⟨x3,hx3bound⟩ : Fin 15)
    (⟨t4,ht4⟩ : Fin 2)
    (by simpa [Nat.sub_add_cancel hn14] using hrootDiv)
    (by simpa [hrootEq,e,Nat.sub_add_cancel hn14] using hrootFin)
    (by simpa [e] using hx1le) hprof1 hR1mod
    (by simpa [hS2eq,e,Nat.sub_add_cancel hn14] using hSecondFin)
    (by simpa [e] using hx2le) hprof2 hS2mod
    (by simpa [hS3eq,e,Nat.sub_add_cancel hn14] using hThirdFin)
    (by simpa [e] using hx3le) hprof3 hS3mod
  let S4 := R4+d3
  have hR4formula : R4+O4=L4*(T1+x1+x2+x3) := by
    dsimp [T1,x1,x2,x3]
    exact hR4
  have hS4eq : fourFourthRem n s t1 x1 t2 x2 t3 x3 t4 = S4 := by
    simp [fourFourthRem,S4,hS3quot,←hp4,hR4formula,T1]
    omega
  have hnot4mod : S4%2^(e-x1-x2-x3)≠0 := by
    have h := hFourthFin.1
    simpa [hS4eq,e,Nat.sub_add_cancel hn14] using h
  have hnot4 : ¬ 2^(e-x1-x2-x3)∣S4 := by
    intro hdiv
    exact hnot4mod (Nat.mod_eq_zero_of_dvd hdiv)
  have hEq4 : K*2^(e-x1-x2-x3)=A4*E+S4 := by
    calc
      K*2^(e-x1-x2-x3)=(A4*E+R4)+d3 := hEq3'
      _=A4*E+(R4+d3) := by omega
      _=A4*E+S4 := by rfl
  have hS4pos : 0<S4 := by dsimp [S4]; omega
  obtain ⟨d4,hx4le,hS4div,hEq4',hd4le,hpow4le⟩ :=
    residue_peel_nodiv (e-x1-x2-x3) x4 K E S4 hS4pos hnot4 hEq4
  have hT4le : T1+x1+x2+x3≤129 := by dsimp [T1]; omega
  have hR4le : R4≤10836 := by
    have hprod : L4*(T1+x1+x2+x3)≤84*129 := Nat.mul_le_mul hL4 hT4le
    omega
  have hS4le : S4≤36624 := by dsimp [S4]; omega
  have hS4lt : S4<2^16 := by
    have hpow : 2^16=65536 := by norm_num
    omega
  have hx4lt : x4<16 := four_exp_lt x4 S4 16 hpow4le hS4lt
  have hx4bound : x4≤15 := by omega
  let Emax := fourEmax n s x1 x2 x3
  have hEbound : E≤Emax := by
    dsimp [Emax,fourEmax,x1,x2,x3,x4] at *
    omega
  have hKformula : fourCoeff s t1 x1 t2 x2 t3 x3 t4=K := by
    have hK' := hK
    rw [hA1,hA2,hA3] at hK'
    simp [fourCoeff,←hp1,←hp2,←hp3,←hp4]
    rw [←Nat.pow_add,←Nat.pow_add] at hK'
    simp only [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] at hK'
    omega
  have hfinal : K*2^(e-x1-x2-x3)>S4*(Emax+1) := by
    have h := hFourthFin.2
    simpa [hS4eq,hKformula,Emax,fourEmax,e,Nat.sub_add_cancel hn14] using h
  have hupper : K*2^(e-x1-x2-x3)≤S4*(Emax+1) := by
    rw [hEq4,hA4]
    have hAE : 2^x4*E≤S4*E := Nat.mul_le_mul_right E hpow4le
    have hSE : S4*E≤S4*Emax := Nat.mul_le_mul_left S4 hEbound
    calc
      2^x4*E+S4≤S4*E+S4 := Nat.add_le_add_right hAE S4
      _≤S4*Emax+S4 := Nat.add_le_add_right hSE S4
      _=S4*(Emax+1) := by rw [Nat.mul_add]; omega
  omega

/-- Four source-profiled shallow cocycles, separated by depth-two energy
divisions, imply an impossible terminal shifted-wall equation. -/
theorem no_four_shallow_energies
 (n s u v w r t1 t2 t3 t4 p d alpha beta gamma delta
  C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4 K R1 R2 R3 R4 E : Nat)
 (hn14 : 14≤n) (hs : 3*s≤n)
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
 by_cases hlarge : 76≤n
 · exact four_layer_abstract_barrier n s u v w r alpha beta gamma delta
     (8^s) p (2^alpha) (2^beta) (2^gamma) (2^delta)
     K R1 R2 R3 R4 E hlarge hP ⟨d,hD⟩ rfl hExp rfl rfl rfl rfl
     hKlower hR1pos hR1bound hR2pos hR2bound hR3pos hR3bound
     hR4pos hR4bound hEbound hEqNat
 · have hn75 : n≤75 := by omega
   exact four_layer_finite_barrier n s u v w r t1 t2 t3 t4 p d
     alpha beta gamma delta C1 C2 C3 C4 L1 L2 L3 L4 O1 O2 O3 O4
     K R1 R2 R3 R4 E hn14 hn75 hs ht1 ht2 ht3 ht4 hp1 hp2 hp3 hp4
     hP hD hR1 hR2 hR3 hR4 hE hK hR1pos hR2pos hR3pos hR4pos hEqNat

#print axioms no_four_shallow_energies

end BB6.Agent43FourShallowAbstract
