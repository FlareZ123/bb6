import ThreeShallowSourceModel
import TwoShallowModelLarge
import OneShallowModelOne
import RightFiveEnergyStep
import InverseIff

namespace BB6.Agent43SourceWord
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent50Energy BB6.Agent43TwoRun

/-- Exact finite sequence of original P1 inverseAt steps, all of depth two.
Its start may be arbitrary; no copied scalar transition is assumed. -/
inductive SourceTwoChain (n : Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop where
  | empty (b d m : Nat) : SourceTwoChain n 0 b d m b d m
  | append (s b d m B D M k c : Nat)
      (h : SourceTwoChain n s b d m B D M)
      (hb : 8 ≤ B) (hb4 : B % 4 = 0) (hd : D % 2 = 1)
      (hi : inverseAt B D 2 = some (k,c))
      (hk : 2 ≤ k) (hc : c % 2 = 1) :
      SourceTwoChain n (s+1) b d m (2*k-4) (c+4) (M+3)

private theorem two_chain_mass (n s b d m B D M : Nat)
    (h : SourceTwoChain n s b d m B D M)
    (hmass : b+d+2*m+2*n+13=14*2^n) :
    B+D+2*M+2*n+13=14*2^n := by
  induction h with
  | empty => exact hmass
  | append s b d m B D M k c prev hb hb4 hd hi hk hc ih =>
    have hprev := ih hmass
    have hInv := (inverseAt_iff_power_mass B D 2 k c (by omega) hb4 hd).mp hi
    have hMass : 2*k+c+2*2+2=B+D := by omega
    omega

private theorem two_chain_model (n s b d m B D M : Nat)
    (h : SourceTwoChain n s b d m B D M)
    (hmass : b+d+2*m+2*n+13=14*2^n) :
    TwoRun ((2:Int)^n)
      ((b:Int)+4*(m:Int)+4*(n:Int)+20) ((m:Int)+(n:Int)+6)
      s ((B:Int)+4*(M:Int)+4*(n:Int)+20) ((M:Int)+(n:Int)+6) := by
  induction h with
  | empty => exact TwoRun.done _ _
  | append s b d m B D M k c prev hb hb4 hd hi hk hc ih =>
    have hm := two_chain_mass n s b d m B D M prev hmass
    have hInv := (inverseAt_iff_power_mass B D 2 k c (by omega) hb4 hd).mp hi
    have hMass : 2*k+c+2*2+2=B+D := by omega
    have hcocycle := two_step_cocycle n B D M k c hm hb4 hInv.1 hMass
    have hcocycleInt :
        8*((↑(2*k-4):Int)+4*(↑(M+3):Int)+4*(n:Int)+20) =
        ((B:Int)+4*(M:Int)+4*(n:Int)+20)+
          84*(2:Int)^n+16*((M:Int)+(n:Int)+6) := by
      exact_mod_cast hcocycle
    have hmodel := TwoRun.step
      ((b:Int)+4*(m:Int)+4*(n:Int)+20) ((m:Int)+(n:Int)+6)
      ((B:Int)+4*(M:Int)+4*(n:Int)+20) ((M:Int)+(n:Int)+6)
      ((↑(2*k-4):Int)+4*(↑(M+3):Int)+4*(n:Int)+20)
      s (ih hmass) hcocycleInt
    have hB : ((↑(M+3):Int)+(n:Int)+6) =
        ((M:Int)+(n:Int)+6)+3 := by omega
    rw [hB]
    exact hmodel

/-- Public original-inverseAt interface for translating any finite depth-two
source run into its exact affine scalar TwoRun. -/
theorem source_two_chain_model (n s b d m B D M : Nat)
    (h : SourceTwoChain n s b d m B D M)
    (hmass : b+d+2*m+2*n+13=14*2^n) :
    TwoRun ((2:Int)^n)
      ((b:Int)+4*(m:Int)+4*(n:Int)+20) ((m:Int)+(n:Int)+6)
      s ((B:Int)+4*(M:Int)+4*(n:Int)+20) ((M:Int)+(n:Int)+6) :=
  two_chain_model n s b d m B D M h hmass

private theorem shallow_zero (n B D M k c : Nat)
    (hmass : B+D+2*M+2*n+13=14*2^n)
    (hb : 8≤B) (hb4 : B%4=0) (hd : D%2=1)
    (hi : inverseAt B D 0=some (k,c))
    (hk : 2≤k) (hc : c%2=1) :
    2*((↑(2*k-4):Int)+4*(↑(M+1):Int)+4*(n:Int)+20)=
      ((B:Int)+4*(M:Int)+4*(n:Int)+20)+4*((M:Int)+(n:Int)+6)-8 := by
  have hInv := (inverseAt_iff_power_mass B D 0 k c (by omega) hb4 hd).mp hi
  have hhalf : 2*(B/2)=B := by omega
  have hp : D+B/2+3=c+3 := by simpa using hInv.1
  have hm : 2*k+c+2=B+D := by omega
  have hNat :
      2*((2*k-4)+4*(M+1)+4*n+20)+8=
        (B+4*M+4*n+20)+4*(M+n+6) := by omega
  have hInt :
      2*((↑(2*k-4):Int)+4*(↑(M+1):Int)+4*(n:Int)+20)+8=
        ((B:Int)+4*(M:Int)+4*(n:Int)+20)+4*((M:Int)+(n:Int)+6) := by
    exact_mod_cast hNat
  omega

private theorem shallow_one (n B D M k c : Nat)
    (hmass : B+D+2*M+2*n+13=14*2^n)
    (hb : 8≤B) (hb4 : B%4=0) (hd : D%2=1)
    (hi : inverseAt B D 1=some (k,c))
    (hk : 2≤k) (hc : c%2=1) :
    4*((↑(2*k-4):Int)+4*(↑(M+2):Int)+4*(n:Int)+20)=
      ((B:Int)+4*(M:Int)+4*(n:Int)+20)+28*(2:Int)^n+
        8*((M:Int)+(n:Int)+6)-8 := by
  have hInv := (inverseAt_iff_power_mass B D 1 k c (by omega) hb4 hd).mp hi
  have hhalf : 2*(B/2)=B := by omega
  have hp : D+B/2+3=2*(c+3) := by simpa using hInv.1
  have hm : 2*k+c+4=B+D := by omega
  have hNat :
      4*((2*k-4)+4*(M+2)+4*n+20)+8=
        (B+4*M+4*n+20)+28*2^n+8*(M+n+6) := by omega
  have hInt :
      4*((↑(2*k-4):Int)+4*(↑(M+2):Int)+4*(n:Int)+20)+8=
        ((B:Int)+4*(M:Int)+4*(n:Int)+20)+28*(2:Int)^n+
          8*((M:Int)+(n:Int)+6) := by
    exact_mod_cast hNat
  omega

/-- No exact shifted-wall hit along a genuine source word (2)^s 0 (2)^r. -/
theorem source_no_zero_word_wall
    (n s r bp dp mp k c be de me : Nat) (hn : 14≤n)
    (hpre : SourceTwoChain n s (14*2^n-2*n-16) 3 0 bp dp mp)
    (hb : 8≤bp) (hb4 : bp%4=0) (hd : dp%2=1)
    (hi : inverseAt bp dp 0=some (k,c))
    (hk : 2≤k) (hc : c%2=1)
    (hsuf : SourceTwoChain n r (2*k-4) (c+4) (mp+1) be de me)
    (hwall : be+4*me+4*n+20=12*2^n) : False := by
  have h100 : 100*n≤2^n := BB6.Agent50RightFiveTwo.hundred_mul_le_pow n hn
  have hroot : (14*2^n-2*n-16)+3+2*0+2*n+13=14*2^n := by omega
  have hmass := two_chain_mass n s _ _ _ _ _ _ hpre hroot
  have hrootModel := two_chain_model n s _ _ _ _ _ _ hpre hroot
  have hnextMass : (2*k-4)+(c+4)+2*(mp+1)+2*n+13=14*2^n := by
    have hInv := (inverseAt_iff_power_mass bp dp 0 k c (by omega) hb4 hd).mp hi
    have hm : 2*k+c+2=bp+dp := by omega
    omega
  have htail := two_chain_model n r _ _ _ _ _ _ hsuf hnextMass
  have hshallow := shallow_zero n bp dp mp k c hmass hb hb4 hd hi hk hc
  have hrootModel' : TwoRun ((2:Int)^n)
      (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s
      ((bp:Int)+4*(mp:Int)+4*(n:Int)+20) ((mp:Int)+(n:Int)+6) := by
    have hrootEq :
        ((↑(14*2^n-2*n-16):Int)+4*(n:Int)+20) =
          14*(2:Int)^n+2*(n:Int)+4 := by
      have hNat : (14*2^n-2*n-16)+4*n+20 = 14*2^n+2*n+4 := by omega
      exact_mod_cast hNat
    have hW : ((↑(14*2^n-2*n-16):Int)+4*(0:Int)+4*(n:Int)+20) =
        14*(2:Int)^n+2*(n:Int)+4 := by omega
    have hB : ((0:Int)+(n:Int)+6) = ((n:Int)+6) := by omega
    simp at hrootModel
    rw [hrootEq] at hrootModel
    exact hrootModel
  have hwallInt :
      ((be:Int)+4*(me:Int)+4*(n:Int)+20)=12*(2:Int)^n := by
    exact_mod_cast hwall
  exact no_scalar_zero_word_wall_from_root n s r hn
    ((bp:Int)+4*(mp:Int)+4*(n:Int)+20) ((mp:Int)+(n:Int)+6)
    ((↑(2*k-4):Int)+4*(↑(mp+1):Int)+4*(n:Int)+20)
    ((be:Int)+4*(me:Int)+4*(n:Int)+20) ((me:Int)+(n:Int)+6)
    hrootModel' hshallow (by
      have hB : ((↑(mp+1):Int)+(n:Int)+6) =
          ((mp:Int)+(n:Int)+6)+1 := by omega
      rw [hB] at htail
      exact htail) hwallInt

/-- No exact shifted-wall hit along a genuine source word (2)^s 1 (2)^r. -/
theorem source_no_one_word_wall
    (n s r bp dp mp k c be de me : Nat) (hn : 14≤n)
    (hpre : SourceTwoChain n s (14*2^n-2*n-16) 3 0 bp dp mp)
    (hb : 8≤bp) (hb4 : bp%4=0) (hd : dp%2=1)
    (hi : inverseAt bp dp 1=some (k,c))
    (hk : 2≤k) (hc : c%2=1)
    (hsuf : SourceTwoChain n r (2*k-4) (c+4) (mp+2) be de me)
    (hwall : be+4*me+4*n+20=12*2^n) : False := by
  have h100 : 100*n≤2^n := BB6.Agent50RightFiveTwo.hundred_mul_le_pow n hn
  have hroot : (14*2^n-2*n-16)+3+2*0+2*n+13=14*2^n := by omega
  have hmass := two_chain_mass n s _ _ _ _ _ _ hpre hroot
  have hrootModel := two_chain_model n s _ _ _ _ _ _ hpre hroot
  have hnextMass : (2*k-4)+(c+4)+2*(mp+2)+2*n+13=14*2^n := by
    have hInv := (inverseAt_iff_power_mass bp dp 1 k c (by omega) hb4 hd).mp hi
    have hm : 2*k+c+4=bp+dp := by omega
    omega
  have htail := two_chain_model n r _ _ _ _ _ _ hsuf hnextMass
  have hshallow := shallow_one n bp dp mp k c hmass hb hb4 hd hi hk hc
  have hrootModel' : TwoRun ((2:Int)^n)
      (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s
      ((bp:Int)+4*(mp:Int)+4*(n:Int)+20) ((mp:Int)+(n:Int)+6) := by
    have hrootEq :
        ((↑(14*2^n-2*n-16):Int)+4*(n:Int)+20) =
          14*(2:Int)^n+2*(n:Int)+4 := by
      have hNat : (14*2^n-2*n-16)+4*n+20 = 14*2^n+2*n+4 := by omega
      exact_mod_cast hNat
    have hW : ((↑(14*2^n-2*n-16):Int)+4*(0:Int)+4*(n:Int)+20) =
        14*(2:Int)^n+2*(n:Int)+4 := by omega
    have hB : ((0:Int)+(n:Int)+6) = ((n:Int)+6) := by omega
    simp at hrootModel
    rw [hrootEq] at hrootModel
    exact hrootModel
  have hwallInt :
      ((be:Int)+4*(me:Int)+4*(n:Int)+20)=12*(2:Int)^n := by
    exact_mod_cast hwall
  exact no_scalar_one_word_wall_from_root n s r hn
    ((bp:Int)+4*(mp:Int)+4*(n:Int)+20) ((mp:Int)+(n:Int)+6)
    ((↑(2*k-4):Int)+4*(↑(mp+2):Int)+4*(n:Int)+20)
    ((be:Int)+4*(me:Int)+4*(n:Int)+20) ((me:Int)+(n:Int)+6)
    hrootModel' hshallow (by
      have hB : ((↑(mp+2):Int)+(n:Int)+6) =
          ((mp:Int)+(n:Int)+6)+2 := by omega
      rw [hB] at htail
      exact htail) hwallInt

#print axioms source_no_zero_word_wall
#print axioms source_no_one_word_wall
end BB6.Agent43SourceWord

namespace BB6.Agent43SourceWord
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent50Energy BB6.Agent43TwoRun

/-- Exact coefficient profile of either genuine shallow source step,
relative to the same integer energy used in the two-run model. -/
theorem source_shallow_profile
    (n B D M t k c : Nat)
    (hmass : B+D+2*M+2*n+13=14*2^n)
    (hb : 8≤B) (hb4 : B%4=0) (hd : D%2=1)
    (hi : inverseAt B D t=some (k,c))
    (hk : 2≤k) (hc : c%2=1) (ht : t≤1) :
    ∃ alpha C L O : Nat,
      1≤alpha ∧ alpha≤2 ∧ 392≤C ∧ 56≤L ∧ L≤84 ∧ O≤232 ∧
      alpha=t+1 ∧
      (alpha,C,L,O)=BB6.Agent43TwoShallowFinite.triple t ∧
      ((2:Int)^alpha)* I ((2:Int)^n)
        ((↑(2*k-4):Int)+4*(↑(M+t+1):Int)+4*(n:Int)+20)
        ((M:Int)+(n:Int)+6+(alpha:Int)) =
      I ((2:Int)^n)
        ((B:Int)+4*(M:Int)+4*(n:Int)+20) ((M:Int)+(n:Int)+6) -
        (C:Int)*(2:Int)^n +(L:Int)*((M:Int)+(n:Int)+6)-(O:Int) := by
  let W : Int := (B:Int)+4*(M:Int)+4*(n:Int)+20
  let X : Int := (↑(2*k-4):Int)+4*(↑(M+t+1):Int)+4*(n:Int)+20
  let Z : Int := (M:Int)+(n:Int)+6
  by_cases htzero : t=0
  · subst t
    refine ⟨1,588,84,232,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by rfl,?_⟩
    have hW := shallow_zero n B D M k c hmass hb hb4 hd hi hk hc
    unfold I
    omega
  · have htone : t=1 := by omega
    subst t
    refine ⟨2,392,56,136,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by rfl,?_⟩
    have hW := shallow_one n B D M k c hmass hb hb4 hd hi hk hc
    unfold I
    omega

#print axioms BB6.Agent43SourceWord.source_shallow_profile
end BB6.Agent43SourceWord

namespace BB6.Agent43SourceWord
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent43TwoRun
open BB6.Agent43TwoShallowModel

/-- At every critical index n>=14, no original legal source inverse word
with exactly two shallow edges of depths 0 or 1, and otherwise only depth-two
edges, reaches the exact shifted wall.
Run lengths are unrestricted and may independently be zero. -/
theorem source_no_two_shallow_word_wall_all
    (n s u r t1 t2 bp dp mp k1 c1 B D M k2 c2 be de me : Nat)
    (hn : 14≤n) (ht1 : t1≤1) (ht2 : t2≤1)
    (hpre : SourceTwoChain n s (14*2^n-2*n-16) 3 0 bp dp mp)
    (hb1 : 8≤bp) (hb14 : bp%4=0) (hd1 : dp%2=1)
    (hi1 : inverseAt bp dp t1=some (k1,c1))
    (hk1 : 2≤k1) (hc1 : c1%2=1)
    (hmid : SourceTwoChain n u (2*k1-4) (c1+4) (mp+t1+1) B D M)
    (hb2 : 8≤B) (hb24 : B%4=0) (hd2 : D%2=1)
    (hi2 : inverseAt B D t2=some (k2,c2))
    (hk2 : 2≤k2) (hc2 : c2%2=1)
    (hsuf : SourceTwoChain n r (2*k2-4) (c2+4) (M+t2+1) be de me)
    (hwall : be+4*me+4*n+20=12*2^n) : False := by
  have hn14 : 14≤n := by omega
  have h100 :100*n≤2^n := BB6.Agent50RightFiveTwo.hundred_mul_le_pow n hn14
  have hrootMass : (14*2^n-2*n-16)+3+2*0+2*n+13=14*2^n := by omega
  have hpreMass := two_chain_mass n s _ _ _ _ _ _ hpre hrootMass
  have hpreModel := two_chain_model n s _ _ _ _ _ _ hpre hrootMass
  have hInv1 := (inverseAt_iff_power_mass bp dp t1 k1 c1 (by omega) hb14 hd1).mp hi1
  have hmassStep1 : 2*k1+c1+2*t1+2=bp+dp := by omega
  have hafter1Mass : (2*k1-4)+(c1+4)+2*(mp+t1+1)+2*n+13=14*2^n := by
    omega
  have hmidMass := two_chain_mass n u _ _ _ _ _ _ hmid hafter1Mass
  have hmidModel := two_chain_model n u _ _ _ _ _ _ hmid hafter1Mass
  have hInv2 := (inverseAt_iff_power_mass B D t2 k2 c2 (by omega) hb24 hd2).mp hi2
  have hmassStep2 : 2*k2+c2+2*t2+2=B+D := by omega
  have hafter2Mass : (2*k2-4)+(c2+4)+2*(M+t2+1)+2*n+13=14*2^n := by
    omega
  have hsufModel := two_chain_model n r _ _ _ _ _ _ hsuf hafter2Mass
  obtain ⟨alpha,C1,L1,O1,hAlpha1,hAlpha1max,hC1,hL1,hL1max,hO1,halpha1,hprofile1,hSh1⟩ :=
    source_shallow_profile n bp dp mp t1 k1 c1 hpreMass
      hb1 hb14 hd1 hi1 hk1 hc1 ht1
  obtain ⟨beta,C2,L2,O2,hBeta1,hBeta1max,hC2,hL2,hL2max,hO2,hbeta1,hprofile2,hSh2⟩ :=
    source_shallow_profile n B D M t2 k2 c2 hmidMass
      hb2 hb24 hd2 hi2 hk2 hc2 ht2
  let Wpre : Int := (bp:Int)+4*(mp:Int)+4*(n:Int)+20
  let Bpre : Int := (mp:Int)+(n:Int)+6
  let Wafter1 : Int := (↑(2*k1-4):Int)+4*(↑(mp+t1+1):Int)+4*(n:Int)+20
  let Wmid : Int := (B:Int)+4*(M:Int)+4*(n:Int)+20
  let Bmid : Int := (M:Int)+(n:Int)+6
  let Wafter2 : Int := (↑(2*k2-4):Int)+4*(↑(M+t2+1):Int)+4*(n:Int)+20
  let Wend : Int := (be:Int)+4*(me:Int)+4*(n:Int)+20
  let Bend : Int := (me:Int)+(n:Int)+6
  have hrootEq :
      ((↑(14*2^n-2*n-16):Int)+4*(0:Int)+4*(n:Int)+20) =
       14*(2:Int)^n+2*(n:Int)+4 := by
    have hnateq : (14*2^n-2*n-16)+4*n+20=14*2^n+2*n+4 := by omega
    exact_mod_cast hnateq
  have hpreModel' : TwoRun ((2:Int)^n)
      (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s Wpre Bpre := by
    rw [show (↑(0:Nat):Int)=0 by rfl] at hpreModel
    rw [hrootEq] at hpreModel
    simpa [Wpre,Bpre] using hpreModel
  have hBafter1 : ((↑(mp+t1+1):Int)+(n:Int)+6) = Bpre+(alpha:Int) := by
    dsimp [Bpre]
    omega
  have hmidModel' : TwoRun ((2:Int)^n)
      Wafter1 (Bpre+(alpha:Int)) u Wmid Bmid := by
    rw [hBafter1] at hmidModel
    simpa [Wafter1,Wmid,Bmid] using hmidModel
  have hBafter2 : ((↑(M+t2+1):Int)+(n:Int)+6) = Bmid+(beta:Int) := by
    dsimp [Bmid]
    omega
  have hsufModel' : TwoRun ((2:Int)^n)
      Wafter2 (Bmid+(beta:Int)) r Wend Bend := by
    rw [hBafter2] at hsufModel
    simpa [Wafter2,Wend,Bend] using hsufModel
  have hSh1' : ((2:Int)^alpha)*I ((2:Int)^n) Wafter1 (Bpre+(alpha:Int)) =
      I ((2:Int)^n) Wpre Bpre - (C1:Int)*(2:Int)^n +
        (L1:Int)*Bpre-(O1:Int) := by
    simpa [Wafter1,Wpre,Bpre] using hSh1
  have hSh2' : ((2:Int)^beta)*I ((2:Int)^n) Wafter2 (Bmid+(beta:Int)) =
      I ((2:Int)^n) Wmid Bmid - (C2:Int)*(2:Int)^n +
        (L2:Int)*Bmid-(O2:Int) := by
    simpa [Wafter2,Wmid,Bmid] using hSh2
  have hwallInt : Wend=12*(2:Int)^n := by
    dsimp [Wend]
    exact_mod_cast hwall
  exact no_two_shallow_model_from_source_coefficients n s u r alpha beta C1 C2 L1 L2 O1 O2 t1 t2
    hn ht1 ht2 hprofile1 hprofile2 hAlpha1 hAlpha1max hBeta1 hBeta1max hC1 hC2 hL1 hL1max hL2 hL2max hO1 hO2
    Wpre Bpre Wafter1 Wmid Bmid Wafter2 Wend Bend
    hpreModel' hSh1' hmidModel' hSh2' hsufModel' hwallInt

/-- Compatibility corollary retaining the original n >= 48 interface. -/
theorem source_no_two_shallow_word_wall_large
    (n s u r t1 t2 bp dp mp k1 c1 B D M k2 c2 be de me : Nat)
    (hn : 48≤n) (ht1 : t1≤1) (ht2 : t2≤1)
    (hpre : SourceTwoChain n s (14*2^n-2*n-16) 3 0 bp dp mp)
    (hb1 : 8≤bp) (hb14 : bp%4=0) (hd1 : dp%2=1)
    (hi1 : inverseAt bp dp t1=some (k1,c1))
    (hk1 : 2≤k1) (hc1 : c1%2=1)
    (hmid : SourceTwoChain n u (2*k1-4) (c1+4) (mp+t1+1) B D M)
    (hb2 : 8≤B) (hb24 : B%4=0) (hd2 : D%2=1)
    (hi2 : inverseAt B D t2=some (k2,c2))
    (hk2 : 2≤k2) (hc2 : c2%2=1)
    (hsuf : SourceTwoChain n r (2*k2-4) (c2+4) (M+t2+1) be de me)
    (hwall : be+4*me+4*n+20=12*2^n) : False := by
  exact source_no_two_shallow_word_wall_all
    n s u r t1 t2 bp dp mp k1 c1 B D M k2 c2 be de me
    (by omega) ht1 ht2 hpre hb1 hb14 hd1 hi1 hk1 hc1
    hmid hb2 hb24 hd2 hi2 hk2 hc2 hsuf hwall

#print axioms BB6.Agent43SourceWord.source_no_two_shallow_word_wall_all
#print axioms BB6.Agent43SourceWord.source_no_two_shallow_word_wall_large
end BB6.Agent43SourceWord
namespace BB6.Agent43SourceWord
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent43TwoRun
open BB6.Agent43ThreeShallowSourceModel

/-- Three genuine shallow inverseAt transitions (depth zero or one), with
arbitrary genuine depth-two runs before, between, and after them, cannot
reach the P1 exact shifted wall from the critical source seed, for n >= 14. -/
theorem source_no_three_shallow_word_wall_all
    (n s u v r t1 t2 t3 bp dp mp k1 c1 B1 D1 M1 k2 c2 B2 D2 M2 k3 c3 be de me : Nat)
    (hn : 14≤n) (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1)
    (hpre : SourceTwoChain n s (14*2^n-2*n-16) 3 0 bp dp mp)
    (hb1 : 8≤bp) (hb14 : bp%4=0) (hd1 : dp%2=1)
    (hi1 : inverseAt bp dp t1=some (k1,c1))
    (hk1 : 2≤k1) (hc1 : c1%2=1)
    (hmid1 : SourceTwoChain n u (2*k1-4) (c1+4) (mp+t1+1) B1 D1 M1)
    (hb2 : 8≤B1) (hb24 : B1%4=0) (hd2 : D1%2=1)
    (hi2 : inverseAt B1 D1 t2=some (k2,c2))
    (hk2 : 2≤k2) (hc2 : c2%2=1)
    (hmid2 : SourceTwoChain n v (2*k2-4) (c2+4) (M1+t2+1) B2 D2 M2)
    (hb3 : 8≤B2) (hb34 : B2%4=0) (hd3 : D2%2=1)
    (hi3 : inverseAt B2 D2 t3=some (k3,c3))
    (hk3 : 2≤k3) (hc3 : c3%2=1)
    (hsuf : SourceTwoChain n r (2*k3-4) (c3+4) (M2+t3+1) be de me)
    (hwall : be+4*me+4*n+20=12*2^n) : False := by
  have hrootMass : (14*2^n-2*n-16)+3+2*0+2*n+13=14*2^n := by omega
  have hpreMass := two_chain_mass n s _ _ _ _ _ _ hpre hrootMass
  have hpreModel := two_chain_model n s _ _ _ _ _ _ hpre hrootMass
  have hInv1 := (inverseAt_iff_power_mass bp dp t1 k1 c1 (by omega) hb14 hd1).mp hi1
  have hmassStep1 : 2*k1+c1+2*t1+2=bp+dp := by omega
  have hafter1Mass : (2*k1-4)+(c1+4)+2*(mp+t1+1)+2*n+13=14*2^n := by omega
  have hmid1Mass := two_chain_mass n u _ _ _ _ _ _ hmid1 hafter1Mass
  have hmid1Model := two_chain_model n u _ _ _ _ _ _ hmid1 hafter1Mass
  have hInv2 := (inverseAt_iff_power_mass B1 D1 t2 k2 c2 (by omega) hb24 hd2).mp hi2
  have hmassStep2 : 2*k2+c2+2*t2+2=B1+D1 := by omega
  have hafter2Mass : (2*k2-4)+(c2+4)+2*(M1+t2+1)+2*n+13=14*2^n := by omega
  have hmid2Mass := two_chain_mass n v _ _ _ _ _ _ hmid2 hafter2Mass
  have hmid2Model := two_chain_model n v _ _ _ _ _ _ hmid2 hafter2Mass
  have hInv3 := (inverseAt_iff_power_mass B2 D2 t3 k3 c3 (by omega) hb34 hd3).mp hi3
  have hmassStep3 : 2*k3+c3+2*t3+2=B2+D2 := by omega
  have hafter3Mass : (2*k3-4)+(c3+4)+2*(M2+t3+1)+2*n+13=14*2^n := by omega
  have hsufModel := two_chain_model n r _ _ _ _ _ _ hsuf hafter3Mass
  obtain ⟨alpha,C1,L1,O1,hAlpha1,hAlpha1max,hC1,hL1,hL1max,hO1,halpha1,hprofile1,hSh1⟩ :=
    source_shallow_profile n bp dp mp t1 k1 c1 hpreMass hb1 hb14 hd1 hi1 hk1 hc1 ht1
  obtain ⟨beta,C2,L2,O2,hBeta1,hBeta1max,hC2,hL2,hL2max,hO2,hbeta1,hprofile2,hSh2⟩ :=
    source_shallow_profile n B1 D1 M1 t2 k2 c2 hmid1Mass hb2 hb24 hd2 hi2 hk2 hc2 ht2
  obtain ⟨gamma,C3,L3,O3,hGamma1,hGamma1max,hC3,hL3,hL3max,hO3,hgamma1,hprofile3,hSh3⟩ :=
    source_shallow_profile n B2 D2 M2 t3 k3 c3 hmid2Mass hb3 hb34 hd3 hi3 hk3 hc3 ht3
  let Wa : Int := (bp:Int)+4*(mp:Int)+4*(n:Int)+20
  let Ba : Int := (mp:Int)+(n:Int)+6
  let Wb : Int := (↑(2*k1-4):Int)+4*(↑(mp+t1+1):Int)+4*(n:Int)+20
  let Wc : Int := (B1:Int)+4*(M1:Int)+4*(n:Int)+20
  let Bc : Int := (M1:Int)+(n:Int)+6
  let Wd : Int := (↑(2*k2-4):Int)+4*(↑(M1+t2+1):Int)+4*(n:Int)+20
  let We : Int := (B2:Int)+4*(M2:Int)+4*(n:Int)+20
  let Be : Int := (M2:Int)+(n:Int)+6
  let Wf : Int := (↑(2*k3-4):Int)+4*(↑(M2+t3+1):Int)+4*(n:Int)+20
  let Wg : Int := (be:Int)+4*(me:Int)+4*(n:Int)+20
  let Bg : Int := (me:Int)+(n:Int)+6
  have hrootEq : ((↑(14*2^n-2*n-16):Int)+4*(0:Int)+4*(n:Int)+20) =
      14*(2:Int)^n+2*(n:Int)+4 := by
    have hnat : (14*2^n-2*n-16)+4*n+20 = 14*2^n+2*n+4 := by omega
    exact_mod_cast hnat
  have hpreModel' : TwoRun ((2:Int)^n)
      (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s Wa Ba := by
    rw [show (↑(0:Nat):Int)=0 by rfl] at hpreModel
    rw [hrootEq] at hpreModel
    simpa [Wa,Ba] using hpreModel
  have hBafter1 : ((↑(mp+t1+1):Int)+(n:Int)+6)=Ba+(alpha:Int) := by
    dsimp [Ba]
    omega
  have hmid1Model' : TwoRun ((2:Int)^n) Wb (Ba+(alpha:Int)) u Wc Bc := by
    rw [hBafter1] at hmid1Model
    simpa [Wb,Wc,Bc] using hmid1Model
  have hBafter2 : ((↑(M1+t2+1):Int)+(n:Int)+6)=Bc+(beta:Int) := by
    dsimp [Bc]
    omega
  have hmid2Model' : TwoRun ((2:Int)^n) Wd (Bc+(beta:Int)) v We Be := by
    rw [hBafter2] at hmid2Model
    simpa [Wd,We,Be] using hmid2Model
  have hBafter3 : ((↑(M2+t3+1):Int)+(n:Int)+6)=Be+(gamma:Int) := by
    dsimp [Be]
    omega
  have hsufModel' : TwoRun ((2:Int)^n) Wf (Be+(gamma:Int)) r Wg Bg := by
    rw [hBafter3] at hsufModel
    simpa [Wf,Wg,Bg] using hsufModel
  have hSh1' : ((2:Int)^alpha)*I ((2:Int)^n) Wb (Ba+(alpha:Int)) =
      I ((2:Int)^n) Wa Ba-(C1:Int)*(2:Int)^n+(L1:Int)*Ba-(O1:Int) := by
    simpa [Wa,Wb,Ba] using hSh1
  have hSh2' : ((2:Int)^beta)*I ((2:Int)^n) Wd (Bc+(beta:Int)) =
      I ((2:Int)^n) Wc Bc-(C2:Int)*(2:Int)^n+(L2:Int)*Bc-(O2:Int) := by
    simpa [Wc,Wd,Bc] using hSh2
  have hSh3' : ((2:Int)^gamma)*I ((2:Int)^n) Wf (Be+(gamma:Int)) =
      I ((2:Int)^n) We Be-(C3:Int)*(2:Int)^n+(L3:Int)*Be-(O3:Int) := by
    simpa [We,Wf,Be] using hSh3
  have hwallInt : Wg=12*(2:Int)^n := by
    dsimp [Wg]
    exact_mod_cast hwall
  exact no_three_shallow_model_from_source_coefficients
    n s u v r t1 t2 t3 alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3
    hn ht1 ht2 ht3 hprofile1 hprofile2 hprofile3
    hC1 hL1 hO1 hC2 hL2 hO2 hC3 hL3 hO3
    Wa Ba Wb Wc Bc Wd We Be Wf Wg Bg
    hpreModel' hSh1' hmid1Model' hSh2' hmid2Model' hSh3' hsufModel' hwallInt

#print axioms source_no_three_shallow_word_wall_all
end BB6.Agent43SourceWord
