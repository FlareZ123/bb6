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
