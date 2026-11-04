import OddWordSourceBridge
import OneResetSourceBudget
import UpperTail

namespace BB6.Agent28
open BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1

private theorem prefix_upper_is_oddcone (b0 d0 b d m r:Nat)
    (h:UpperTail b0 d0 0 b d m r) : OddCone b0 d0 b d m := by
  induction h with
  | root => exact OddCone.root
  | step b d m r k c hprev hb hb4 hd hi hk hc ih =>
      exact OddCone.parent b d m 0 k c ih hb hb4 hd hi hk hc

private theorem source_bridge_pow (n : Nat) (hn : 4 ≤ n) : n+4 ≤ 2^n := by
  have hb : ∀ t:Nat, (t+4)+4 ≤ 2^(t+4) := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
        have hidx : (t+1)+4 = (t+4)+1 := by omega
        rw [hidx, Nat.pow_succ]
        omega
  have heq : (n-4)+4 = n := by omega
  simpa only [heq] using hb (n-4)

/-- Original-source one-positive-reset wall exclusion: any upper prefix,
    one genuine inverseAt with t≥1, and any upper suffix. -/
theorem source_critical_one_reset_no_wall
    (n bp dp mp r t k c b d m s : Nat)
    (hn : 30≤n) (ht : 1≤t)
    (hpre : UpperTail (14*2^n-2*n-16) 3 0 bp dp mp r)
    (hbp : 8≤bp) (hbp4 : bp%4=0) (hdp : dp%2=1)
    (hi : inverseAt bp dp t=some (k,c))
    (hk : 2≤k) (hc : c%2=1)
    (hpost : UpperTail (2*k-4) (c+4) (mp+t+1) b d m s)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hwall : b=4*(m+n)) : False := by
  let P : Nat := 2^n
  let K : Nat := 7*P-n-3
  let b0 : Nat := 14*P-2*n-16
  have hdom : n+4 ≤ P := source_bridge_pow n (by omega)
  have hK : K+n+3=7*P := by dsimp [K]; omega
  have hroot : b0+10=2*K := by dsimp [b0,K]; omega
  have hpreDy := upper_tail_dyadic b0 3 0 bp dp mp r
    (by simpa only [b0,P] using hpre)
  have hprepow : 2^r*(bp+12)=b0+12 := hpreDy.1
  have hmr : mp=r := by omega
  let Fr : Nat := (bp+12)/2
  let Dr : Nat := dp/2
  let Dp : Nat := (c+3)/2
  let Ff : Nat := (b+12)/2
  have hFr : 2*Fr=bp+12 := by dsimp [Fr]; omega
  have hDr : dp=2*Dr+1 := by dsimp [Dr]; omega
  have hDp : c+3=2*Dp := by dsimp [Dp]; omega
  have hFf : 2*Ff=b+12 := by dsimp [Ff]; omega
  have hR : 2^r*Fr+(n+2)=7*P := by
    have hh : 2*(2^r*Fr)=2*(K+1) := by
      calc
        _ = 2^r*(bp+12) := by rw [←hFr]; ac_rfl
        _ = b0+12 := hprepow
        _ = 2*(K+1) := by omega
    omega
  have hprecone : OddCone b0 3 bp dp mp :=
    prefix_upper_is_oddcone b0 3 bp dp mp r
      (by simpa only [b0,P] using hpre)
  have hpmass := odd_cone_mass b0 3 bp dp mp hprecone
  have hprenorm : Fr+Dr+r=K+2 := by omega
  have hb2 : bp=2*(bp/2) := by omega
  have hp := (inverseAt_iff_power_mass bp dp t k c (by omega) hbp4 hdp).mp hi
  have hpower : dp+bp/2+3=2^t*(c+3) := hp.1
  have hpval : 2^(t+1)*Dp=2^t*(c+3) := by
    rw [Nat.pow_succ, hDp]
    ac_rfl
  have hstep : 2^(t+1)*Dp+r=K+Dr := by omega
  have hpostdy := upper_tail_dyadic (2*k-4) (c+4) (mp+t+1) b d m s hpost
  have hpostpow : 2^s*(b+12)=2*k+8 := by omega
  have hSf : 2^s*Ff=k+4 := by
    have heq : 2*(2^s*Ff)=2*(k+4) := by
      calc
        _ = 2^s*(b+12) := by rw [←hFf]; ac_rfl
        _ = 2*k+8 := hpostpow
        _ = 2*(k+4) := by omega
    omega
  have hresetcone : OddCone b0 3 (2*k-4) (c+4) (mp+t+1) :=
    OddCone.parent bp dp mp t k c hprecone hbp hbp4 hdp hi hk hc
  have hrmass := odd_cone_mass b0 3 (2*k-4) (c+4) (mp+t+1) hresetcone
  have hpostnorm : 2^s*Ff+Dp+r+(t+1)=K+2 := by omega
  have hm : m=r+(t+1)+s := by omega
  obtain ⟨Df,A,T,hdF,hbalance,hword⟩ :=
    source_oddcone_has_word b0 K b d m hroot
      (by simpa only [b0,P] using hcone)
  have hwallDf : Df+3*(r+(t+1)+s)+2*n+4=K := by omega
  have hword' : OddWord K Df (r+(t+1)+s) A T := by
    simpa only [←hm] using hword
  exact exact_one_reset_wall_impossible n r (t+1) s K Fr Dr Dp Ff Df A T hn
    (by omega) (by simpa only [P] using hK)
    (by simpa only [P] using hR)
    hprenorm hstep hpostnorm hword' hwallDf

#print axioms BB6.Agent28.source_critical_one_reset_no_wall
end BB6.Agent28
