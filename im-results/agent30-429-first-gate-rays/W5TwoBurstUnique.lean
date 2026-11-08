import W5TwoBurst
import BB429Burst
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

namespace BB429TwoBurstUnique
open BB429TwoBurst BB429FirstGateRays

/-- Exponential width inequality forces the second burst to be
    exactly two first-branch steps shorter than the first burst. -/
theorem exp_gap (n p : Nat) (hn : n%4=3) (hp : p%4=1)
    (hlo : 12*2^n+27+3*p ≤ 56*2^p)
    (hhi : 56*2^p < 24*2^n+21+3*p) : n=p+2 := by
  by_cases hne : n = p+2
  · exact hne
  exfalso
  by_cases hsmall : n ≤ p+1
  · have hpow := Nat.pow_le_pow_right (by decide : 0<2) hsmall
    have he : 2^(p+1) = 2*2^p := by
      rw [Nat.pow_succ]
      omega
    rw [he] at hpow
    have hp5 : 5 ≤ p := by omega
    have hlinear := two_pow_ge p
    omega
  · have hbig : p+3 ≤ n := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0<2) hbig
    have he : 2^(p+3) = 8*2^p := by
      rw [Nat.pow_add]
      simp only [show (2:Nat)^3=8 by decide]
      omega
    rw [he] at hpow
    have hpos : 0<2^p := Nat.pow_pos (by decide)
    omega

/-- An exact low-even branch of the original twelve-branch #429 accelerator. -/
theorem low_even_source (a b : Nat)
    (heven : b%2=0) (hbelow : b<2*a)
    (hd : (a-b/2)%2=0) :
    BB429.next (a,b) = some (11,2*a+b-2) := by
  have hguard : ¬ (2*a+3 ≤ b) := by omega
  have h2 : b ≠ 2*a+2 := by omega
  have h1 : b ≠ 2*a+1 := by omega
  have h0 : b ≠ 2*a := by omega
  have hdne : a-b/2 ≠ 1 := by omega
  simp [BB429.next,hguard,h2,h1,h0,heven,hdne,hd]

/-- Every admissible first-burst / low-even / second-burst fatal path from
    the right-five J(3,4k+17) boundary belongs to the explicit K_two family. -/
theorem unique_two_burst (k n p a b c x y : Nat)
    (hf : BB429Burst.firstRun n (3,4*k+17)=some (a,b))
    (heven : b%2=0) (hbelow : b<2*a)
    (hd : (a-b/2)%2=0) (hc : c=2*a+b-2)
    (hs : BB429Burst.firstRun p (11,c)=some (x,y))
    (hgate : y+1=2*x) :
    ∃ t, k=kTwo t ∧ n=4*t+7 ∧ p=4*t+5 := by
  obtain ⟨ha,hmass⟩ := BB429Burst.prefix_formula 3 (4*k+17) n a b hf
  obtain ⟨hx,hfinal⟩ := BB429Burst.prefix_formula 11 c p x y hs
  have heq : 2*a+b+33+3*p = 56*2^p := by omega
  have habodd : a%2=1 := by omega
  have hbmod : b%4=2 := by omega
  have hnmod : n%4=3 := by omega
  have hpmod : p%4=1 := by omega
  have hlo : 12*2^n+27+3*p ≤ 56*2^p := by omega
  have hhi : 56*2^p < 24*2^n+21+3*p := by omega
  have hn : n=p+2 := exp_gap n p hnmod hpmod hlo hhi
  have hp5 : 5≤p := by
    have he : 2^(p+2)=4*2^p := by
      rw [Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega
    rw [hn,he] at hlo
    have hpow : 2^1=2 := by decide
    by_cases h1 : p=1
    · rw [h1,hpow] at hlo
      omega
    · omega
  let t : Nat := p/4-1
  have hpform : p=4*t+5 := by dsimp [t]; omega
  have hnform : n=4*t+7 := by omega
  have hqform : qTwo t=2^p := by rw [hpform]; rfl
  have hkform : k=kTwo t := by
    have hmass' := hmass
    rw [hnform] at hmass'
    have heq' := heq
    rw [hpform] at heq'
    have hk := kTwo_formula t
    rw [hqform] at hk
    omega
  exact ⟨t,hkform,hnform,hpform⟩

/-- Unique two-burst low-even fatal accelerator pattern, using the original
    twelve-branch next function for the exceptional middle instruction. -/
theorem unique_two_burst_source (k n p a b c x y : Nat)
    (hf : BB429Burst.firstRun n (3,4*k+17)=some (a,b))
    (heven : b%2=0) (hbelow : b<2*a)
    (hd : (a-b/2)%2=0)
    (hmid : BB429.next (a,b) = some (11,c))
    (hs : BB429Burst.firstRun p (11,c)=some (x,y))
    (hgate : y+1=2*x) :
    ∃ t, k=kTwo t ∧ n=4*t+7 ∧ p=4*t+5 := by
  have heq : c=2*a+b-2 := by
    have hr := low_even_source a b heven hbelow hd
    have h : some (11,c) = some (11,2*a+b-2) := hmid.symm.trans hr
    exact (Prod.mk.inj ((Option.some.inj h))).2
  exact unique_two_burst k n p a b c x y hf heven hbelow hd heq hs hgate

/-- Strictly increasing seeds certify infinitely many distinct two-burst inputs. -/
theorem kTwo_strict_succ (t : Nat) : kTwo t < kTwo (t+1) := by
  have hpow : 2^(4*(t+1)+5) = 16*2^(4*t+5) := by
    have he : 4*(t+1)+5 = (4*t+5)+4 := by omega
    rw [he, Nat.pow_add]
    simp only [show (2:Nat)^4=16 by decide]
    omega
  have hq := q_bound t
  dsimp [qTwo] at hq
  dsimp [kTwo]
  rw [hpow]
  omega

#print axioms kTwo_strict_succ
#print axioms low_even_source
#print axioms unique_two_burst_source
#print axioms unique_two_burst
#print axioms exp_gap
end BB429TwoBurstUnique
