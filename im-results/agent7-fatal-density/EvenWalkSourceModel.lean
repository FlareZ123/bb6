import EvenWalkGapBridge
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace GapNumber

private theorem pow16 (n:Nat) (hn:4≤n): 2^n=16*2^(n-4):=by
  have he:n=(n-4)+4:=by omega
  rw[he,Nat.pow_add]
  simp [Nat.mul_comm]

private theorem pow_mod3 (j:Nat):
  2^j%3=(if j%2=0 then 1 else 2):=by
  induction j with
  | zero=>decide
  | succ j ih=>
      rw [Nat.pow_succ,Nat.mul_mod,ih]
      by_cases h:j%2=0
      · simp[h];omega
      · have hj:j%2=1:=by omega
        simp[hj];omega

private theorem safe_near (n q d:Nat) (hn:25≤n)
 (hsector:n%6=4 ∨ n%6=5)
 (hdiv:(9*d)%27≠0)
 (hq:4*d=8*2^(n-4)+q+(n-4)+5):
 CascadeEvenChainGap.SafeResidue (n-4) q:=by
  let k:=n-4
  have hkmod:k%6=0 ∨ k%6=1:=by
    dsimp[k]
    rcases hsector with h|h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hpmod:2^k%3=if k%2=0 then 1 else 2:=pow_mod3 k
  have hE:(8*2^k+k)%3=2:=by
    rcases hkmod with h|h
    · have he:k%2=0:=by omega
      have ht:k%3=0:=by omega
      rw [if_pos he] at hpmod
      omega
    · have he:k%2=1:=by omega
      have ht:k%3=1:=by omega
      have hn: k%2≠0:=by omega
      rw [if_neg hn] at hpmod
      omega
  have hd:d%3≠0:=by
    intro hz
    have hh:(9*d)%27=0:=by omega
    exact hdiv hh
  have hqmod:q%3≠2:=by
    have heq :4*d=8*2^k+q+k+5:=hq
    omega
  exact ⟨hqmod,Or.inl hE⟩

/-- Genuine original blank-reset root exclusion for every second-tier
    low-valuation source arm satisfying the literal inverse arithmetic,
    every qualifying n>=25, and every symbolic canonical ray depth j. -/
theorem second_tier_root_dead (n j D h w q d:Nat)
 (hn:25≤n)
 (hsector:n%6=4∨n%6=5)
 (hD:D+(n-1)=2^j*(2*n+3))
 (hm:32*D+64*n+128≤2^n)
 (hl:9*h+8*D+9*n+7=14*2^n)
 (he:2*h=2*2^n+w+(n-2))
 (hw:2*w+5=9*d)
 (hdiv:(2*w+5)%27≠0)
 (hband:6*2^(n-4)+1≤2*d ∧ 2*d≤8*2^(n-4)-1)
 (hq:4*d=8*2^(n-4)+q+(n-4)+5):
 ¬CascadeSweep.ReachC (2,0) (q,0):=by
 let p:=2^(n-4)
 have hpow:2^n=16*p:=pow16 n (by omega)
 have hqp:q≤8*p:=by
   have hu:=hband.2
   dsimp[p] at *
   omega
 let B:=8*p-q
 have hQB:B+q=8*p:=by dsimp[B];omega
 have hweak:2*(2^j*(2*n+3))+2*n+10≤p:=by
   rw[hpow] at hm
   omega
 have hmodel:81*B+3=16*p+128*(2^j*(2*n+3))+169*n:=by
   rw[hpow] at hl he
   dsimp[B]
   omega
 have hs:CascadeEvenChainGap.SafeResidue (n-4) q:=by
   apply safe_near n q d hn hsector
   · rw [←hw];exact hdiv
   · exact hq
 exact uniform_two_four_root_exclusion n j B q hn hmodel hweak hQB hs

#print axioms second_tier_root_dead
end GapNumber
