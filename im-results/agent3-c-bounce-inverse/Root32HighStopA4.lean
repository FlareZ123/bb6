import Root32HighStopP7
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace BB6.Agent3Root32HighStopA4

open BB6.Agent46
open BB6.Agent3Root32HighStopIntegrated
open BB6.Agent3Root32HighStopS1

/-- The corrected P7E1E residual's left coordinate. -/
def a4X (t : Nat) : Nat := 2814461475*t + 754739388

/-- The corrected P7E1E residual's right coordinate. -/
def a4Y (t : Nat) : Nat := (4231969245*t + 1134865019)/2

/-- On t = 31 (mod 32), A4 lies in the exact odd/odd valuation-three
    layer. These are the hypotheses for the source-certified low-value
    odd/odd inverse. -/
theorem a4_t31_facts (t : Nat) (ht : t%32=31) :
    5 < a4X t ∧
    5 ≤ a4Y t ∧
    a4X t%2=1 ∧
    a4Y t%2=1 ∧
    (a4X t+a4Y t)%4=0 ∧
    (a4X t+a4Y t)%16=8 ∧
    24 ≤ a4X t+a4Y t := by
  have htmin : 31≤t := by omega
  have ht4 : t%4=3 := by omega
  have hy2 : 2*a4Y t = 4231969245*t+1134865019 := by
    dsimp [a4Y]
    omega
  have hsum2 : 2*(a4X t+a4Y t) =
      9860892195*t+2644343795 := by
    dsimp [a4X,a4Y]
    omega
  have hN : (9860892195*t+2644343795)%32=16 := by omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [a4X]
    omega
  · dsimp [a4Y]
    omega
  · dsimp [a4X]
    omega
  · omega
  · omega
  · omega
  · dsimp [a4X]
    omega

/-- The A4 target is genuinely blank-unreachable throughout
    t = 31 (mod 32). Its unique low-valuation odd/odd source parent has
    odd right coordinate and sum 1 (mod 4), contradicting the global
    blank odd-image theorem. -/
theorem a4_unreachable_of_t_mod32_31 (t : Nat) (ht : t%32=31) :
    ¬ RunReach (a4X t) (a4Y t) := by
  intro hreach
  rcases a4_t31_facts t ht with
    ⟨hx,hy,hxodd,hyodd,hsum4,hsum16,hsize⟩
  let p := (a4X t+a4Y t-4)/2
  let q := (a4X t+3*a4Y t-10)/4
  have hparent : RunReach p q := by
    simpa [RunReach,p,q] using
      (BB6.Agent3.oddodd_lowval_blank_reach_iff
        (a4X t) (a4Y t) hxodd hyodd hy hsum4 (by omega) hsize).mp hreach
  have htmin : 31≤t := by omega
  have hP8 : 8*(p+q)=38046615075*t+10202761387 := by
    dsimp [p,q,a4X,a4Y]
    omega
  have hQ8 : 8*q=18324830685*t+4914073813 := by
    dsimp [q,a4X,a4Y]
    omega
  have hPmod : (38046615075*t+10202761387)%32=8 := by omega
  have hQmod : (18324830685*t+4914073813)%16=8 := by omega
  have hpX : 5<p := by
    dsimp [p,a4X,a4Y]
    omega
  have hpY : 5≤q := by
    dsimp [q,a4X,a4Y]
    omega
  have hpOdd : q%2=1 := by omega
  have hpSum : (p+q)%4=1 := by omega
  exact (run_no_odd_sum_one p q hpX hpY hpOdd hpSum) hparent

#print axioms a4_t31_facts
#print axioms a4_unreachable_of_t_mod32_31

end BB6.Agent3Root32HighStopA4
