import CFull32
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CCert

/-- Twenty-four finite-quotient-absent high stopping-parameter pairs, at modulus 32. -/
def highPairGood (jr mr : Nat) : Prop :=
  seen (q (2*(jr+32)+3)) (q (160-(jr+3*mr+5))) (q 0) = false

instance highPairGood_decidable (jr mr : Nat) : Decidable (highPairGood jr mr) := by
  unfold highPairGood
  infer_instance

def newHighPairs : List (Nat×Nat) :=
  [(0,13),(0,25),(1,28),(4,25),(4,29),(5,16),
   (8,1),(8,5),(9,4),(12,5),(12,17),(13,24),
   (16,9),(16,29),(17,12),(20,9),(20,13),(21,0),
   (24,17),(24,21),(25,20),(28,1),(28,21),(29,8)]

theorem newHighPairs_excluded :
    newHighPairs.all (fun p => decide (highPairGood p.1 p.2)) = true := by
  decide +kernel

theorem high_pair_absent_sound (j m k : Nat)
    (hj : 3 ≤ j) (hk : 8 ≤ k) (hm : 2 ≤ m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hb : highPairGood (j%32) (m%32)) :
    seen (q (2*j+3)) (q k) (q 0) = false := by
  have hmod0 : (k+j+3*m+5)%32 = 0 := by
    have hp : 32 ∣ 2^(2*m+2) := by
      simpa using Nat.pow_dvd_pow 2 (show 5 ≤ 2*m+2 by omega)
    obtain ⟨d, hd⟩ := hp
    have hdiv : 32 ∣ 2^(2*m+2)*(j+3) := by
      refine ⟨d*(j+3), ?_⟩
      rw [hd]
      simp only [Nat.mul_assoc]
    rw [heq]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hK : 8 ≤ 160-(j%32+3*(m%32)+5) := by omega
  have hKmod : k%32 = (160-(j%32+3*(m%32)+5))%32 := by omega
  have ha : q (2*j+3)=q (2*(j%32+32)+3) :=
    q_congr_big _ _ (by omega) (by omega) (by omega)
  have hkq : q k = q (160-(j%32+3*(m%32)+5)) :=
    q_congr_big _ _ hk hK hKmod
  have hs := hb
  rw [ha,hkq]
  exact hs

theorem high_24_pairs_absent (j m k:Nat)
    (hj:3≤j)(hk:8≤k)(hm:2≤m)
    (heq:k+j+3*m+5=2^(2*m+2)*(j+3))
    (hp:(j%32,m%32) ∈ newHighPairs) :
    seen (q (2*j+3)) (q k) (q 0) = false := by
  have hb : highPairGood (j%32) (m%32) :=
    of_decide_eq_true ((List.all_eq_true.mp newHighPairs_excluded) (j%32,m%32) hp)
  exact high_pair_absent_sound j m k hj hk hm heq hb

theorem high_24_pairs_unreachable (j m k:Nat)
    (hj:3≤j)(hk:8≤k)(hm:2≤m)
    (heq:k+j+3*m+5=2^(2*m+2)*(j+3))
    (hp:(j%32,m%32) ∈ newHighPairs) :
    ¬ Reach (2*j+3,k,0) := by
  intro h
  have hs := reachable_seen h
  rw [high_24_pairs_absent j m k hj hk hm heq hp] at hs
  cases hs

#print axioms high_24_pairs_unreachable
end CCert
