import HighTower3A
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3

/-- Abstract affine inverse right-counter tower, independent of halting m. -/
def affineRightSeed (seed : Nat) : Nat → Nat
  | 0 => seed
  | n+1 => 2*affineRightSeed seed n+2

theorem affineRightSeed_even (seed d : Nat) (hs : seed%4=0) :
    affineRightSeed seed d%2=0 := by
  cases d with
  | zero => change seed%2=0; omega
  | succ d => change (2*affineRightSeed seed d+2)%2=0; omega

theorem affineRightSeed_lower (seed d : Nat) (hs : 32≤seed) :
    32≤affineRightSeed seed d := by
  induction d with
  | zero => change 32≤seed; exact hs
  | succ d ih => change 32≤2*affineRightSeed seed d+2; omega

/-- For every seed divisible by 4 and at least 32, the exact affine inverse
    depth is the number of right-tower levels, with no bounded trace. -/
theorem affineRightSeed_oddDepth (seed d : Nat)
    (hmod : seed%4=0) (hl : 32≤seed) :
    BB6.Agent15.oddDepth (affineRightSeed seed d)=d := by
  induction d with
  | zero =>
      have hn : ¬(4≤seed ∧ seed%4=2) := by omega
      change BB6.Agent15.oddDepth seed=0
      rw [BB6.Agent15.oddDepth,dif_neg hn]
  | succ d ih =>
      have he := affineRightSeed_even seed d hmod
      have hge := affineRightSeed_lower seed d hl
      have hg : 4≤affineRightSeed seed (d+1) ∧
          affineRightSeed seed (d+1)%4=2 := by
        simp only [affineRightSeed]; omega
      have hr : (affineRightSeed seed (d+1)-2)/2=affineRightSeed seed d := by
        simp only [affineRightSeed]; omega
      rw [BB6.Agent15.oddDepth,dif_pos hg,hr,ih]
      omega

/-- Uniform exact normalizer right seed for arbitrary depth. -/
theorem affineRightSeed_terminal (seed d a : Nat)
    (hmod : seed%4=0) (hl : 32≤seed) (ha : a%4=3) :
    (BB6.Agent15.affineNormalize a (affineRightSeed seed d)).2=seed := by
  induction d generalizing a with
  | zero =>
      have hn : ¬(4≤seed ∧ seed%2=0 ∧ (a+seed)%4=1) := by omega
      change (BB6.Agent15.affineNormalize a seed).2=seed
      rw [BB6.Agent15.affineNormalize,dif_neg hn]
  | succ d ih =>
      have he := affineRightSeed_even seed d hmod
      have hge := affineRightSeed_lower seed d hl
      have hg : 4≤affineRightSeed seed (d+1) ∧
          affineRightSeed seed (d+1)%2=0 ∧
          (a+affineRightSeed seed (d+1))%4=1 := by
        simp only [affineRightSeed]; omega
      have ha' : (a+affineRightSeed seed (d+1)-2)%4=3 := by
        simp only [affineRightSeed]; omega
      have hr : (affineRightSeed seed (d+1)-2)/2=affineRightSeed seed d := by
        simp only [affineRightSeed]; omega
      rw [BB6.Agent15.affineNormalize,dif_pos hg,hr]
      exact ih (a+affineRightSeed seed (d+1)-2) ha'

#print axioms affineRightSeed_oddDepth
#print axioms affineRightSeed_terminal
end BB6.Agent3
