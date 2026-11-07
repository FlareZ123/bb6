import FullBoolean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent27Norm

/-- One branch of the authentic source normalizer. -/
private theorem norm_step (a k : Nat)
    (h:4≤k ∧ k%2=0 ∧ (a+k)%4=1) :
  BB6.Agent15.affineNormalize a k =
    BB6.Agent15.affineNormalize (a+k-2) ((k-2)/2) := by
  rw [BB6.Agent15.affineNormalize.eq_1]
  simp only [dif_pos h]

private theorem norm_stop (a k : Nat)
    (h:¬(4≤k ∧ k%2=0 ∧ (a+k)%4=1)) :
  BB6.Agent15.affineNormalize a k = (a,k) := by
  rw [BB6.Agent15.affineNormalize.eq_1]
  simp only [dif_neg h]

/-- Affine states after each of the seven forced inverse normalizer steps. -/
def a0 (t : Nat) : Nat := 8192*t+4515
def k0 (t : Nat) : Nat := 17592186040320*t+9702331119358
def a1 (t : Nat) : Nat := 17592186048512*t+9702331123871
def k1 (t : Nat) : Nat := 8796093020160*t+4851165559678
def a2 (t : Nat) : Nat := 26388279068672*t+14553496683547
def k2 (t : Nat) : Nat := 4398046510080*t+2425582779838
def a3 (t : Nat) : Nat := 30786325578752*t+16979079463383
def k3 (t : Nat) : Nat := 2199023255040*t+1212791389918
def a4 (t : Nat) : Nat := 32985348833792*t+18191870853299
def k4 (t : Nat) : Nat := 1099511627520*t+606395694958
def a5 (t : Nat) : Nat := 34084860461312*t+18798266548255
def k5 (t : Nat) : Nat := 549755813760*t+303197847478
def a6 (t : Nat) : Nat := 34634616275072*t+19101464395731
def k6 (t : Nat) : Nat := 274877906880*t+151598923738
def a7 (t : Nat) : Nat := 34909494181952*t+19253063319467
def k7 (t : Nat) : Nat := 137438953440*t+75799461868

theorem step0 (t:Nat) :
    BB6.Agent15.affineNormalize (a0 t) (k0 t) =
    BB6.Agent15.affineNormalize (a1 t) (k1 t) := by
  have hg : 4≤k0 t ∧ k0 t % 2=0 ∧ (a0 t+k0 t)%4=1 := by
    dsimp [a0,k0]
    omega
  calc
    _ = BB6.Agent15.affineNormalize (a0 t+k0 t-2) ((k0 t-2)/2) := norm_step _ _ hg
    _ = BB6.Agent15.affineNormalize (a1 t) (k1 t) := by
      have ha : a0 t+k0 t-2=a1 t := by dsimp [a0,k0,a1]; omega
      have hk : (k0 t-2)/2=k1 t := by dsimp [k0,k1]; omega
      rw [ha,hk]

theorem step1 (t:Nat) :
    BB6.Agent15.affineNormalize (a1 t) (k1 t) =
    BB6.Agent15.affineNormalize (a2 t) (k2 t) := by
  have hg : 4≤k1 t ∧ k1 t % 2=0 ∧ (a1 t+k1 t)%4=1 := by
    dsimp [a1,k1]
    omega
  calc
    _ = BB6.Agent15.affineNormalize (a1 t+k1 t-2) ((k1 t-2)/2) := norm_step _ _ hg
    _ = BB6.Agent15.affineNormalize (a2 t) (k2 t) := by
      have ha : a1 t+k1 t-2=a2 t := by dsimp [a1,k1,a2]; omega
      have hk : (k1 t-2)/2=k2 t := by dsimp [k1,k2]; omega
      rw [ha,hk]

theorem step2 (t:Nat) :
    BB6.Agent15.affineNormalize (a2 t) (k2 t) =
    BB6.Agent15.affineNormalize (a3 t) (k3 t) := by
  have hg : 4≤k2 t ∧ k2 t % 2=0 ∧ (a2 t+k2 t)%4=1 := by
    dsimp [a2,k2]
    omega
  calc
    _ = BB6.Agent15.affineNormalize (a2 t+k2 t-2) ((k2 t-2)/2) := norm_step _ _ hg
    _ = BB6.Agent15.affineNormalize (a3 t) (k3 t) := by
      have ha : a2 t+k2 t-2=a3 t := by dsimp [a2,k2,a3]; omega
      have hk : (k2 t-2)/2=k3 t := by dsimp [k2,k3]; omega
      rw [ha,hk]

theorem step3 (t:Nat) :
    BB6.Agent15.affineNormalize (a3 t) (k3 t) =
    BB6.Agent15.affineNormalize (a4 t) (k4 t) := by
  have hg : 4≤k3 t ∧ k3 t % 2=0 ∧ (a3 t+k3 t)%4=1 := by
    dsimp [a3,k3]
    omega
  calc
    _ = BB6.Agent15.affineNormalize (a3 t+k3 t-2) ((k3 t-2)/2) := norm_step _ _ hg
    _ = BB6.Agent15.affineNormalize (a4 t) (k4 t) := by
      have ha : a3 t+k3 t-2=a4 t := by dsimp [a3,k3,a4]; omega
      have hk : (k3 t-2)/2=k4 t := by dsimp [k3,k4]; omega
      rw [ha,hk]

theorem step4 (t:Nat) :
    BB6.Agent15.affineNormalize (a4 t) (k4 t) =
    BB6.Agent15.affineNormalize (a5 t) (k5 t) := by
  have hg : 4≤k4 t ∧ k4 t % 2=0 ∧ (a4 t+k4 t)%4=1 := by
    dsimp [a4,k4]
    omega
  calc
    _ = BB6.Agent15.affineNormalize (a4 t+k4 t-2) ((k4 t-2)/2) := norm_step _ _ hg
    _ = BB6.Agent15.affineNormalize (a5 t) (k5 t) := by
      have ha : a4 t+k4 t-2=a5 t := by dsimp [a4,k4,a5]; omega
      have hk : (k4 t-2)/2=k5 t := by dsimp [k4,k5]; omega
      rw [ha,hk]

theorem step5 (t:Nat) :
    BB6.Agent15.affineNormalize (a5 t) (k5 t) =
    BB6.Agent15.affineNormalize (a6 t) (k6 t) := by
  have hg : 4≤k5 t ∧ k5 t % 2=0 ∧ (a5 t+k5 t)%4=1 := by
    dsimp [a5,k5]
    omega
  calc
    _ = BB6.Agent15.affineNormalize (a5 t+k5 t-2) ((k5 t-2)/2) := norm_step _ _ hg
    _ = BB6.Agent15.affineNormalize (a6 t) (k6 t) := by
      have ha : a5 t+k5 t-2=a6 t := by dsimp [a5,k5,a6]; omega
      have hk : (k5 t-2)/2=k6 t := by dsimp [k5,k6]; omega
      rw [ha,hk]

theorem step6 (t:Nat) :
    BB6.Agent15.affineNormalize (a6 t) (k6 t) =
    BB6.Agent15.affineNormalize (a7 t) (k7 t) := by
  have hg : 4≤k6 t ∧ k6 t % 2=0 ∧ (a6 t+k6 t)%4=1 := by
    dsimp [a6,k6]
    omega
  calc
    _ = BB6.Agent15.affineNormalize (a6 t+k6 t-2) ((k6 t-2)/2) := norm_step _ _ hg
    _ = BB6.Agent15.affineNormalize (a7 t) (k7 t) := by
      have ha : a6 t+k6 t-2=a7 t := by dsimp [a6,k6,a7]; omega
      have hk : (k6 t-2)/2=k7 t := by dsimp [k6,k7]; omega
      rw [ha,hk]

theorem terminal (t:Nat) :
    BB6.Agent15.affineNormalize (a7 t) (k7 t) = (a7 t, k7 t) := by
  have hnot : ¬(4≤k7 t ∧ k7 t%2=0 ∧ (a7 t+k7 t)%4=1) := by
    dsimp [a7,k7]
    omega
  exact norm_stop _ _ hnot

/-- Every member of this affine family has precisely seven forced
    affine-predecessor stripping steps in the original source normalizer. -/
theorem norm_family (t:Nat) :
    BB6.Agent15.affineNormalize (a0 t) (k0 t) = (a7 t,k7 t) := by
  rw [step0]
  rw [step1]
  rw [step2]
  rw [step3]
  rw [step4]
  rw [step5]
  rw [step6]
  exact terminal t

#print axioms norm_family
end BB6.Agent27Norm
