import SourceBridgeB
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

theorem pow_mod24_all (m : Nat) (hm : 2 ≤ m) : (2^(2*m+2))%24=16 := by
  have h : ∀ t : Nat, (2^(2*(t+2)+2))%24=16 := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
      have he : 2*(t+1+2)+2=(2*(t+2)+2)+2 := by omega
      rw [he, Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega
  have hh := h (m-2)
  have he : m-2+2=m := by omega
  simpa only [he] using hh

theorem pow_bound (m : Nat) (hm : 1 ≤ m) : 3*m+9 ≤ 2^(2*m+2) := by
  have h : ∀ t : Nat, 3*(t+1)+9 ≤ 2^(2*(t+1)+2) := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
      have he : 2*(t+1+1)+2=(2*(t+1)+2)+2 := by omega
      rw [he, Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega
  have hh := h (m-1)
  have he : m-1+1=m := by omega
  simpa only [he] using hh

end BB6.Agent46

set_option maxHeartbeats 0

namespace BB6.Agent46
open BB6CLine

/-- A c=0 target with nonzero middle counter has a unique immediate source. -/
theorem c0_parent (a k : Nat) (hk : 1 ≤ k)
    (s : Nat × Nat × Nat) (h : nextC s = some (a,k,0)) :
    s=(a,k-1,1) := by
  rcases s with ⟨x,y,z⟩
  rcases z with _ | _ | _ | _ | z
  · rcases x with _ | _ | x
    · simp [nextC] at h
    · rcases y with _ | y <;> simp [nextC] at h
    · simp [nextC] at h
  · simp [nextC] at h
    rcases h with ⟨hx,hy⟩
    simp only [Prod.mk.injEq, and_true]
    constructor
    · exact hx
    · omega
  · simp [nextC] at h
  · simp [nextC] at h
  · rcases x with _ | x
    · by_cases he : y%2=0
      · simp [nextC,he] at h
      · simp [nextC,he] at h
    · simp [nextC] at h

/-- For middle counter at least three, every c=1 target has a unique source. -/
theorem c1_parent (a k : Nat) (hk : 3 ≤ k)
    (s : Nat × Nat × Nat) (h : nextC s = some (a,k,1)) :
    s=(a,k-2,3) := by
  rcases s with ⟨x,y,z⟩
  rcases z with _ | _ | _ | _ | z
  · rcases x with _ | _ | x
    · simp [nextC] at h
    · rcases y with _ | y
      · simp [nextC] at h
        omega
      · simp [nextC] at h
        omega
    · simp [nextC] at h
      omega
  · simp [nextC] at h
  · simp [nextC] at h
  · simp [nextC] at h
    rcases h with ⟨hx,hy⟩
    simp only [Prod.mk.injEq, and_true]
    constructor
    · exact hx
    · omega
  · rcases x with _ | x
    · by_cases he : y%2=0
      · simp [nextC,he] at h
        omega
      · simp [nextC,he] at h
    · simp [nextC] at h

theorem reach_c0_parent (a k : Nat) (hk : 1 ≤ k)
    (hr : Reach (a,k,0)) : Reach (a,k-1,1) := by
  cases hr with
  | next s t hs ht =>
    have eq := c0_parent a k hk s ht
    rw [eq] at hs
    exact hs

theorem reach_c1_parent (a k : Nat) (hk : 3 ≤ k)
    (hr : Reach (a,k,1)) : Reach (a,k-2,3) := by
  cases hr with
  | init => omega
  | next s t hs ht =>
    have eq := c1_parent a k hk s ht
    rw [eq] at hs
    exact hs

theorem reach_c0_two_parent (a k : Nat) (hk : 4 ≤ k)
    (hr : Reach (a,k,0)) : Reach (a,k-3,3) := by
  have h1 := reach_c0_parent a k (by omega) hr
  have h2 := reach_c1_parent a (k-1) (by omega) h1
  simpa only [show k-1-2=k-3 by omega] using h2

/-- Terminal residue cylinders inherited from backward-closed high-c core A. -/
theorem no_reach_A_3_7 (a K : Nat) (hK : 4 ≤ K)
    (ha : a % 48 = 3) (hk : K % 24 = 7)
    (hr : Reach (a,K,0)) : False := by
  have hp := reach_c0_two_parent a K hK hr
  have hbad := A4Backward.source_blank_never_bad (a,K-3,3) hp
  apply hbad
  simp only [A4Backward.bad, show ¬((3:Nat)<2) by omega, ↓reduceIte, A4Backward.high]
  left
  omega

theorem no_reach_A_27_19 (a K : Nat) (hK : 4 ≤ K)
    (ha : a % 48 = 27) (hk : K % 24 = 19)
    (hr : Reach (a,K,0)) : False := by
  have hp := reach_c0_two_parent a K hK hr
  have hbad := A4Backward.source_blank_never_bad (a,K-3,3) hp
  apply hbad
  simp only [A4Backward.bad, show ¬((3:Nat)<2) by omega, ↓reduceIte, A4Backward.high]
  right;right;right;right;left
  omega

/-- Terminal residue cylinders inherited from backward-closed high-c core B. -/
theorem no_reach_B_11_11 (a K : Nat) (hK : 4 ≤ K)
    (ha : a % 48 = 11) (hk : K % 24 = 11)
    (hr : Reach (a,K,0)) : False := by
  have hp := reach_c0_two_parent a K hK hr
  have hbad := A4BackwardB.source_blank_never_badB (a,K-3,3) hp
  apply hbad
  simp only [A4BackwardB.badB, show ¬((3:Nat)<2) by omega, ↓reduceIte, A4BackwardB.highB]
  right;left
  omega

theorem no_reach_B_35_23 (a K : Nat) (hK : 4 ≤ K)
    (ha : a % 48 = 35) (hk : K % 24 = 23)
    (hr : Reach (a,K,0)) : False := by
  have hp := reach_c0_two_parent a K hK hr
  have hbad := A4BackwardB.source_blank_never_badB (a,K-3,3) hp
  apply hbad
  simp only [A4BackwardB.badB, show ¬((3:Nat)<2) by omega, ↓reduceIte, A4BackwardB.highB]
  right;right;right;right;right;left
  omega

/-- Entire high stopping family j≡0 (mod12), m≡4 (mod8), on the original
    accelerated blank orbit, eliminated without a finite search cutoff. -/
theorem high_stop_j12_m4_excluded (j m k : Nat)
    (hj : j%12=0) (hm : m%8=4)
    (heq : k+j+3*m+5 = 2^(2*m+2)*(j+3)) :
    ¬ Reach (2*j+3,k,0) := by
  intro hr
  have hm4 : 4≤m := by omega
  have hpower : 3*m+9≤2^(2*m+2) := pow_bound m (by omega)
  have hpge : 1≤2^(2*m+2) := by omega
  have hjmul : j≤2^(2*m+2)*j := by
    simpa using Nat.mul_le_mul_right j hpge
  have hprod : 2^(2*m+2)*(j+3) = 2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add,Nat.mul_comm]
  have hkle : 4≤k := by
    rw [hprod] at heq
    omega
  have hp24 : (2^(2*m+2))%24=16 := pow_mod24_all m (by omega)
  have hmod0 : (2^(2*m+2)*(j+3))%24=0 := by
    rw [Nat.mul_mod, hp24]
    have hj24 : (j+3)%24=3 ∨ (j+3)%24=15 := by omega
    rcases hj24 with hh | hh <;> rw [hh] <;> decide
  have heqmod : (k+j+3*m+5)%24=0 := by
    rw [heq]
    exact hmod0
  have j24 : j%24=0 ∨ j%24=12 := by omega
  rcases j24 with j0 | j12
  · have ha : (2*j+3)%48=3 := by omega
    have hk : k%24=7 := by omega
    exact no_reach_A_3_7 (2*j+3) k hkle ha hk hr
  · have ha : (2*j+3)%48=27 := by omega
    have hk : k%24=19 := by omega
    exact no_reach_A_27_19 (2*j+3) k hkle ha hk hr

#print axioms c0_parent
#print axioms c1_parent
#print axioms no_reach_A_3_7
#print axioms no_reach_A_27_19
#print axioms no_reach_B_11_11
#print axioms no_reach_B_35_23
#print axioms high_stop_j12_m4_excluded

end BB6.Agent46
