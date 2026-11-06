import OddSevenForcedRoot
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Seven
open BB6.Agent46

/-- Extend the source-certified even-right unique-parent gate across a
    nonunique 2-adic sum-seven section by eliminating its bounce parent
    using the actual blank-root odd-image obstruction. -/
def mixedEvenRightGate (x y : Nat) : Prop :=
  sixEvenRightGate x y ∨
  (x%2=1 ∧ y%8=6 ∧ (x+y+1)%32=16 ∧ 48≤x+y+1)

instance mixedEvenRightGate_decidable (x y : Nat) :
    Decidable (mixedEvenRightGate x y) := by
  unfold mixedEvenRightGate sixEvenRightGate
  infer_instance

/-- A terminating deterministic normalization that follows exactly
    blank-root-equivalent inverse section edges. -/
def mixedEvenRightNormalize (x y : Nat) : Nat × Nat :=
  if hg : mixedEvenRightGate x y then
    mixedEvenRightNormalize (x+y-2) ((y-2)/2)
  else (x,y)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [mixedEvenRightGate,sixEvenRightGate] at *
    omega

theorem mixed_reach_iff_normalize (x y : Nat) :
    BB6.Agent3.CReach x y ↔
    BB6.Agent3.CReach (mixedEvenRightNormalize x y).1
                       (mixedEvenRightNormalize x y).2 := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y with
  | ind z ih =>
      unfold mixedEvenRightNormalize
      by_cases hg : mixedEvenRightGate x y
      · rw [dif_pos hg]
        have hnext : BB6.Agent3.CReach x y ↔
          BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
          rcases hg with hn|hs
          · rcases hn with ⟨hy,he,h0,h7⟩
            exact six_even_right_blank_reach_iff x y hy he h0 h7
          · rcases hs with ⟨hx,hy,hmod,hbig⟩
            exact sumseven_forced_root_iff x y hx hy hmod hbig
        have hlt : (x+y-2)+2*((y-2)/2)<z := by
          rcases hg with hn|hs
          · rcases hn with ⟨hy,_,_,_⟩
            omega
          · rcases hs with ⟨_,hy,_,_⟩
            omega
        have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
        exact hnext.trans hrec
      · rw [dif_neg hg]

/-- Executable original-blank disjointness test after mixed normalization. -/
def mixedEvenRightExcluded (x y : Nat) : Bool :=
  let p := mixedEvenRightNormalize x y
  decide (5≤p.2 ∧ p.2%2=1 ∧
     ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2))

theorem mixedEvenRightExcluded_sound (x y : Nat)
    (hex : mixedEvenRightExcluded x y = true) :
    ∀ time, BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  intro time ht
  obtain ⟨n,hn⟩ := (mixed_reach_iff_normalize x y).mp ⟨time,ht⟩
  have hh : 5≤(mixedEvenRightNormalize x y).2 ∧
      (mixedEvenRightNormalize x y).2%2=1 ∧
      (((mixedEvenRightNormalize x y).1+(mixedEvenRightNormalize x y).2)%4=1 ∨
       ((mixedEvenRightNormalize x y).1+(mixedEvenRightNormalize x y).2)%4=2) := by
    simpa [mixedEvenRightExcluded] using (of_decide_eq_true hex)
  rcases hh with ⟨hy,ho,hbad⟩
  cases n with
  | zero =>
      have heq : ((mixedEvenRightNormalize x y).1,
          (mixedEvenRightNormalize x y).2)=(5,1) := by
        apply Option.some.inj
        simpa [BB6.Agent8Section.run] using hn.symm
      have hp := congrArg Prod.snd heq
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (mixedEvenRightNormalize x y).1 (mixedEvenRightNormalize x y).2 hn hy ho
      omega

#print axioms mixed_reach_iff_normalize
#print axioms mixedEvenRightExcluded_sound
end BB6.Agent19Seven
