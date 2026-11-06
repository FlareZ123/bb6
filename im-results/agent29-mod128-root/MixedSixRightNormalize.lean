import MixedNormalize
import RootMod128Source
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Mixed
open BB6.Agent46

/-- Extend the source-certified even-right unique-parent gate into an additional
    nonunique 2-adic sum-seven section by eliminating its bounce parent
    using the actual blank-root odd-image obstruction. -/
def mixedSixRightGate (x y : Nat) : Prop :=
  BB6.Agent19Seven.mixedEvenRightGate x y ∨
  (x%8=5 ∧ y%2=0 ∧ 6≤y ∧ (x+y+1)%128=96 ∧ 48≤x+y+1)

instance mixedSixRightGate_decidable (x y : Nat) :
    Decidable (mixedSixRightGate x y) := by
  unfold mixedSixRightGate BB6.Agent19Seven.mixedEvenRightGate sixEvenRightGate
  infer_instance

/-- A terminating deterministic normalization that follows exactly
    blank-root-equivalent inverse section edges. -/
def mixedSixRightNormalize (x y : Nat) : Nat × Nat :=
  if hg : mixedSixRightGate x y then
    mixedSixRightNormalize (x+y-2) ((y-2)/2)
  else (x,y)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [mixedSixRightGate, BB6.Agent19Seven.mixedEvenRightGate, sixEvenRightGate] at *
    omega

theorem mixedSix_reach_iff_normalize (x y : Nat) :
    BB6.Agent3.CReach x y ↔
    BB6.Agent3.CReach (mixedSixRightNormalize x y).1
                       (mixedSixRightNormalize x y).2 := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y with
  | ind z ih =>
      unfold mixedSixRightNormalize
      by_cases hg : mixedSixRightGate x y
      · rw [dif_pos hg]
        have hnext : BB6.Agent3.CReach x y ↔
          BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
          rcases hg with hn|hs
          · rcases hn with hn|hseven
            · rcases hn with ⟨hy,he,h0,h7⟩
              exact six_even_right_blank_reach_iff x y hy he h0 h7
            · rcases hseven with ⟨hx,hy,hmod,hbig⟩
              exact BB6.Agent19Seven.sumseven_forced_root_iff x y hx hy hmod hbig
          · rcases hs with ⟨hx,hy,hy6,hmod,hbig⟩
            exact BB6.Agent29New.sum96_forced_root_iff x y hx hy hy6 hmod hbig
        have hlt : (x+y-2)+2*((y-2)/2)<z := by
          rcases hg with hn|hs
          · rcases hn with hn|hseven
            · rcases hn with ⟨hy,_,_,_⟩
              omega
            · rcases hseven with ⟨_,hy,_,_⟩
              omega
          · rcases hs with ⟨_,_,hy6,_,_⟩
            omega
        have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
        exact hnext.trans hrec
      · rw [dif_neg hg]

/-- Executable original-blank disjointness test after mixed normalization. -/
def mixedSixRightExcluded (x y : Nat) : Bool :=
  let p := mixedSixRightNormalize x y
  decide (5≤p.2 ∧ p.2%2=1 ∧
     ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2))

theorem mixedSixRightExcluded_sound (x y : Nat)
    (hex : mixedSixRightExcluded x y = true) :
    ∀ time, BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  intro time ht
  obtain ⟨n,hn⟩ := (mixedSix_reach_iff_normalize x y).mp ⟨time,ht⟩
  have hh : 5≤(mixedSixRightNormalize x y).2 ∧
      (mixedSixRightNormalize x y).2%2=1 ∧
      (((mixedSixRightNormalize x y).1+(mixedSixRightNormalize x y).2)%4=1 ∨
       ((mixedSixRightNormalize x y).1+(mixedSixRightNormalize x y).2)%4=2) := by
    simpa [mixedSixRightExcluded] using (of_decide_eq_true hex)
  rcases hh with ⟨hy,ho,hbad⟩
  cases n with
  | zero =>
      have heq : ((mixedSixRightNormalize x y).1,
          (mixedSixRightNormalize x y).2)=(5,1) := by
        apply Option.some.inj
        simpa [BB6.Agent8Section.run] using hn.symm
      have hp := congrArg Prod.snd heq
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (mixedSixRightNormalize x y).1 (mixedSixRightNormalize x y).2 hn hy ho
      omega

#print axioms mixedSix_reach_iff_normalize
#print axioms mixedSixRightExcluded_sound
end BB6.Agent29Mixed
