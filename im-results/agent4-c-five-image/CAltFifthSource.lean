import CAltFifthArithmetic
import CAllDepthBlank
import ConeBroadSource
import ThreeConeProper
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Five
open BB6.Agent46

private theorem root_absent_from_forced_parent (x y a k time : Nat)
    (hy : y≠1)
    (hforce : ∀ b l, secNext (b,l)=some (x,y) → b=a ∧ l=k)
    (hparent : ∀ n, BB6.Agent8Section.run secNext n (some (5,1)) ≠ some (a,k)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  cases time with
  | zero =>
      intro hit
      simp [BB6.Agent8Section.run] at hit
      omega
  | succ n =>
      intro hit
      change (BB6.Agent8Section.run secNext n (some (5,1))).bind secNext =
        some (x,y) at hit
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [hp] at hit
      | some p =>
          rcases p with ⟨b,l⟩
          have hstep : secNext (b,l)=some (x,y) := by simpa [hp] using hit
          obtain ⟨hb,hl⟩ := hforce b l hstep
          rw [hb,hl] at hp
          exact hparent n hp

private theorem E_absent (w t time : Nat) (he : (w+t)%2=0) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (52*w+100*t+81,6*w+14*t+9) := by
  cases time with
  | zero =>
      intro hit
      simp [BB6.Agent8Section.run] at hit
  | succ n =>
      intro hit
      have hp := BB6.Agent3.blank_section_odd_image n
        (52*w+100*t+81) (6*w+14*t+9) hit (by omega) (by omega)
      omega

private theorem D_absent (w t time : Nat) (he : (w+t)%2=0) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (40*w+72*t+63,12*w+28*t+20) := by
  apply root_absent_from_forced_parent
    (40*w+72*t+63) (12*w+28*t+20)
    (52*w+100*t+81) (6*w+14*t+9) time (by omega)
  · intro b l hstep
    have hinv : sectionPreimageAll b l _ _ :=
      (section_preimage_all_iff b l _ _).mp hstep
    have hcopy : BB6.Agent34Broad.sectionPreimageAll b l _ _ := hinv
    have hh := BB6.Agent34Three.only_direct b l
      (40*w+72*t+63) (12*w+28*t+20)
      (by omega) (by omega) (Or.inr (by omega)) hcopy
    omega
  · intro n
    exact E_absent w t n he

private theorem H_absent (w t time : Nat) (he : (w+t)%2=0) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (16*(w+t)+23,24*w+56*t+42) := by
  apply root_absent_from_forced_parent
    (16*(w+t)+23) (24*w+56*t+42)
    (40*w+72*t+63) (12*w+28*t+20) time (by omega)
  · intro b l hstep
    have hinv : sectionPreimageAll b l _ _ :=
      (section_preimage_all_iff b l _ _).mp hstep
    have hh := BB6.Agent4Three.only_direct_mod4_one b l
      (16*(w+t)+23) (24*w+56*t+42)
      (by omega) (by omega) (by omega) hinv
    omega
  · intro n
    exact D_absent w t n he

private theorem P_absent (w t time : Nat) (ht : 2≤t) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (64*(w+t)+101,32*t+6) := by
  apply root_absent_from_forced_parent
    (64*(w+t)+101) (32*t+6)
    (64*w+96*t+105) (16*t+2) time (by omega)
  · intro b l hstep
    have hinv : sectionPreimageAll b l _ _ :=
      (section_preimage_all_iff b l _ _).mp hstep
    have hcopy : BB6.Agent34Broad.sectionPreimageAll b l _ _ := hinv
    have hh := BB6.Agent34Three.only_direct b l
      (64*(w+t)+101) (32*t+6)
      (by omega) (by omega) (Or.inr (by omega)) hcopy
    omega
  · intro n
    have hsector : (((64*w+96*t+105)+(16*t+2))%8=1 ∧ (16*t+2)%16=10) ∨
        (((64*w+96*t+105)+(16*t+2))%8=3 ∧ (16*t+2)%16=2) := by
      right
      omega
    exact BB6.Agent34Three.cone_blank_unreachable n
      (64*w+96*t+105) (16*t+2) (by omega) hsector

/-- All original blank-section returns avoid this two-branch fifth-image cylinder. -/
theorem fifth_blank_unreachable (w t time : Nat)
    (ht : 2≤t) (he : (w+t)%2=0) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (64*w+89,64*t+14) := by
  cases time with
  | zero =>
      intro hit
      simp [BB6.Agent8Section.run] at hit
  | succ n =>
      intro hit
      change (BB6.Agent8Section.run secNext n (some (5,1))).bind secNext =
        some (64*w+89,64*t+14) at hit
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [hp] at hit
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some (64*w+89,64*t+14) := by
            simpa [hp] using hit
          have hinv : sectionPreimageAll a k (64*w+89) (64*t+14) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases two_parent_arithmetic a k w t hinv with hd|hb
          · rw [hd.1,hd.2] at hp
            exact P_absent w t n ht hp
          · rw [hb.1,hb.2] at hp
            exact H_absent w t n he hp

#print axioms fifth_blank_unreachable
end BB6.Agent4Five
