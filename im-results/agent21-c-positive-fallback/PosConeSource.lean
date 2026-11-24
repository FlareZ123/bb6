import PosConeKernel
import FullSectionInverse
import M32SectionEmbedding
import CSourceBridge16
import EvenOddTwoParentRoot

namespace BB6.Agent21PositiveCone
open BB6.Agent46

def srcReach (p : P) : Prop := BB6.Agent3.CReach p.1 p.2
def srcSeen (p : P) : Bool := CCert.seen (CCert.q p.1) (CCert.q p.2) (CCert.q 0)

theorem predicate_agrees (a k x y : Nat) :
    inverse a k x y ↔ sectionPreimageCriterion a k x y := Iff.rfl

theorem src_seen (p : P) (hr : srcReach p) : srcSeen p=true := by
  have hr15 : BB6.Agent15.CReach p.1 p.2 := by
    simpa [srcReach,BB6.Agent3.CReach,BB6.Agent15.CReach] using hr
  have hline := BB6.Agent15.m32_section_reach_embeds hr15
  exact CCert.reachable_seen (CCert.source_reachable_embeds16 hline)

theorem src_bad_sound (p : P) (h : bad srcSeen p=true) : ¬srcReach p := by
  intro hr
  have hs := src_seen p hr
  simp only [bad,hs,Bool.not_true,Bool.false_or,decide_eq_true_eq] at h
  exact BB6.Agent13TwoParent.odd_forbidden_image p.1 p.2 h.1 h.2.1 h.2.2 hr

theorem src_parent (p : P) (hy : 5≤p.2) (hr : srcReach p) :
    ∃ a k, srcReach (a,k) ∧ inverse a k p.1 p.2 := by
  obtain ⟨n,hn⟩ := hr
  cases n with
  | zero =>
    have hp : (5,1)=p := by simpa [BB6.Agent8Section.run] using hn
    rw [←hp] at hy
    omega
  | succ n =>
    change (BB6.Agent8Section.run secNext n (some (5,1))).bind secNext=some p at hn
    cases he : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [he] at hn
    | some q =>
      have hn' : secNext q=some p := by simpa [he] using hn
      have hp : secNext (q.1,q.2)=some (p.1,p.2) := hn'
      exact ⟨q.1,q.2,⟨n,he⟩,(predicate_agrees _ _ _ _).mpr
        ((complete_section_inverse _ _ _ _ hy).mp hp)⟩

theorem check_source (f x y : Nat) (h : check srcSeen f (x,y)=true) :
    ¬BB6.Agent3.CReach x y :=
  check_sound srcReach srcSeen src_bad_sound src_parent f (x,y) h

#print axioms predicate_agrees
#print axioms src_seen
#print axioms src_parent
#print axioms check_source
end BB6.Agent21PositiveCone
