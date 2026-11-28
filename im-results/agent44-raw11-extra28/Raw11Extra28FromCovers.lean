import Raw11Extra28AllChildren
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Proof-independent exact finite-roster composition. Unlike the Route 158
constructor, this computes the exact 12-child membership complement
from *only* literal tables, never from an opaque certificate proof term.
It then consumes independent Covers at the twelve distinct bounds using
the already-sound Q0RosterConsume.sameTable checker. This is conditional
until the genuine child Covers are supplied. No oracle or unproved leaf.
-/
namespace BB6.Agent44Extra28FromCovers
open BB6Coverage BB6.Agent13BlankDelay

def p7 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨true,true,1⟩)
def p8 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨false,false,2⟩)
def p9 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨false,true,2⟩)
def p10 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨true,false,2⟩)
def p12 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨false,false,3⟩)
def p13 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨false,true,3⟩)
def p14 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨true,false,3⟩)
def p15 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨true,true,3⟩)
def p16 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨false,false,4⟩)
def p17 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨false,true,4⟩)
def p18 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨true,false,4⟩)
def p19 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨true,true,4⟩)

def covered : List PartialMachine := [
  p7,
  p8,
  p9,
  p10,
  p12,
  p13,
  p14,
  p15,
  p16,
  p17,
  p18,
  p19
]

theorem no_residual :
    Q0RosterConsume.removeCovered BB6.Agent44Extra28AllChildren.remaining covered = [] := by
  decide +kernel

structure Covers where
  c7 : Cover (WeightedBound 72) p7
  c8 : Cover (WeightedBound 42) p8
  c9 : Cover (WeightedBound 84) p9
  c10 : Cover (WeightedBound 101) p10
  c12 : Cover (WeightedBound 64) p12
  c13 : Cover (WeightedBound 79) p13
  c14 : Cover (WeightedBound 96) p14
  c15 : Cover (WeightedBound 119) p15
  c16 : Cover (WeightedBound 81) p16
  c17 : Cover (WeightedBound 150) p17
  c18 : Cover (WeightedBound 141) p18
  c19 : Cover (WeightedBound 158) p19

theorem all_covered (h : Covers) :
    ∀ p ∈ covered, Cover (WeightedBound 158) p := by
  intro p hp
  simp only [covered, List.mem_cons, List.mem_singleton] at hp
  rcases hp with h7 | h8 | h9 | h10 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19
  · subst p
    exact Q0RosterConsume.liftCover (by decide : 72 ≤ 158) h.c7
  · subst p
    exact Q0RosterConsume.liftCover (by decide : 42 ≤ 158) h.c8
  · subst p
    exact Q0RosterConsume.liftCover (by decide : 84 ≤ 158) h.c9
  · subst p
    exact Q0RosterConsume.liftCover (by decide : 101 ≤ 158) h.c10
  · subst p
    exact Q0RosterConsume.liftCover (by decide : 64 ≤ 158) h.c12
  · subst p
    exact Q0RosterConsume.liftCover (by decide : 79 ≤ 158) h.c13
  · subst p
    exact Q0RosterConsume.liftCover (by decide : 96 ≤ 158) h.c14
  · subst p
    exact Q0RosterConsume.liftCover (by decide : 119 ≤ 158) h.c15
  · subst p
    exact Q0RosterConsume.liftCover (by decide : 81 ≤ 158) h.c16
  · subst p
    exact Q0RosterConsume.liftCover (by decide : 150 ≤ 158) h.c17
  · subst p
    exact Q0RosterConsume.liftCover (by decide : 141 ≤ 158) h.c18
  · subst p
    exact Q0RosterConsume.liftCover (by decide : 158 ≤ 158) h.c19

theorem safe (h : Covers) :
    ∀ m, compatible BB6.Agent44Extra28AllChildren.parent m → WeightedBound 158 m :=
  (BB6.Agent44Extra28AllChildren.consume 158 (by decide)
    (Q0RosterConsume.consume 158 BB6.Agent44Extra28AllChildren.remaining covered
      (all_covered h)
      (by
        intro p hp
        rw [no_residual] at hp
        cases hp))).sound

theorem completeCover (h : Covers) :
    Cover (WeightedBound 158) BB6.Agent44Extra28AllChildren.parent :=
  .leaf _ (safe h)

theorem completeCoverAt (B : Nat) (hB : 158 ≤ B) (h : Covers) :
    Cover (WeightedBound B) BB6.Agent44Extra28AllChildren.parent :=
  Q0RosterConsume.liftCover hB (completeCover h)

#print axioms no_residual
#print axioms all_covered
#print axioms completeCover
end BB6.Agent44Extra28FromCovers
