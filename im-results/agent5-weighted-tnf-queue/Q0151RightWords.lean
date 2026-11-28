import Q0151RightCut
import Q0151PhysicalStack

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151Category
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151RightCut
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151SourceMacro

/-!
A finite concrete right tape is a sequence of strictly positive runs of
ones, each followed by one zero. The abstract right signature stores the
category of its first run and a backward two-mode acceptance mask of the
remaining runs. This provides the first- and second-run cut-completeness
statements required by the real Turing-machine macro induction.
-/

def runBits : List Nat → List Bool
  | [] => []
  | n :: ns => rr (n+1) (runBits ns)

def suffixMask : List Nat → Nat
  | [] => 4
  | n :: ns => pre (cat (n+1)) (suffixMask ns)

def rightSig : List Nat → RightSummary
  | [] => emptyRight
  | n :: ns => ⟨cat (n+1),suffixMask ns⟩

theorem cat_pos (n : Nat) : cat (n+1) ≠ 0 := by
  by_cases h : n+1 ≤ 4
  · rw [cat_small (n+1) h]
    omega
  · have hlarge : 5 ≤ n+1 := by omega
    have hc := cat_large (n+1) hlarge
    omega

theorem cut_single (n : Nat) :
    (cat (n+1),emptyRight) ∈ cut (rightSig [n]) := by
  change (cat (n+1),emptyRight) ∈ cut ⟨cat (n+1),4⟩
  simp [cut,cat_pos n,emptyRight]

theorem cut_second (a b : Nat) (rest : List Nat)
    (hb : cat (b+1) ∈ firstVariants)
    (hr : suffixMask rest ∈ suffixVariants) :
    (cat (a+1),rightSig (b::rest)) ∈
      cut (rightSig (a::b::rest)) := by
  change (cat (a+1),⟨cat (b+1),suffixMask rest⟩) ∈
    cut ⟨cat (a+1),pre (cat (b+1)) (suffixMask rest)⟩
  exact cut_complete (cat (a+1)) (cat (b+1)) (suffixMask rest)
    (cat_pos a) hb hr

theorem rightSig_empty : rightSig [] = emptyRight := rfl
theorem runBits_cons (n : Nat) (rest : List Nat) :
    runBits (n::rest) = rr (n+1) (runBits rest) := rfl

#print axioms cat_pos
#print axioms cut_single
#print axioms cut_second
end BB6.Agent5Q0151RightWords
