import CZeroContextMax
import W4HeadPrefix
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429CZeroContextPrefix
open BB429OddExcursion BB429SourceE1Delta
open BB429W4HeadMax BB429W4HeadPrefix
open BB429PhysicalBridge BB429DeltaPhysicalBridge
open BB6Coverage BB429PhysicalFrontier

private def ones (n : Nat) : List Bool := List.replicate n true

private def entry (k : Nat) (left right : List Bool) : Zipper :=
  z 2 (true::false::(ones (2*k+4) ++ (false::false::left)))
    false (false::right)

private def finish (k : Nat) (left right : List Bool) : Zipper :=
  z 0 (ones 6 ++ left) true (ones (2*k+1) ++ (false::true::right))

/-- The exact full-run maximum certificate also proves total successful
    execution at every bounded prefix, without any finite simulation cap. -/
theorem context_prefix_exists (k t : Nat) (left right : List Bool)
    (ht : t ≤ 2*k+22) :
    ∃ p, runWithMax t (entry k left right) = some p := by
  have hfull : runWithMax (2*k+22) (entry k left right) =
      some (finish k left right,-((2*k+2 : Nat) : Int),1) :=
    BB429CZeroContextMax.czero_context_max k left right
  have hs : t+(2*k+22-t) = 2*k+22 := by omega
  rw [← hs,runWithMax_add] at hfull
  cases h : runWithMax t (entry k left right) with
  | none => simp [h] at hfull
  | some p => exact ⟨p,rfl⟩

/-- All successful primitive prefixes of the C/0 source corridor
    end at most one cell to the right of its entry, for every k and every
    uninspected left/right tape tail. -/
theorem context_all_prefix_bound (k t : Nat) (left right : List Bool)
    (ht : t ≤ 2*k+22) (q : Zipper) (delta : Int)
    (hrun : runWithDelta t (entry k left right) = some (q,delta)) :
    delta ≤ 1 := by
  have hproj := runWithMax_toDelta t (entry k left right)
  cases hmax : runWithMax t (entry k left right) with
  | none => simp [hmax, hrun] at hproj
  | some p =>
    have hdelta : p.2.1 = delta := by
      simp [hmax,hrun] at hproj
      exact hproj.2
    have hlen : t+(2*k+22-t)=2*k+22 := by omega
    have hfull : runWithMax (t+(2*k+22-t)) (entry k left right) =
        some (finish k left right,-((2*k+2 : Nat) : Int),1) := by
      rw [hlen]
      exact BB429CZeroContextMax.czero_context_max k left right
    have hle := runWithMax_prefix_le t (2*k+22-t)
      (entry k left right) p hmax
      (finish k left right,-((2*k+2 : Nat) : Int),1) hfull
    simp only [Prod.snd] at hle
    omega

/-- Original six-state two-symbol bi-infinite tape, all k, all t bounded
    by 2k+22, arbitrary remote tails. Each primitive prefix exists and
    never has a head coordinate greater than the initial coordinate +1. -/
theorem original_context_all_prefix_bound (k t : Nat)
    (left right : List Bool) (c : Config)
    (hc : Represents (entry k left right) c)
    (ht : t ≤ 2*k+22) :
    ∃ c', BB6Coverage.run target429 t c = some c' ∧
      c'.head ≤ c.head+1 := by
  obtain ⟨p,hmax⟩ := context_prefix_exists k t left right ht
  have hproj := runWithMax_toDelta t (entry k left right)
  have hdelta : runWithDelta t (entry k left right) =
      some (p.1,p.2.1) := by
    rw [hmax] at hproj
    simp only [Option.map_some] at hproj
    exact hproj.symm
  obtain ⟨c',hraw,_,hhead⟩ :=
    source_runWithDelta_rep t (entry k left right) c hc
      p.1 p.2.1 hdelta
  have hb := context_all_prefix_bound k t left right ht p.1 p.2.1 hdelta
  exact ⟨c',hraw,by omega⟩

#print axioms context_prefix_exists
#print axioms context_all_prefix_bound
#print axioms original_context_all_prefix_bound
end BB429CZeroContextPrefix
