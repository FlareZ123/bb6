import CZeroContextToE1Max
import W4HeadPrefix
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429CZeroContextToE1Physical
open BB6Coverage BB429OddExcursion BB429CZeroEvenReturn
open BB429CZeroContextToE1Max BB429W4HeadMax BB429W4HeadPrefix
open BB429PhysicalBridge BB429DeltaPhysicalBridge BB429SourceE1Delta

private theorem physical_run_add (m n : Nat) (c : Config) :
    BB6Coverage.run BB429PhysicalFrontier.target429 (m+n) c =
      (BB6Coverage.run BB429PhysicalFrontier.target429 m c).bind
        (BB6Coverage.run BB429PhysicalFrontier.target429 n) := by
  induction n with
  | zero =>
      simp only [Nat.add_zero]
      change (BB6Coverage.run BB429PhysicalFrontier.target429 m c) =
        (BB6Coverage.run BB429PhysicalFrontier.target429 m c).bind (fun d => some d)
      cases BB6Coverage.run BB429PhysicalFrontier.target429 m c <;> rfl
  | succ n ih =>
      rw [Nat.add_succ]
      change ((BB6Coverage.run BB429PhysicalFrontier.target429 (m+n) c).bind
        (rawStep BB429PhysicalFrontier.target429)) =
        (BB6Coverage.run BB429PhysicalFrontier.target429 m c).bind
          (fun d => (BB6Coverage.run BB429PhysicalFrontier.target429 n d).bind
            (rawStep BB429PhysicalFrontier.target429))
      rw [ih]
      rw [Option.bind_assoc]

/-- Every original-machine physical prefix of the 6k+21 corridor has
    its head at most four positions right of the original C/0 head. -/
theorem physical_even_C0_to_E1_all_prefix (k t : Nat) (tail : List Bool)
    (c : Config)
    (hrep : Represents (z 2 (ones (2*k+2) ++ (false::tail)) false []) c)
    (ht : t ≤ 6*k+21) :
    ∃ d, BB6Coverage.run BB429PhysicalFrontier.target429 t c = some d ∧
      d.head ≤ c.head + 4 := by
  let start := z 2 (ones (2*k+2) ++ (false::tail)) false []
  have hlen : t+(6*k+21-t) = 6*k+21 := by omega
  have hfull := even_C0_to_E1_context_max k tail
  change runWithMax (6*k+21) start = _ at hfull
  rw [←hlen,runWithMax_add] at hfull
  cases hp : runWithMax t start with
  | none => simp [hp] at hfull
  | some p =>
      have hdelta : runWithDelta t start = some (p.1,p.2.1) := by
        have hproj := runWithMax_toDelta t start
        simpa [hp] using hproj.symm
      obtain ⟨d,hraw,_,hhead⟩ :=
        source_runWithDelta_rep t start c hrep p.1 p.2.1 hdelta
      have hpbound : p.2.1 ≤ 4 :=
        runWithMax_prefix_le t (6*k+21-t) start p hp
          (z 4 tail true (ones (2*k+4) ++ [true,false,true]),
            -(((2*k+3:Nat):Int)),4)
          (by rw [hlen]; simpa [start] using even_C0_to_E1_context_max k tail)
      refine ⟨d,hraw,?_⟩
      omega

/-- At the end of the complete two-C0 corridor, the original raw head
    is exactly 2k+3 cells to the left of its initial position. -/
theorem physical_even_C0_to_E1_endpoint (k : Nat) (tail : List Bool) (c : Config)
    (hrep : Represents (z 2 (ones (2*k+2) ++ (false::tail)) false []) c) :
    ∃ d, BB6Coverage.run BB429PhysicalFrontier.target429 (6*k+21) c = some d ∧
      Represents (z 4 tail true (ones (2*k+4) ++ [true,false,true])) d ∧
      d.head = c.head - ((2*k+3:Nat):Int) := by
  have hdelta : runWithDelta (6*k+21)
      (z 2 (ones (2*k+2) ++ (false::tail)) false []) =
    some (z 4 tail true (ones (2*k+4) ++ [true,false,true]),
      -(((2*k+3:Nat):Int))) := by
    have hproj := runWithMax_toDelta (6*k+21)
      (z 2 (ones (2*k+2) ++ (false::tail)) false [])
    simpa [even_C0_to_E1_context_max k tail] using hproj.symm
  obtain ⟨d,hr,hrep',hhead⟩ := source_runWithDelta_rep (6*k+21)
    (z 2 (ones (2*k+2) ++ (false::tail)) false []) c hrep
    (z 4 tail true (ones (2*k+4) ++ [true,false,true]))
    (-(((2*k+3:Nat):Int))) hdelta
  refine ⟨d,hr,hrep',?_⟩
  omega

/-- Authentic blank-run reduction: every reached even-context C/0 head
    enters the unknown-left-context E/1 section after 6k+21 steps,
    with an exact head shift and +4 global excursion bound. -/
theorem blank_even_C0_to_E1_corridor (n k : Nat) (tail : List Bool) (c : Config)
    (hroot : BB6Coverage.run BB429PhysicalFrontier.target429 n BB6Coverage.blank = some c)
    (hrep : Represents (z 2 (ones (2*k+2) ++ (false::tail)) false []) c) :
    ∃ d, BB6Coverage.run BB429PhysicalFrontier.target429 (n+6*k+21) BB6Coverage.blank = some d ∧
      Represents (z 4 tail true (ones (2*k+4) ++ [true,false,true])) d ∧
      d.head = c.head - ((2*k+3:Nat):Int) ∧
      (∀ t (p : Config), n ≤ t → t ≤ n+6*k+21 →
        BB6Coverage.run BB429PhysicalFrontier.target429 t BB6Coverage.blank = some p →
        p.head ≤ c.head+4) := by
  obtain ⟨d,hsegment,hrep',hhead⟩ := physical_even_C0_to_E1_endpoint k tail c hrep
  refine ⟨d,?_,hrep',hhead,?_⟩
  · rw [show n+6*k+21=n+(6*k+21) by omega,physical_run_add,hroot]
    exact hsegment
  · intro t p hle hge hp
    have ht : t = n+(t-n) := by omega
    have hremain : t-n ≤ 6*k+21 := by omega
    obtain ⟨q,hq,hqbound⟩ :=
      physical_even_C0_to_E1_all_prefix k (t-n) tail c hrep hremain
    have hqp : BB6Coverage.run BB429PhysicalFrontier.target429 t BB6Coverage.blank =
        some q := by
      rw [ht,physical_run_add,hroot]
      exact hq
    have heq : q = p := Option.some.inj (hqp.symm.trans hp)
    subst p
    omega

#print axioms physical_even_C0_to_E1_all_prefix
#print axioms physical_even_C0_to_E1_endpoint
#print axioms blank_even_C0_to_E1_corridor
end BB429CZeroContextToE1Physical
