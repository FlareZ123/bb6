import CZeroHeadFrontier
import W4HeadPrefix
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429CZeroHeadPrefix
open BB6Coverage BB429OddExcursion BB429CZeroEvenReturn
open BB429CZeroContext BB429CZeroHeadFrontier BB429W4HeadMax
open BB429W4HeadPrefix BB429DeltaPhysicalBridge BB429PhysicalBridge
open BB429SourceE1Delta

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

/-- The entire even C/0 return has a sharp all-prefix head bound +3. -/
theorem even_C0_context_prefix_le_three (k t : Nat) (tail : List Bool)
    (ht : t ≤ 4*k+11) (p : Zipper × Int × Int)
    (hp : runWithMax t (z 2 (ones (2*k+2) ++ false::tail) false []) = some p) :
    p.2.1 ≤ 3 := by
  have hlen : t+(4*k+11-t) = 4*k+11 := by omega
  have hfull := even_C0_context_max k tail
  rw [← hlen] at hfull
  exact runWithMax_prefix_le t (4*k+11-t)
    (z 2 (ones (2*k+2) ++ false::tail) false []) p hp
    (z 2 (true::false::(ones (2*k+4) ++ tail)) false [],3,3) hfull

/-- All source prefixes admit a raw physical simulation at most +3 right. -/
theorem physical_even_C0_context_all_prefix (k t : Nat) (tail : List Bool)
    (c : Config)
    (hrep : Represents (z 2 (ones (2*k+2) ++ (false::tail)) false []) c)
    (ht : t ≤ 4*k+11) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 t c = some c' ∧
      c'.head ≤ c.head + 3 := by
  let start := z 2 (ones (2*k+2) ++ (false::tail)) false []
  have hlen : t+(4*k+11-t) = 4*k+11 := by omega
  have hfull := even_C0_context_max k tail
  change runWithMax (4*k+11) start = _ at hfull
  rw [← hlen,runWithMax_add] at hfull
  cases hp : runWithMax t start with
  | none => simp [hp] at hfull
  | some p =>
      have hdelta : runWithDelta t start = some (p.1,p.2.1) := by
        have hproj := runWithMax_toDelta t start
        simpa [hp] using hproj.symm
      obtain ⟨c', hraw, _, hhead⟩ :=
        source_runWithDelta_rep t start c hrep p.1 p.2.1 hdelta
      have hmax : p.2.1 ≤ 3 :=
        even_C0_context_prefix_le_three k t tail ht p (by simpa [start] using hp)
      refine ⟨c',hraw,?_⟩
      omega

/-- At the endpoint the original physical head advances three exactly. -/
theorem physical_even_C0_context_endpoint (k : Nat) (tail : List Bool) (c : Config)
    (hrep : Represents (z 2 (ones (2*k+2) ++ (false::tail)) false []) c) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 (4*k+11) c = some c' ∧
      Represents (z 2 (true::false::(ones (2*k+4) ++ tail)) false []) c' ∧
      c'.head = c.head + 3 := by
  have hdelta : runWithDelta (4*k+11)
      (z 2 (ones (2*k+2) ++ (false::tail)) false []) =
    some (z 2 (true::false::(ones (2*k+4) ++ tail)) false [],3) := by
    have hproj := runWithMax_toDelta (4*k+11)
      (z 2 (ones (2*k+2) ++ (false::tail)) false [])
    simpa [even_C0_context_max k tail] using hproj.symm
  exact source_runWithDelta_rep (4*k+11) _ c hrep _ 3 hdelta

/-- A genuine blank-run C/0 head record stays a global right record
    across the complete even-context return, for any distant tape. -/
theorem authentic_even_C0_record_extension (n k : Nat) (tail : List Bool)
    (c : Config)
    (hroot : BB6Coverage.run BB429PhysicalFrontier.target429 n BB6Coverage.blank = some c)
    (hrep : Represents (z 2 (ones (2*k+2) ++ (false::tail)) false []) c)
    (hprior : ∀ t (d : Config), t ≤ n →
      BB6Coverage.run BB429PhysicalFrontier.target429 t BB6Coverage.blank = some d →
      d.head ≤ c.head) :
    ∃ d, BB6Coverage.run BB429PhysicalFrontier.target429 (n+4*k+11) BB6Coverage.blank = some d ∧
      Represents (z 2 (true::false::(ones (2*k+4) ++ tail)) false []) d ∧
      d.head = c.head + 3 ∧
      (∀ t (d' : Config), t ≤ n+4*k+11 →
        BB6Coverage.run BB429PhysicalFrontier.target429 t BB6Coverage.blank = some d' →
        d'.head ≤ d.head) := by
  obtain ⟨d,hsegment,hrep',hhead⟩ := physical_even_C0_context_endpoint k tail c hrep
  refine ⟨d,?_,hrep',hhead,?_⟩
  · rw [show n+4*k+11 = n+(4*k+11) by omega,physical_run_add,hroot]
    exact hsegment
  · intro t d' ht hroot'
    by_cases hle : t ≤ n
    · have h := hprior t d' hle hroot'
      omega
    · have hsplit : t = n+(t-n) := by omega
      have hremain : t-n ≤ 4*k+11 := by omega
      obtain ⟨p,hp,hpbound⟩ :=
        physical_even_C0_context_all_prefix k (t-n) tail c hrep hremain
      have hpt : BB6Coverage.run BB429PhysicalFrontier.target429 t BB6Coverage.blank =
          some p := by
        rw [hsplit,physical_run_add,hroot]
        exact hp
      have heq : p = d' := Option.some.inj (hpt.symm.trans hroot')
      subst d'
      omega

#print axioms even_C0_context_prefix_le_three
#print axioms physical_even_C0_context_all_prefix
#print axioms physical_even_C0_context_endpoint
#print axioms authentic_even_C0_record_extension
end BB429CZeroHeadPrefix
