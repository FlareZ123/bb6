import BB429ShiftRays
import BB429SurvivorBase
import Lean.Elab.Tactic.Omega

namespace BB429Combined677
set_option maxHeartbeats 30000000
set_option maxRecDepth 40000

/-- The four genuine-root inverse/rank exclusions newly surviving Agent 1's
    complete 673-class sieve, expressed at the common modulus 262144. -/
def extra : List Nat := [765,3281,2385,16381]

def excluded677 : List Nat := BB429SplitSieve.excluded ++ extra

/-- Genuine full-table necessary-mask cardinality, with no double counting. -/
theorem excluded677_count : excluded677.length = 677 := by
  simp [excluded677, extra, List.length_append,
    BB429SplitSieve.excluded_count]

theorem excluded677_nodup : excluded677.Nodup := by decide

/-- All authentic accelerated blank-root terminal counters avoid the
    union of the source-proved 673 classes and four shifted-root classes. -/
theorem blank_halt_not_677 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) :
    a%262144 ∉ excluded677 := by
  intro h
  obtain hOld | hExtra := List.mem_append.mp h
  · exact BB429SplitSieve.blank_halt_not_excluded n a b hr hg hOld
  · have hFour : a%262144=765 ∨ a%262144=3281 ∨
        a%262144=2385 ∨ a%262144=16381 := by
      simpa [extra] using hExtra
    obtain h765 | h3281 | h2385 | h16381 := hFour
    · exact (BB429ShiftRays.blank_halt_not_765_mod_32768 n a b hr hg)
        (by omega)
    · exact (BB429ShiftRays.blank_halt_not_3281_mod_32768 n a b hr hg)
        (by omega)
    · exact (BB429ShiftRays.blank_halt_not_2385_mod_262144 n a b hr hg) h2385
    · exact (BB429ShiftRays.blank_halt_not_16381_mod_131072 n a b hr hg)
        (by omega)

/-- Precisely the original source mask's 255 unresolved 18-bit lifts,
    with the four newly certified roots removed. -/
def still251 : List Nat :=
  BB429SurvivorMask.live255.filter (fun r => decide (r ∉ extra))

theorem still251_count : still251.length = 251 := by decide

theorem still251_nodup : still251.Nodup := by decide

/-- The new explicit mask is exactly the old necessary 58/16384 mask
    intersected with the complement of all 677 source exclusions. -/
theorem still251_iff (u : Nat) :
    u%262144 ∈ still251 ↔
      u%16384 ∈ BB429SurvivorMask.base58 ∧
      u%262144 ∉ excluded677 := by
  constructor
  · intro h
    obtain ⟨hLive,hExtra⟩ := List.mem_filter.mp h
    obtain ⟨hBase,hOld⟩ :=
      (BB429SurvivorMask.live255_iff u).mp hLive
    refine ⟨hBase, ?_⟩
    intro hBad
    obtain hOrig | hNew := List.mem_append.mp hBad
    · exact hOld hOrig
    · exact (of_decide_eq_true hExtra) hNew
  · rintro ⟨hBase,hSafe⟩
    have hOld : u%262144 ∉ BB429SplitSieve.excluded := by
      intro hh
      exact hSafe (List.mem_append.mpr (Or.inl hh))
    have hExtra : u%262144 ∉ extra := by
      intro hh
      exact hSafe (List.mem_append.mpr (Or.inr hh))
    apply List.mem_filter.mpr
    constructor
    · exact (BB429SurvivorMask.live255_iff u).mpr ⟨hBase,hOld⟩
    · exact decide_eq_true hExtra

#print axioms excluded677_count
#print axioms excluded677_nodup
#print axioms blank_halt_not_677
#print axioms still251_count
#print axioms still251_nodup
#print axioms still251_iff
end BB429Combined677
