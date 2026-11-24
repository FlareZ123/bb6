import SparseBlankDelay
import CrossUpper
import TwoCylinder

namespace BB6.Agent13BlankDelay
open BB6Coverage

/-- The weight is computed on the concrete total completion, including
    every zero-symbol row not queried by its canonical blank run. -/
theorem weighted_of_never (B : Nat) (m : Machine) (h : NeverHalts m) :
    WeightedBound B m := by
  intro k d hk _
  have hn := h (k+1)
  rw [hk.2] at hn
  contradiction

theorem weighted_of_margin (B : Nat) (m : Machine)
    (h : DecidedBelow (B-5) m) (hB : 5≤B) : WeightedBound B m := by
  rcases h with hn|⟨n,hb,hh⟩
  · exact weighted_of_never B m hn
  · intro k d hk hd
    have he := halting_time_unique m k n hk hh
    have hlt : d<6 := by
      have hm : d∈List.range 6 := (List.mem_filter.mp hd).1
      exact List.mem_range.mp hm
    omega

/-- Exact sparse leaf rule, valid for every compatible total completion. -/
theorem weighted_halt_leaf (p : PartialMachine) (B n : Nat)
    (hf : p initialSlot=some (some ⟨true,true,1⟩))
    (hh : ∀ m, compatible p m → HaltsAfter m n)
    (hd : ∀ d∈possibleDelays p 0, d+n+1≤B) :
    Cover (WeightedBound B) p :=
  .leaf p ((uniform_halter_weight_iff p B n hf hh).mpr hd)

/-- A single weighted 1RB cover implies the universal raw 28-choice bound. -/
theorem raw_upper_from_weighted_first_one (B : Nat) (hB : 6≤B)
    (cert : Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder) :
    ∀ m : BB6.Coverage.RawMachine, ∀ n : Nat,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) n → n≤B := by
  apply (BB6.CoverageAdapter.universal_raw_upper_iff B).mp
  apply (upper_iff_weighted_first_one B hB).mpr
  intro m hf
  have hc : compatible BB6.CoverageAdapter.firstOneCylinder m := by
    exact (compatible_refine_iff emptyTable m initialSlot rfl
      (some ⟨true,true,(1 : Fin 6)⟩)).mpr ⟨empty_compatible m,hf⟩
  exact cert.sound m hc

theorem exact_from_weighted_first_one (B : Nat) (hB : 6≤B)
    (cert : Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  ⟨champ,raw_upper_from_weighted_first_one B hB cert⟩

#print axioms raw_upper_from_weighted_first_one
#print axioms exact_from_weighted_first_one
end BB6.Agent13BlankDelay
