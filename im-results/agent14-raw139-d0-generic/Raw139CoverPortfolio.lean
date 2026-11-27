import Raw139NormalizedE0CutsProspective

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139CoverPortfolio
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0CutsProspective

/-- Covers transport from a wider partial cylinder to any refinement. -/
def subsumes (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun s => [false, true].all fun b =>
    match p (s,b) with
    | none => true
    | some t => decide (q (s,b) = some t)

theorem subsumes_sound {p q : PartialMachine} (h : subsumes p q = true)
    {m : Machine} (hm : compatible q m) : compatible p m := by
  intro s t hs
  rcases s with ⟨a,b⟩
  have ha := List.all_eq_true.mp h a (List.mem_finRange a)
  have hb := List.all_eq_true.mp ha b (by cases b <;> simp)
  simp only [hs, decide_eq_true_eq] at hb
  exact hm (a,b) t hb

theorem cover_restrict {good : Machine → Prop} {p q : PartialMachine}
    (h : subsumes p q = true) (hp : Cover good p) : Cover good q :=
  Cover.leaf q (fun m hm => hp.sound m (subsumes_sound h hm))

theorem cover_mono {A B : Nat} {p : PartialMachine} (h : A ≤ B)
    (hp : Cover (WeightedBound A) p) : Cover (WeightedBound B) p :=
  Cover.leaf p (fun m hm k d hk hd => Nat.le_trans (hp.sound m hm k d hk hd) h)

/-- A checked parent list can discharge both exact rows and descendants;
    no global roster IDs or cardinality assumptions are used. -/
def hit (ps : List PartialMachine) (q : PartialMachine) : Bool :=
  ps.any (fun p => subsumes p q)

def residual (ps : List PartialMachine) : List PartialMachine :=
  remainingTables.filter (fun q => !hit ps q)

theorem reinsert {good : Machine → Prop} (ps : List PartialMachine)
    (hp : ∀ p ∈ ps, Cover good p)
    (hr : ∀ q ∈ residual ps, Cover good q) :
    ∀ q ∈ remainingTables, Cover good q := by
  intro q hq
  cases he : hit ps q with
  | false => exact hr q (List.mem_filter.mpr ⟨hq, by simp [he]⟩)
  | true =>
    obtain ⟨p, hp', hsub⟩ := List.any_eq_true.mp he
    exact cover_restrict hsub (hp p hp')

theorem raw139_cover_from_portfolio (B : Nat) (hb : 59 ≤ B)
    (ps : List PartialMachine)
    (hp : ∀ p ∈ ps, Cover (WeightedBound B) p)
    (hr : ∀ q ∈ residual ps, Cover (WeightedBound B) q)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound B) (child r.1 r.2))
    (hrc : Cover (WeightedBound B) (leaf rowRC) → Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) → Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) : Cover (WeightedBound B) p0 :=
  raw139_cover B hb ha (reinsert ps hp hr) hrc hre hf

def e0OneRF : PartialMachine := leaf (2, ⟨true,true,5⟩)
def f1ZeroLD : PartialMachine := leaf (5, ⟨false,false,3⟩)
def e0Eight : List PartialMachine := e0OneRF :: acceptedSixPlusZeroRC
def portfolioNine : List PartialMachine := f1ZeroLD :: e0Eight
def prospectiveTen : List PartialMachine := e0ZeroLF :: portfolioNine

theorem oneRF_occurs_once : (remainingTables.filter (fun p => sameTable p e0OneRF)).length = 1 := by decide
theorem f1ZeroLD_occurs_once : (remainingTables.filter (fun p => sameTable p f1ZeroLD)).length = 1 := by decide
theorem residual_e0Eight_count : (residual e0Eight).length = 59 := by decide
theorem residual_portfolioNine_count : (residual portfolioNine).length = 58 := by decide
theorem residual_prospectiveTen_count : (residual prospectiveTen).length = 57 := by decide

/-- The finite difference is exactly the requested nine rows, so no unintended
    descendant pruning is hidden by a count. -/
theorem portfolioNine_exact : remainingTables.all (fun q =>
    hit portfolioNine q == matchesAny q portfolioNine) = true := by decide

#print axioms subsumes_sound
#print axioms cover_mono
#print axioms raw139_cover_from_portfolio
#print axioms oneRF_occurs_once
#print axioms f1ZeroLD_occurs_once
#print axioms residual_e0Eight_count
#print axioms residual_portfolioNine_count
#print axioms residual_prospectiveTen_count
#print axioms portfolioNine_exact
end BB6.Agent14Raw139CoverPortfolio
