import Lean

namespace BB6.RectCover

variable {S V : Type} [DecidableEq V]
abbrev Box (S V : Type) := S → List V

def Fits (r : Box S V) (m : S → V) : Prop := ∀ s, m s ∈ r s

/-- A subrectangle is certified by pointwise inclusion, rather than
    equality of its product-domain representation. -/
def subsetB (slots : List S) (r c : Box S V) : Bool :=
  slots.all fun s => (r s).all fun v => decide (v ∈ c s)

theorem subset_sound (slots : List S) (complete : ∀ s, s ∈ slots)
    (r c : Box S V) (h : subsetB slots r c = true)
    (m : S → V) (hm : Fits r m) : Fits c m := by
  intro s
  have hs := List.all_eq_true.mp h s (complete s)
  exact of_decide_eq_true (List.all_eq_true.mp hs (m s) (hm s))

def covered (slots : List S) (closed : List (Box S V)) (r : Box S V) : Bool :=
  closed.any fun c => subsetB slots r c

/-- Sound for any partition refinement, any predicate and any list of
    already bounded boxes. The false-match complement is explicit. -/
theorem consume (slots : List S) (complete : ∀ s, s ∈ slots)
    (closed remaining : List (Box S V)) (P : (S → V) → Prop)
    (hc : ∀ c ∈ closed, ∀ m, Fits c m → P m)
    (hr : ∀ r ∈ remaining, covered slots closed r = false → ∀ m, Fits r m → P m) :
    ∀ r ∈ remaining, ∀ m, Fits r m → P m := by
  intro r hmem m hm
  cases h : covered slots closed r with
  | false => exact hr r hmem h m hm
  | true =>
    obtain ⟨c, hmemc, hsub⟩ := List.any_eq_true.mp h
    exact hc c hmemc m (subset_sound slots complete r c hsub m hm)

#print axioms subset_sound
#print axioms consume
end BB6.RectCover
