import Lean

namespace BB6.Agent49Box
abbrev Box (S V : Type) := S → List V
abbrev Cube (S V : Type) := List (S × V)

variable {S V : Type} [DecidableEq S] [DecidableEq V]

def Fits (b : Box S V) (m : S → V) : Prop :=
  ∀ s, m s ∈ b s

def Matches (c : Cube S V) (m : S → V) : Prop :=
  ∀ x ∈ c, m x.1 = x.2

def restrict (b : Box S V) (s : S) (f : V → Bool) : Box S V :=
  fun k => if k = s then (b k).filter f else b k

theorem fits_restrict (b : Box S V) (s : S) (f : V → Bool) (m : S → V) :
    Fits (restrict b s f) m ↔ Fits b m ∧ f (m s) = true := by
  constructor
  · intro h
    have hs := h s
    simp [restrict] at hs
    refine ⟨?_, hs.2⟩
    intro k
    by_cases hk : k = s
    · subst k
      exact hs.1
    · simpa [restrict, hk] using h k
  · rintro ⟨h, hf⟩ k
    by_cases hk : k = s
    · subst k
      simpa [restrict, hf] using h s
    · simpa [restrict, hk] using h k

def reject (b : Box S V) (x : S × V) : Box S V :=
  restrict b x.1 (fun v => decide (v ≠ x.2))

def accept (b : Box S V) (x : S × V) : Box S V :=
  restrict b x.1 (fun v => decide (v = x.2))

theorem fits_reject (b : Box S V) (x : S × V) (m : S → V) :
    Fits (reject b x) m ↔ Fits b m ∧ m x.1 ≠ x.2 := by
  simp [reject, fits_restrict]

theorem fits_accept (b : Box S V) (x : S × V) (m : S → V) :
    Fits (accept b x) m ↔ Fits b m ∧ m x.1 = x.2 := by
  simp [accept, fits_restrict]

/-- Disjoint first-mismatch pieces. Empty boxes are removed by subtract. -/
def pieces (b : Box S V) : Cube S V → List (Box S V)
  | [] => []
  | x :: xs => reject b x :: pieces (accept b x) xs

theorem pieces_exact (b : Box S V) (c : Cube S V) (m : S → V) :
    (∃ r ∈ pieces b c, Fits r m) ↔ Fits b m ∧ ¬ Matches c m := by
  induction c generalizing b with
  | nil => simp [pieces, Matches]
  | cons x xs ih =>
    simp only [pieces, List.mem_cons, exists_eq_or_imp, fits_reject, ih,
      fits_accept, Matches, List.mem_cons]
    constructor
    · rintro (⟨hb, hne⟩ | ⟨⟨hb, he⟩, hn⟩)
      · exact ⟨hb, fun h => hne (h x (Or.inl rfl))⟩
      · exact ⟨hb, fun h => hn (fun y hy => h y (Or.inr hy))⟩
    · rintro ⟨hb, hn⟩
      by_cases he : m x.1 = x.2
      · right
        refine ⟨⟨hb, he⟩, ?_⟩
        intro hx
        apply hn
        intro y hy
        rcases hy with rfl | hy
        · exact he
        · exact hx y hy
      · exact Or.inl ⟨hb, he⟩

def possible (b : Box S V) (c : Cube S V) : Bool :=
  c.all (fun x => decide (x.2 ∈ b x.1))

def live (slots : List S) (b : Box S V) : Bool :=
  slots.all (fun s => !(b s).isEmpty)

theorem fits_live (slots : List S) (b : Box S V) (m : S → V)
    (h : Fits b m) : live slots b = true := by
  apply List.all_eq_true.mpr
  intro s _
  have hs := h s
  cases e : b s with
  | nil => simp [e] at hs
  | cons v vs => simp [e]

theorem possible_of_match (b : Box S V) (c : Cube S V) (m : S → V)
    (hb : Fits b m) (hc : Matches c m) : possible b c = true := by
  apply List.all_eq_true.mpr
  intro x hx
  exact decide_eq_true (hc x hx ▸ hb x.1)

/-- If the cylinder cannot meet a box, preserve the box unchanged. This
    shortcut prevents artificial fragmentation by irrelevant certificates. -/
def subtract (slots : List S) (b : Box S V) (c : Cube S V) : List (Box S V) :=
  if possible b c then (pieces b c).filter (live slots) else [b]

theorem subtract_exact (slots : List S) (b : Box S V) (c : Cube S V)
    (m : S → V) :
    (∃ r ∈ subtract slots b c, Fits r m) ↔ Fits b m ∧ ¬ Matches c m := by
  unfold subtract
  cases hp : possible b c with
  | false =>
    simp only [Bool.false_eq_true, ite_false, List.mem_singleton, exists_eq_left]
    exact ⟨fun hb => ⟨hb, fun hc => by
      rw [possible_of_match b c m hb hc] at hp
      contradiction⟩, fun h => h.1⟩
  | true =>
    simp only [ite_true, List.mem_filter]
    rw [← pieces_exact b c m]
    constructor
    · rintro ⟨r, ⟨hr, _⟩, hm⟩
      exact ⟨r, hr, hm⟩
    · rintro ⟨r, hr, hm⟩
      exact ⟨r, ⟨hr, fits_live slots r m hm⟩, hm⟩

def subtractMany (slots : List S) (bs : List (Box S V)) :
    List (Cube S V) → List (Box S V)
  | [] => bs
  | c :: cs => subtractMany slots (bs.flatMap fun b => subtract slots b c) cs

theorem subtractMany_exact (slots : List S) (bs : List (Box S V))
    (cs : List (Cube S V)) (m : S → V) :
    (∃ r ∈ subtractMany slots bs cs, Fits r m) ↔
      (∃ b ∈ bs, Fits b m) ∧ ∀ c ∈ cs, ¬ Matches c m := by
  induction cs generalizing bs with
  | nil => simp [subtractMany]
  | cons c cs ih =>
    rw [subtractMany, ih]
    constructor
    · rintro ⟨⟨r, hr, hm⟩, htail⟩
      obtain ⟨b, hb, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨hfit, hnot⟩ := (subtract_exact slots b c m).mp ⟨r, hr, hm⟩
      refine ⟨⟨b, hb, hfit⟩, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hnot
      · exact htail d hd
    · rintro ⟨⟨b, hb, hfit⟩, hall⟩
      obtain ⟨r, hr, hm⟩ := (subtract_exact slots b c m).mpr
        ⟨hfit, hall c (List.mem_cons_self ..)⟩
      exact ⟨⟨r, List.mem_flatMap.mpr ⟨b, hb, hr⟩, hm⟩,
        fun d hd => hall d (List.mem_cons_of_mem _ hd)⟩

/-- The residual obligations may be proved individually, at any common
    predicate P, without enumerating the single-valued completion tables. -/
theorem consume (slots : List S) (b : Box S V) (cs : List (Cube S V))
    (P : (S → V) → Prop)
    (closed : ∀ c ∈ cs, ∀ m, Matches c m → P m)
    (openCover : ∀ r ∈ subtractMany slots [b] cs, ∀ m, Fits r m → P m) :
    ∀ m, Fits b m → P m := by
  intro m hm
  classical
  by_cases hc : ∃ c ∈ cs, Matches c m
  · obtain ⟨c, hmem, hmatch⟩ := hc
    exact closed c hmem m hmatch
  · have hnone : ∀ c ∈ cs, ¬ Matches c m :=
      fun c hmem hmatch => hc ⟨c, hmem, hmatch⟩
    obtain ⟨r, hr, hfit⟩ := (subtractMany_exact slots [b] cs m).mpr
      ⟨⟨b, by simp, hm⟩, hnone⟩
    exact openCover r hr m hfit

def Disjoint (a b : Box S V) : Prop :=
  ∀ m : S → V, ¬ (Fits a m ∧ Fits b m)

theorem pieces_disjoint (b : Box S V) (c : Cube S V) :
    (pieces b c).Pairwise Disjoint := by
  induction c generalizing b with
  | nil => simp [pieces]
  | cons x xs ih =>
    rw [pieces, List.pairwise_cons]
    refine ⟨?_, ih _⟩
    intro r hr m h
    have hn := (fits_reject b x m).mp h.1
    have he := (pieces_exact (accept b x) xs m).mp ⟨r, hr, h.2⟩
    exact hn.2 ((fits_accept b x m).mp he.1).2

theorem subtract_disjoint (slots : List S) (b : Box S V) (c : Cube S V) :
    (subtract slots b c).Pairwise Disjoint := by
  unfold subtract
  split
  · exact (pieces_disjoint b c).filter _
  · simp

theorem subtractMany_disjoint (slots : List S) (bs : List (Box S V))
    (cs : List (Cube S V)) (hd : bs.Pairwise Disjoint) :
    (subtractMany slots bs cs).Pairwise Disjoint := by
  induction cs generalizing bs with
  | nil => exact hd
  | cons c cs ih =>
    apply ih
    apply List.pairwise_flatMap.mpr
    refine ⟨fun b _ => subtract_disjoint slots b c, ?_⟩
    apply hd.imp
    intro a b hab r hr t ht m hm
    exact hab m
      ⟨((subtract_exact slots a c m).mp ⟨r, hr, hm.1⟩).1,
       ((subtract_exact slots b c m).mp ⟨t, ht, hm.2⟩).1⟩

#print axioms subtractMany_disjoint
#print axioms subtractMany_exact
#print axioms consume

end BB6.Agent49Box
