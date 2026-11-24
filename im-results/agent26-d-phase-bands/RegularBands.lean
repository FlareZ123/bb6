import GrowthBands
import DRegular

namespace BB6.Agent26.GrowthBands

/-- A regular section has suffix (01)^q 1^b, with the first zero included. -/
def measure (s : DRegular.L) : Section := ⟨s.a,2*s.q+s.b⟩

def seed (a : Fin 4) : DRegular.L := match a with
  | 0 => ⟨5,0,0⟩
  | 1 => ⟨9,0,0⟩
  | 2 => ⟨15,0,0⟩
  | 3 => ⟨39,0,0⟩

def shift (a : Fin 4) : Nat := if a=3 then 9 else 10

def anchor (a : Fin 4) : DRegular.L := match a with
  | 0 => ⟨123501,1,5⟩
  | 1 => ⟨196699,0,0⟩
  | 2 => ⟨276715,0,0⟩
  | 3 => ⟨277451,0,0⟩

theorem anchor_run : ∀ a, DRegular.run (shift a) (seed a) = some (anchor a) := by decide

theorem anchor_measure : ∀ a, measure (anchor a) = base a := by decide

theorem regular_edge (s t : DRegular.L) (h : DRegular.next s = some t)
    (hn : 5 ≤ s.a) : Edge (measure s) (measure t) := by
  simp only [DRegular.next] at h
  simp only [measure]
  split at h <;> rename_i e
  · split at h <;> rename_i f
    · cases h; constructor <;> simp_all <;> omega
    · split at h <;> rename_i g <;> cases h <;> constructor <;> simp_all <;> omega
  · split at h <;> rename_i f
    · split at h <;> rename_i g
      · cases h; constructor <;> simp_all <;> omega
      · split at h <;> rename_i j
        · cases h; constructor <;> simp_all <;> omega
        · split at h <;> rename_i k <;> cases h <;> constructor <;> simp_all <;> omega
    · split at h <;> rename_i g
      · cases h; constructor <;> simp_all <;> omega
      · split at h <;> rename_i j
        · cases h; constructor <;> simp_all <;> omega
        · split at h <;> rename_i k
          · contradiction
          · split at h <;> rename_i l <;> cases h <;> constructor <;> simp_all <;> omega

theorem regular_path (n : Nat) (s t : DRegular.L) (hn : 5 ≤ s.a)
    (h : DRegular.run n s = some t) : Path n (measure s) (measure t) := by
  induction n generalizing s with
  | zero => simp [DRegular.run] at h; subst t; exact Path.nil _
  | succ n ih =>
    cases hs : DRegular.next s with
    | none => simp [DRegular.run,hs] at h
    | some u =>
      have e := regular_edge s u hs hn
      exact Path.cons e (ih u (edge_live e) (by simpa [DRegular.run,hs] using h))

/-- All finite surviving regular paths, with exact imported arithmetic seeds. -/
theorem regular_disjoint {a b : Fin 4} {i j : Nat} {x y : DRegular.L}
    (p : DRegular.run i (anchor a) = some x)
    (q : DRegular.run j (anchor b) = some y)
    (h : a≠b ∨ i≠j) : x.a≠y.a := by
  have ha : ∀ a, 5 ≤ (anchor a).a := by decide
  have p' := regular_path i (anchor a) x (ha a) p
  have q' := regular_path j (anchor b) y (ha b) q
  rw [anchor_measure] at p' q'
  exact disjoint_paths p' q' h

def early : List DRegular.L := (List.finRange 4).flatMap fun a =>
  (List.range (shift a)).map fun i => (DRegular.run i (seed a)).getD ⟨0,0,0⟩

theorem early_nodup : early.Nodup := by decide

theorem early_survives : ∀ (a : Fin 4) (i : Fin (shift a)),
    (DRegular.run i.val (seed a)).isSome = true := by decide

theorem early_before_base : ∀ (a b : Fin 4) (i : Fin (shift a)),
    ((DRegular.run i.val (seed a)).getD ⟨0,0,0⟩).a < (anchor b).a := by decide

#print axioms early_nodup
#print axioms early_survives
#print axioms early_before_base
#print axioms anchor_run
#print axioms regular_edge
#print axioms regular_disjoint
end BB6.Agent26.GrowthBands
