import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Agent26.GrowthBands

structure Section where
  n : Nat
  tailLen : Nat
  deriving DecidableEq, Repr

def lower (c : Section) : Nat := 5*c.n-23
def upper (c : Section) : Nat := 5*(c.n+c.tailLen)+40

/-- Per-return sufficient inequalities. They allow arbitrary tail lengths. -/
structure Edge (c d : Section) : Prop where
  live : 5 ≤ c.n
  lowerBound : 8*c.n ≤ 3*d.n+23
  upperBound : 3*(d.n+d.tailLen) ≤ 8*(c.n+c.tailLen)+40

/-- Bounds for the B row, allowing arbitrary residual tape length. -/
theorem B_edge (k L n' L' : Nat) (hstart : 5 ≤ 3*k+2)
    (hlo : 8*k+9 ≤ n') (hmass : n'+L' ≤ 8*k+9+L) :
    Edge ⟨3*k+2,L⟩ ⟨n',L'⟩ := by
  constructor <;> simp_all <;> omega

/-- A row: x pair tokens, y triple tokens, z consumed physical cells,
    t residual input length. Implicit final zeros need not be counted. -/
theorem A_edge (k L x y z t n' L' : Nat) (hstart : 5 ≤ 3*k+3)
    (hconsume : x+3*y ≤ z) (hpartition : z+t ≤ L)
    (hlo : 8*k+7+2*x+8*y ≤ n')
    (hmass : n'+L' ≤ 8*k+11+2*x+8*y+t+9) :
    Edge ⟨3*k+3,L⟩ ⟨n',L'⟩ := by
  constructor <;> simp_all <;> omega

/-- E row: residual suffix length increases by at most ten. -/
theorem E_edge (k L n' L' : Nat) (hstart : 5 ≤ 3*k+4)
    (hlo : 8*k+3 ≤ n') (hmass : n'+L' ≤ 8*k+9+L+10) :
    Edge ⟨3*k+4,L⟩ ⟨n',L'⟩ := by
  constructor <;> simp_all <;> omega

theorem edge_live {c d : Section} (e : Edge c d) : 5 ≤ d.n := by
  have := e.live
  have := e.lowerBound
  omega

theorem edge_increases {c d : Section} (e : Edge c d) : c.n < d.n := by
  have := e.live
  have := e.lowerBound
  omega

theorem lower_step {c d : Section} (e : Edge c d) : 8*lower c ≤ 3*lower d := by
  have := e.live
  have := edge_live e
  have := e.lowerBound
  unfold lower
  omega

theorem upper_step {c d : Section} (e : Edge c d) : 3*upper d ≤ 8*upper c := by
  have := e.upperBound
  unfold upper
  omega

theorem lower_le_n (c : Section) : lower c ≤ 5*c.n := by
  unfold lower; omega

theorem n_le_upper (c : Section) : 5*c.n ≤ upper c := by
  unfold upper; omega

inductive Path : Nat → Section → Section → Prop where
  | nil (c : Section) : Path 0 c c
  | cons {k : Nat} {c d e : Section} : Edge c d → Path k d e → Path (k+1) c e

theorem path_n_mono {k : Nat} {c d : Section} (p : Path k c d) : c.n ≤ d.n := by
  induction p with
  | nil => exact Nat.le_refl _
  | cons e _ ih => exact Nat.le_trans (Nat.le_of_lt (edge_increases e)) ih

theorem path_strict {k : Nat} {c d : Section} (p : Path (k+1) c d) : c.n < d.n := by
  cases p with
  | cons e p => exact Nat.lt_of_lt_of_le (edge_increases e) (path_n_mono p)

/-- Any two paths of the same length preserve a strict separation of their bands. -/
theorem sync_gap {k : Nat} {a b x y : Section}
    (p : Path k a x) (q : Path k b y) (gap : upper a < lower b) : upper x < lower y := by
  induction p generalizing b y with
  | nil a =>
    cases q
    exact gap
  | cons e p ih =>
    cases q with
    | cons f q =>
      apply ih q
      have := upper_step e
      have := lower_step f
      omega

theorem gap_n {a b : Section} (gap : upper a < lower b) : a.n < b.n := by
  have := n_le_upper a
  have := lower_le_n b
  omega

theorem sync_order {k : Nat} {a b x y : Section}
    (p : Path k a x) (q : Path k b y) (gap : upper a < lower b) : x.n < y.n :=
  gap_n (sync_gap p q gap)

/-- Split a path at an arbitrary prefix length. -/
theorem split_path {i j : Nat} {a z : Section} (p : Path (i+j) a z) :
    ∃ b, Path i a b ∧ Path j b z := by
  induction i generalizing a with
  | zero =>
    exact ⟨a, Path.nil a, by simpa using p⟩
  | succ i ih =>
    rw [show i+1+j=i+j+1 by omega] at p
    cases p with
    | cons e p =>
      obtain ⟨b, hb, hz⟩ := ih p
      exact ⟨b, Path.cons e hb, hz⟩

/-- Strict ordering even if the second path has more steps. No common
    continuation or assumption of eventual success is required. -/
theorem offset_order {i j : Nat} {a b x y : Section}
    (p : Path i a x) (q : Path j b y) (ij : i < j)
    (gap : 3*upper a < 8*lower b) : x.n < y.n := by
  obtain ⟨k, hk⟩ : ∃ k, j=1+i+k := ⟨j-i-1, by omega⟩
  subst j
  rw [show 1+i+k=(i+k)+1 by omega] at q
  cases q with
  | @cons _ _ d _ e q =>
    have hh := lower_step e
    have gap' : upper a < lower d := by omega
    obtain ⟨z,pz,qz⟩ := split_path q
    exact Nat.lt_of_lt_of_le (sync_order p pz gap') (path_n_mono qz)

-- Base sections at index 10 for seeds 5,9,15; index 9 for seed 39.
def base : Fin 4 → Section
  | 0 => ⟨123501,7⟩
  | 1 => ⟨196699,0⟩
  | 2 => ⟨276715,0⟩
  | 3 => ⟨277451,0⟩

-- Finite proof by cases, without native_decide.
theorem base_gap : ∀ a b : Fin 4, a < b → upper (base a) < lower (base b) := by decide

theorem base_cross : ∀ a b : Fin 4, 3*upper (base a) < 8*lower (base b) := by decide

/-- The four phase-shifted reachable paths are strictly ordered first by
    phase length, then by seed index. This is an all-time conditional
    statement, not a bounded trajectory scan. -/
theorem ordered_paths {a b : Fin 4} {i j : Nat} {x y : Section}
    (p : Path i (base a) x) (q : Path j (base b) y)
    (h : i<j ∨ (i=j ∧ a<b)) : x.n<y.n := by
  rcases h with hij | ⟨hij,hab⟩
  · exact offset_order p q hij (base_cross a b)
  · subst j
    exact sync_order p q (base_gap a b hab)

theorem disjoint_paths {a b : Fin 4} {i j : Nat} {x y : Section}
    (p : Path i (base a) x) (q : Path j (base b) y)
    (h : a≠b ∨ i≠j) : x.n≠y.n := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact Nat.ne_of_lt (ordered_paths p q (Or.inl hlt))
  · have hab : a≠b := by
      rcases h with h | h
      · exact h
      · exact False.elim (h heq)
    have hv : a.val ≠ b.val := fun hv => hab (Fin.ext hv)
    rcases Nat.lt_or_gt_of_ne hv with hlt | hgt
    · exact Nat.ne_of_lt (ordered_paths p q (Or.inr ⟨heq,hlt⟩))
    · exact Ne.symm (Nat.ne_of_lt (ordered_paths q p (Or.inr ⟨heq.symm,hgt⟩)))
  · exact Ne.symm (Nat.ne_of_lt (ordered_paths q p (Or.inl hgt)))

#print axioms A_edge
#print axioms B_edge
#print axioms E_edge
#print axioms base_gap
#print axioms base_cross
#print axioms ordered_paths
#print axioms disjoint_paths
end BB6.Agent26.GrowthBands
