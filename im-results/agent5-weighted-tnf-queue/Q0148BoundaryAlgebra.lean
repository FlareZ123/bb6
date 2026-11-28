import Q0148PackedBoundary

namespace BB6.Agent5Q0148BoundaryAlgebra
open BB6.Agent5Q0148BoundarySweep BB6.Agent5Q0148GapInvariant BB6.Agent5Q0148PackedBoundary

/-- All internal parameters represent gaps at least three. -/
theorem chain_positive (xs : List Nat) (h : chain xs) : ∀ u ∈ xs, 1 ≤ u := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simpa [chain] using h.1
    | cons y ys =>
      simp only [chain] at h
      intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · have hy := ih h.2 y (by simp)
        omega
      · exact ih h.2 u (by simpa only [List.mem_cons] using hu)

theorem valid_positive (g : GapState) (hg : valid g) : ∀ u ∈ g.xs, 1 ≤ u :=
  chain_positive g.xs hg.2.2.2.1

theorem valid_nonempty (g : GapState) (hg : valid g) : g.xs ≠ [] := by
  intro h
  have hl := hg.2.2.1
  have hr := hg.2.1
  rw [h] at hl
  simp at hl
  omega

def resetUs (g : GapState) : List Nat := g.xs.tail ++ [1]

def resetN (g : GapState) : Nat := first g.xs

theorem reset_blocks (g : GapState) (hg : valid g) :
    (resetUs g).reverse ++ [resetN g] = 1::g.xs.reverse := by
  have hn := valid_nonempty g hg
  cases hx : g.xs with
  | nil => exact False.elim (hn hx)
  | cons n ns => simp [resetUs,resetN,hx,first,List.reverse_append,List.reverse_cons]

theorem reset_future (g : GapState) :
    future g.b g.xs = (resetUs g).map (2*·) ++
      (if g.b=0 then [0] else [0,0,0]) := by
  by_cases hb : g.b=0 <;> simp [future,resetUs,hb,List.append_assoc]

/-- Convert old-gap marker parameters to exact interior chunk words.
An internal parameter u≥1 corresponds to old-gap parameter 2(u-1). -/
def priorChunks : List Nat → List LeftChunk
  | [] => []
  | n::ns => (.separatedMarker :: List.replicate (n+2) .alternating) ++ priorChunks ns

theorem priorChunks_append (xs ys : List Nat) :
    priorChunks (xs++ys) = priorChunks xs ++ priorChunks ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [priorChunks,ih,List.append_assoc]

theorem blocks_splice (xs : List Nat) (h : ∀ u ∈ xs, 1 ≤ u) :
    .separatedMarker :: blocks xs =
      priorChunks (xs.map (fun u => 2*(u-1))) ++ [.separatedMarker] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ u ∈ xs, 1 ≤ u := fun u hu => h u (by simp [hu])
    have he : 2*(x-1)+2 = 2*x := by omega
    simp [blocks,priorChunks,he,List.append_assoc,← ih ht]

theorem boundary_splice (g : GapState) (hg : valid g) :
    boundaryChunks g = List.replicate 2 .alternating ++
      priorChunks (g.xs.reverse.map (fun u => 2*(u-1))) ++
      [.separatedMarker] ++ List.replicate (2*g.b) .alternating := by
  have h : ∀ u ∈ g.xs.reverse, 1 ≤ u := by
    intro u hu
    exact valid_positive g hg u (by simpa using hu)
  change List.replicate 2 .alternating ++ ([.separatedMarker] ++ blocks g.xs.reverse) ++ List.replicate (2*g.b) .alternating = _
  have he : [.separatedMarker] ++ blocks g.xs.reverse =
      priorChunks (g.xs.reverse.map (fun u => 2*(u-1))) ++ [.separatedMarker] := blocks_splice _ h
  rw [he]
  simp [List.append_assoc]

theorem nonempty_snoc {α : Type} (xs : List α) (h : xs ≠ []) :
    ∃ ys x, xs = ys ++ [x] := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨[],x,rfl⟩
    | cons y ys =>
      obtain ⟨zs,w,hz⟩ := ih (by simp)
      exact ⟨x::zs,w,by simp [hz]⟩

/-- The train always has at least three markers, including the final zero. -/
theorem future_split (g : GapState) (hg : valid g) :
    ∃ n mid u, future g.b g.xs = n :: (mid ++ [u,0]) := by
  have hlen := (next_valid g hg).2.2.1
  have hr := (next_valid g hg).2.1
  have hl : 2 ≤ (next g).xs.length := by omega
  have he := future_eq g.b g.xs
  change future g.b g.xs = (next g).xs.map (fun u => 2*(u-1)) ++ [0] at he
  rw [he]
  cases hx : (next g).xs with
  | nil => simp [hx] at hl
  | cons x xs =>
    have hn : xs ≠ [] := by
      intro h; simp [hx,h] at hl
    obtain ⟨mid,u,hu⟩ := nonempty_snoc xs hn
    rw [hu]
    refine ⟨2*(x-1),mid.map (fun u => 2*(u-1)),2*(u-1),?_⟩
    simp [List.append_assoc]

#print axioms boundary_splice
#print axioms future_split
#print axioms reset_blocks
#print axioms reset_future
end BB6.Agent5Q0148BoundaryAlgebra
