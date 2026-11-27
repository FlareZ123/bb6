import Std

namespace PeriodicGrid

def Good (q r : Nat) : Prop :=
  0 < r ∧ r < q ∧ (12 * r < q ∨ (q < 4 * r ∧ 3 * r < q))

def rank (q r : Nat) : Nat :=
  if 12*r < q then r-1 else (q-1)/12 + r - (q/4+1)

private theorem floor_bound (q : Nat) :
    (q-1)/12 + (q-1)/3 - q/4 ≤ (q-1)/6 := by
  have hrem : q % 12 = 0 ∨ q % 12 = 1 ∨ q % 12 = 2 ∨
      q % 12 = 3 ∨ q % 12 = 4 ∨ q % 12 = 5 ∨
      q % 12 = 6 ∨ q % 12 = 7 ∨ q % 12 = 8 ∨
      q % 12 = 9 ∨ q % 12 = 10 ∨ q % 12 = 11 := by omega
  rcases hrem with h | h | h | h | h | h | h | h | h | h | h | h <;> omega

private theorem in_bound (q r : Nat) (h : Good q r) :
    rank q r < (q-1)/6 := by
  rcases h with ⟨hr0, hrq, he | ⟨hleft, hright⟩⟩
  · simp [rank, he]
    have hbd := floor_bound q
    omega
  · have hnot : ¬ 12*r < q := by omega
    simp [rank, hnot]
    have hbd := floor_bound q
    omega

private theorem rank_inj (q r s : Nat) (hr : Good q r) (hs : Good q s)
    (he : rank q r = rank q s) : r = s := by
  rcases hr with ⟨hr0, hrq, he0⟩
  rcases hs with ⟨hs0, hsq, hs0'⟩
  unfold rank at he
  split at he <;> split at he <;> omega

private theorem rank_map_nodup (q : Nat) (l : List Nat) (hn : l.Nodup)
    (hg : ∀ r, r ∈ l → Good q r) : (l.map (rank q)).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hxnot, hxsnd⟩ := List.nodup_cons.mp hn
    have hx : Good q x := hg x (by simp)
    have hxs : ∀ r, r ∈ xs → Good q r := by
      intro r hr
      exact hg r (by simp [hr])
    simp only [List.map_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hmem
      have hsame : y = x := rank_inj q y x (hxs y hy) hx hxy
      exact hxnot (hsame ▸ hy)
    · exact ih hxsnd hxs

/-- Any positive integer q (odd or even) admits at most floor((q-1)/6)
    distinct fractions r/q in (0,1/12) union (1/4,1/3). -/
theorem grid_packing_all (q : Nat)
    (l : List Nat) (hn : l.Nodup) (hg : ∀ r, r ∈ l → Good q r) :
    l.length ≤ (q-1)/6 := by
  let n := (q-1)/6
  have hsub : (l.map (rank q)) ⊆ List.range n := by
    intro z hz
    obtain ⟨r, hr, hre⟩ := List.mem_map.mp hz
    have hb := in_bound q r (hg r hr)
    have he : z < n := by simpa [n, hre] using hb
    exact List.mem_range.mpr he
  have hlen := List.Nodup.length_le_of_subset (rank_map_nodup q l hn hg) hsub
  simpa only [List.length_map, List.length_range] using hlen

/-- Backward-compatible odd-denominator specialization. -/
theorem odd_grid_packing (q : Nat) (_hqodd : q % 2 = 1)
    (l : List Nat) (hn : l.Nodup) (hg : ∀ r, r ∈ l → Good q r) :
    l.length ≤ (q-1)/6 := grid_packing_all q l hn hg

/-- Direct denominator-free contradiction for the proposed periodic
    F-run path. The model bridge must supply the distinct rotation list. -/
theorem no_periodic_rank_budget_direct (K t : Nat)
    (hbudget : K ≤ 6*t) (htpos : 0 < t)
    (rotations : List Nat) (hl : rotations.length = t)
    (hn : rotations.Nodup)
    (hg : ∀ r, r ∈ rotations → Good K r) : False := by
  have hpack := grid_packing_all K rotations hn hg
  omega

/-- Retain the earlier reduced-denominator certificate interface. -/
theorem no_periodic_rank_budget (q K t : Nat)
    (_hqodd : q % 2 = 1) (hKpos : 0 < K)
    (hqdiv : q ∣ K) (hbudget : K ≤ 6*t)
    (rotations : List Nat) (hl : rotations.length = t)
    (hn : rotations.Nodup)
    (hg : ∀ r, r ∈ rotations → Good q r) : False := by
  have hpack := grid_packing_all q rotations hn hg
  have hqle : q ≤ K := Nat.le_of_dvd hKpos hqdiv
  omega

#print axioms PeriodicGrid.grid_packing_all
#print axioms PeriodicGrid.odd_grid_packing
#print axioms PeriodicGrid.no_periodic_rank_budget_direct
#print axioms PeriodicGrid.no_periodic_rank_budget
end PeriodicGrid
