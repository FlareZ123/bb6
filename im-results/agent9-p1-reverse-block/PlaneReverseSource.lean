import PlaneReverse
import ReverseBlock
import WeightedDigitGap

namespace BB6.Agent9PlaneReverse
open BB6.Agent45ReverseBlock (Walk digits corr eq_of_walk walk_of_eq walk_bound)
open BB6.Agent45WeightedDigitGap (digitWeight corr_le_mul)

def wordWeight (q k B : Nat) : Nat := q*B+digitWeight k B

theorem wordWeight_add_corr (q k B : Nat) (hB : B<2^k) :
    wordWeight q k B+corr k B=(q+k)*B := by
  have h := corr_le_mul k B hB
  unfold wordWeight digitWeight
  rw [Nat.add_mul]
  omega

theorem target_lt (ys : List Nat) (hys : ∀ y∈ys, y≤1) :
    digits ys<2^ys.length := by
  induction ys with
  | nil => simp [digits]
  | cons y ys ih =>
    have h := hys y (by simp)
    have ht := ih (fun v hv => hys v (by simp [hv]))
    simp only [digits,List.length_cons,Nat.pow_succ]
    omega

theorem terminal_lt {F z c : Nat} {ys : List Nat} (h : Walk F z ys c) :
    z<F := by
  induction h with
  | nil hz => exact hz
  | step ys c y b r h hy hb hc hr he ih => exact ih

/-- Exact broad reverse image through the original `ReverseBlock.Walk`.
    The output lane is indexed by the residue of the selected-word weight;
    the lane bit index is the offset inside its terminal interval. -/
theorem walk_iff_planes (q c : Nat) (ys : List Nat) (ends : Nat → Prop)
    (hys : ∀ y∈ys, y≤1) :
    (∃ z, ends z ∧ Walk (q+ys.length) z ys c) ↔
    ∃ B<2^ys.length, ∃ t,
      first (2^ys.length) (digits ys) (wordWeight q ys.length B)+t<q+ys.length ∧
      ends (first (2^ys.length) (digits ys) (wordWeight q ys.length B)+t) ∧
      c=residue (2^ys.length) (digits ys) (wordWeight q ys.length B)+2^ys.length*t ∧ c<q := by
  rw [←plane_membership_iff (2^ys.length) (digits ys) q (q+ys.length) c
    (wordWeight q ys.length) ends (Nat.two_pow_pos _) (target_lt ys hys)]
  constructor
  · rintro ⟨z,hz,hw⟩
    obtain ⟨B,hB,he⟩ := eq_of_walk hw
    have hc := walk_bound hw
    rw [Nat.add_sub_cancel] at hc
    have hW := wordWeight_add_corr q ys.length B hB
    exact ⟨B,hB,z,terminal_lt hw,hz,by omega,hc⟩
  · rintro ⟨B,hB,z,hz,ht,he,hc⟩
    have hW := wordWeight_add_corr q ys.length B hB
    refine ⟨z,ht,walk_of_eq _ _ _ _ _ hys hB ?_ ?_⟩
    · simpa using hc
    · omega

#print axioms wordWeight_add_corr
#print axioms target_lt
#print axioms walk_iff_planes
end BB6.Agent9PlaneReverse
