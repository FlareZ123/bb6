import PeriodMarker
import PeriodWordBounds

namespace PeriodPrimitive
open PeriodWord

def Primitive (w : List Nat) : Prop :=
  ∀ r, 0<r → r<cost w → (2^r*weight w)%(2^(cost w)-1) ≠ weight w

theorem positive_depth_cost (w : List Nat)
    (hp : ∃ t ∈ w, 0<t) : 1<cost w := by
  induction w with
  | nil =>
      obtain ⟨t, ht, _⟩ := hp
      cases ht
  | cons t ts ih =>
      obtain ⟨u,hu,hu0⟩ := hp
      rcases List.mem_cons.mp hu with h | h
      · have ht : 0<t := by simpa [h] using hu0
        simp only [cost]
        omega
      · have hts := ih ⟨u,h,hu0⟩
        simp only [cost]
        omega

theorem positive_marker (w : List Nat)
    (hp : ∃ t ∈ w, 0<t) :
    0<weight w ∧ weight w<2^(cost w)-1 := by
  constructor
  · cases w with
    | nil =>
      obtain ⟨t,ht,_⟩ := hp
      cases ht
    | cons t ts =>
      simp only [weight]
      have ht : 0<2^t := Nat.pow_pos (by decide)
      omega
  · have hb := nonzero_word_marker_lt w hp
    omega

/-- For every positive-depth finite word with no shorter cyclic binary
    period, exact infinite repetition is impossible at any scalar node.
    The theorem is uniform in word length and its maximum depth. -/
theorem no_infinite_primitive_ray (L : Nat) (w : List Nat)
    (hp : ∃ t ∈ w, 0<t) (hprim : Primitive w)
    (m z : Nat → Nat)
    (hr : ∀ n, Run L w (m n) (z n) (m (n+1)) (z (n+1))) : False := by
  let S := cost w
  let H := weight w
  let B := 2^S-1
  have hS : 1<S := positive_depth_cost w hp
  have hH : 0<H ∧ H<B := positive_marker w hp
  have hB : 0<B := by
    have hh : 2 < 2^S := by
      have h22 : 2^2≤2^S := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    dsimp [B]
    omega
  obtain ⟨d,hd⟩ := periodic_run_integral_slope L w (by omega) m z hr
  have hcast : (((2^S-1):Nat):Int) = ((2^S:Nat):Int)-1 := by
    have hh : 1≤2^S := Nat.one_le_pow S 2 (by decide)
    omega
  have hIntdiv : ((B:Nat):Int) ∣ ((H*S:Nat):Int) := by
    refine ⟨d, ?_⟩
    have hd' : ((2^S:Nat):Int)-1 = ((2:Nat)^(cost w):Int)-1 := by rfl
    dsimp [S, H, B] at *
    simp only [Int.natCast_mul] at *
    rw [hcast]
    simpa using hd.symm
  have hNatdiv : B ∣ H*S := (Int.natCast_dvd_natCast).mp hIntdiv
  obtain ⟨Q,hq⟩ := hNatdiv
  have hQpos : 0<Q := by
    have hh : 0<H*S := Nat.mul_pos hH.1 (by omega)
    by_cases hzero : Q=0
    · simp [hzero] at hq
      omega
    · omega
  have hQlt : Q<S := by
    have hbq : B*Q<B*S := by
      calc
        B*Q = H*S := hq.symm
        _ = S*H := by ac_rfl
        _ < S*B := Nat.mul_lt_mul_of_pos_left hH.2 (by omega)
        _ = B*S := by ac_rfl
    exact (Nat.mul_lt_mul_left hB).mp hbq
  have hratio_nat : (2^S-1)*Q=S*H := by
    simpa only [B, Nat.mul_comm] using hq.symm
  obtain ⟨r,hrpos,hrlt,hrot⟩ :=
    PeriodMarker.shorter_marker_rotation S H Q hS hH
      ⟨hQpos,hQlt⟩ hratio_nat
  exact hprim r hrpos hrlt hrot

#print axioms no_infinite_primitive_ray
end PeriodPrimitive
