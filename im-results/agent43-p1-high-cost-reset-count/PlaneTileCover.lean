import WordPlane
import PlaneReverse

namespace BB6.Agent43WordPlane
open BB6.Agent43Matrix64 (Rows)
open BB6.Agent9PlaneReverse (first residue first_identity interval_index_iff plane_membership_iff)

/-- A certificate may use a superset of the true lanes. Each selected-word
    interval has exactly the same start and length as plane_reverse.cpp. -/
def PlaneChecks (M Y q F : Nat) (w : Nat → Nat) (ends : Rows) (lane : Nat → Rows) : Prop :=
  ∀ B, B<M →
    let z0 := first M Y (w B)
    let c0 := residue M Y (w B)
    let count := min ((q-1-c0)/M+1) (F-z0)
    c0<q → z0<F → ∀ b, 64*b<count → TileOK ends (lane c0) z0 count b

/-- A plane cover needs only word inclusions, with all quotient and range
    computations confined to the small arithmetic coordinates. -/
theorem plane_checks_cover (M Y q F c : Nat) (w : Nat → Nat) (ends : Rows) (lane : Nat → Rows)
    (hM : 0<M) (hY : Y<M) (he : Words64 ends)
    (hchecks : PlaneChecks M Y q F w ends lane)
    (h : ∃ B<M, ∃ t, first M Y (w B)+t<F ∧ WordMem ends (first M Y (w B)+t) ∧
      c=residue M Y (w B)+M*t ∧ c<q) : PlaneMem M lane c := by
  obtain ⟨B,hB,t,hz,hbit,hc,hq⟩ := h
  let z0 := first M Y (w B)
  let c0 := residue M Y (w B)
  let count := min ((q-1-c0)/M+1) (F-z0)
  change c=c0+M*t at hc
  have hc0 : c0<q := by omega
  have hz0 : z0<F := by change z0+t<F at hz; omega
  have hr : c0<M := (first_identity M Y (w B) hM hY).2
  have ht : t<count := by
    apply Nat.lt_min.mpr
    exact ⟨(interval_index_iff M c0 q t hM hc0).1 (by omega),by change z0+t<F at hz; omega⟩
  have hcheck : ∀ b, 64*b<count → TileOK ends (lane c0) z0 count b := hchecks B hB hc0 hz0
  have hb := tile_cover ends (lane c0) z0 count he hcheck t ht hbit
  unfold PlaneMem WordMem
  rw [hc,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr,Nat.add_mul_div_left _ _ hM,Nat.div_eq_of_lt hr,Nat.zero_add]
  exact hb

/-- The ordinary output may also be a superset. Only its in-range low bits
    are required to contain the exact flattened lanes. -/
def OutputChecks (S q : Nat) (lane : Nat → Rows) (starts : Rows) : Prop :=
  ∀ b, 64*b<q →
    let X := flatten S lane b &&& (2^(min 64 (q-64*b))-1)
    X &&& starts b=X

theorem output_checks_cover (S q c : Nat) (lane : Nat → Rows) (starts : Rows)
    (hS : 0<S) (hc : c<q) (hcheck : OutputChecks S q lane starts)
    (hm : PlaneMem (64*S) lane c) : WordMem starts c := by
  have hbit := (flatten_bit S c lane hS).2 hm
  change (flatten S lane (c/64)).testBit (c%64)=true at hbit
  have hdecomp := Nat.div_add_mod c 64
  have hj : c%64<64 := Nat.mod_lt _ (by decide)
  have h := hcheck (c/64) (by omega)
  have hlim : c%64<min 64 (q-64*(c/64)) := by omega
  have he := congrArg (fun x : Nat => x.testBit (c%64)) h
  rw [Nat.testBit_and,Nat.testBit_and,Nat.testBit_two_pow_sub_one] at he
  simp only [hbit,decide_eq_true hlim,Bool.true_and] at he
  exact he

/-- Packed interval checks plus local transposes certify the complete
    reverse image without evaluating any word larger than 128 bits. -/
theorem packed_plane_cover (S Y q F c : Nat) (w : Nat → Nat) (ends starts : Rows)
    (lane : Nat → Rows) (hS : 0<S) (hY : Y<64*S) (he : Words64 ends)
    (hchecks : PlaneChecks (64*S) Y q F w ends lane)
    (houtput : OutputChecks S q lane starts)
    (h : ∃ B<64*S, ∃ z<F, WordMem ends z ∧ 64*S*z+Y=w B+c ∧ c<q) : WordMem starts c := by
  have hM : 0<64*S := Nat.mul_pos (by decide) hS
  have hp := (plane_membership_iff (64*S) Y q F c w (WordMem ends) hM hY).1 h
  have hm := plane_checks_cover (64*S) Y q F c w ends lane hM hY he hchecks hp
  obtain ⟨B,hB,z,hz,ht,hs,hc⟩ := h
  exact output_checks_cover S q c lane starts hS hc houtput hm

#print axioms plane_checks_cover
#print axioms output_checks_cover
#print axioms packed_plane_cover
end BB6.Agent43WordPlane
