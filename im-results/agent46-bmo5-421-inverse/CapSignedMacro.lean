import CapNegativeExit

namespace CapSieve

/-- Evaluate a compressed event using the given continuation. -/
def followEvent (limit : Nat) (cont : Nat → Nat → Bool)
    (e : Nat × Option (Nat × Nat)) : Bool :=
  if e.1>limit then false else
    match e.2 with
    | none => true
    | some (j,q) => cont j q

/-- Compress the complete negative run, with exactly the same answer at
    every finite band limit as the established band macro. -/
theorem band_halt_negative {limit k w : Nat} (hv : CapNegative.Valid k w) :
    bandHaltBy limit k (negQ k w)=
      followEvent limit (bandHaltBy limit) (CapNegative.event k w) := by
  rw [bandHaltBy]
  by_cases hkl : k>limit
  · rw [if_pos hkl]
    unfold followEvent
    rw [if_pos (by have := negative_event_band k w; omega)]
  · rw [if_neg hkl,band_macro_negative hv]
    by_cases hs : w=0 ∨ w=2*k+3 ∨ w=2*k+7 ∨ 2*k+9<3*w
    · rw [CapNegative.event_stop hs]
      unfold followEvent
      dsimp
      rw [if_neg hkl]
      by_cases ht : w=2*k+3
      · simp [ht]
      · by_cases hsp : w=2*k+7
        · simp [ht,hsp]
        · have hd : ¬3*w≤2*k+9 := by have := hv.1; omega
          simp [ht,hsp,hd]
    · have hd : 3*w≤2*k+9 := by omega
      rw [CapNegative.event_step hs,
          if_neg (by omega : w≠2*k+3),
          if_neg (by omega : w≠2*k+7),if_pos hd]
      change (if k<k+1 then bandHaltBy limit (k+1) (negQ (k+1) (3*w)) else false)=_
      rw [if_pos (by omega : k<k+1)]
      exact band_halt_negative (CapNegative.step_valid hv hd)
termination_by limit+1-k
decreasing_by omega

/-- First positive return or terminal, from any valid band coordinate.
    A failed positive gate does not terminate the computation: it enters
    the exact negative excursion, then returns to the positive sector. -/
def signedEvent (k q : Nat) : Nat × Option (Nat × Nat) :=
  if q≤2*P k-2 then
    let p := positiveNext k q
    if k+7≤p then (k,some (k+1,p))
    else CapNegative.event k (2*p-3)
  else CapNegative.event k (negWeight k q)

theorem signed_event_band (k q : Nat) : k≤(signedEvent k q).1 := by
  unfold signedEvent
  split
  · dsimp
    split
    · omega
    · exact negative_event_band _ _
  · exact negative_event_band _ _

theorem signed_event_return {k q j v : Nat} (hv : ValidQ k q)
    (he : (signedEvent k q).2=some (j,v)) :
    (signedEvent k q).1<j ∧ PosQ j v := by
  unfold signedEvent at he ⊢
  by_cases hp : q≤2*P k-2
  · rw [if_pos hp] at he ⊢
    dsimp at he ⊢
    have hpos : PosQ k q := ⟨hv.1,hp,hv.2.2⟩
    by_cases hpass : k+7≤positiveNext k q
    · rw [if_pos hpass] at he ⊢
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      have hq : 0<q := by have := hv.1; omega
      have hb := positive_next_bounds hq hp
      exact ⟨by omega,⟨hpass,hb.2,positive_next_parity hq hp hv.2.2⟩⟩
    · rw [if_neg hpass] at he ⊢
      exact negative_event_return (entry_weight hpos (by omega)).1 he
  · rw [if_neg hp] at he ⊢
    exact negative_event_return (weight_valid hv (by omega)) he

theorem band_halt_same_macro {limit k q v : Nat}
    (h : bandMacro k q=bandMacro k v) :
    bandHaltBy limit k q=bandHaltBy limit k v := by
  rw [bandHaltBy.eq_1 limit k q,bandHaltBy.eq_1 limit k v,h]

theorem signed_event_exact {limit k q : Nat} (hv : ValidQ k q) :
    bandHaltBy limit k q=followEvent limit (bandHaltBy limit) (signedEvent k q) := by
  unfold signedEvent
  by_cases hp : q≤2*P k-2
  · rw [if_pos hp]
    dsimp
    have hpos : PosQ k q := ⟨hv.1,hp,hv.2.2⟩
    by_cases hpass : k+7≤positiveNext k q
    · rw [if_pos hpass]
      have hq : 0<q := by have := hv.1; omega
      rw [bandHaltBy,positive_gate_pass hq hp hpass]
      unfold followEvent
      dsimp
      by_cases hk : k>limit <;> simp [hk]
    · rw [if_neg hpass]
      have hf : positiveNext k q<k+7 := by omega
      rw [band_halt_same_macro (positive_fail_macro hpos hf)]
      exact band_halt_negative (entry_weight hpos hf).1
  · rw [if_neg hp]
    have hneg : 2*P k-1≤q := by omega
    exact (congrArg (bandHaltBy limit k) (negQ_of_weight hv hneg).symm).trans
      (band_halt_negative (weight_valid hv hneg))

/-- The positive-return macro's exact bounded halting test. -/
def signedHaltBy (limit k q : Nat) : Bool :=
  if (signedEvent k q).1>limit then false else
    match (signedEvent k q).2 with
    | none => true
    | some (j,v) => if k<j then signedHaltBy limit j v else false
termination_by limit+1-k
decreasing_by
  have hb := signed_event_band k q
  omega

theorem signed_halt_by_eq {limit k q : Nat} (hv : ValidQ k q) :
    signedHaltBy limit k q=bandHaltBy limit k q := by
  rw [signedHaltBy,signed_event_exact hv]
  unfold followEvent
  have hb := signed_event_band k q
  by_cases hl : (signedEvent k q).1>limit
  · rw [if_pos hl,if_pos hl]
  · rw [if_neg hl,if_neg hl]
    cases he : (signedEvent k q).2 with
    | none => rfl
    | some z =>
      obtain ⟨j,v⟩ := z
      have hr := signed_event_return hv he
      have hj : k<j := by omega
      change (if k<j then signedHaltBy limit j v else false)=bandHaltBy limit j v
      rw [if_pos hj]
      exact signed_halt_by_eq (pos_valid hr.2)
termination_by limit+1-k
decreasing_by omega

/-- Exact terminal criterion at each positive entry, allowing safe
    exceptional excursions and returns. -/
theorem positive_event_terminal_iff {k q : Nat} (hk : 1≤k) (hv : PosQ k q) :
    (signedEvent k q).2=none ↔
      ∃ n, 3^n*(2*positiveNext k q-3)=2*(k+n)+3 := by
  unfold signedEvent
  rw [if_pos hv.2.1]
  dsimp
  by_cases hpass : k+7≤positiveNext k q
  · rw [if_pos hpass]
    constructor
    · intro h; contradiction
    · rintro ⟨n,h⟩
      have hbig : 2*k+7<2*positiveNext k q-3 := by omega
      have hg := CapNegative.above_grows hbig n
      omega
  · rw [if_neg hpass]
    exact CapNegative.event_terminal_iff hk (entry_weight hv (by omega)).1

#print axioms band_halt_negative
#print axioms signed_event_return
#print axioms signed_halt_by_eq
#print axioms positive_event_terminal_iff
end CapSieve
