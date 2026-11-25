import RankWidth
set_option maxHeartbeats 0

namespace DExit
open DLowerRank

/-- Pop the written cell of a second-child input. The previous lower-rank
    theorem pays for the entire pop, so the first-child output rank does not
    exceed the original output rank. -/
theorem inverse_child_rank {s z b r y : Nat} (hb : b < 2)
    (h : Exit s (2*z+b) r y) : rank z ≤ rank y := by
  have hl := first_exit_lower h
  by_cases hz : z=0
  · subst z; rw [rank]; simp
  · have hp := rank_push b z hb
    have hc : push b (cls z) ≠ 0 := by
      rw [← push_sound b z hb]
      exact fun hh => by have := (cls_zero _).1 hh; omega
    have hw := (wt_bounds (push b (cls z)%16)).1
    unfold charge at hp
    simp only [hc,ite_false] at hp
    omega

/-- The finite inverse grammar stores output goals in a fixed rank ball and
    restricts every answer by the proved local lower-rank inequality. -/
inductive InverseBounded (cap : Nat) : Nat → Nat → Nat → Nat → Prop where
  | left (q w b r : Nat) (h : rule q (w%2) = some (b,false,r))
      (hc : rank (2*(w/2)+b) ≤ cap)
      (hr : rank w ≤ rank (2*(w/2)+b)+4) :
      InverseBounded cap q w r (2*(w/2)+b)
  | right (q w b r r2 y r3 z : Nat) (h : rule q (w%2) = some (b,true,r))
      (h1 : InverseBounded cap r (w/2) r2 y)
      (h2 : InverseBounded cap r2 (2*y+b) r3 z)
      (hc : rank z ≤ cap) (hr : rank w ≤ rank z+4) :
      InverseBounded cap q w r3 z

theorem inverse_bounded_sound {cap q w r y} (h : InverseBounded cap q w r y) : Exit q w r y := by
  induction h with
  | left q w b r hr _ _ => exact Exit.left q w b r hr
  | right q w b r r2 y r3 z hr _ _ _ _ ih1 ih2 =>
    exact Exit.right q w b r r2 y r3 z hr ih1 ih2

theorem inverse_bounded_complete {q w r y} (h : Exit q w r y)
    {cap : Nat} (hc : rank y ≤ cap) : InverseBounded cap q w r y := by
  induction h with
  | left q w b r hr => exact .left q w b r hr hc (first_exit_lower (.left q w b r hr))
  | right q w b r r2 y r3 z hr h1 h2 ih1 ih2 =>
    have hb := (rule_valid hr).2.1
    have hy := inverse_child_rank hb h2
    exact .right q w b r r2 y r3 z hr (ih1 (Nat.le_trans hy hc)) (ih2 hc) hc
      (first_exit_lower (.right q w b r r2 y r3 z hr h1 h2))

theorem inverse_grammar_iff (q w r y : Nat) :
    Exit q w r y ↔ InverseBounded (rank y) q w r y :=
  ⟨fun h => inverse_bounded_complete h (Nat.le_refl _), inverse_bounded_sound⟩

theorem inverse_finite_universe {cap q w r y} (h : InverseBounded cap q w r y) :
    q < 6 ∧ r < 6 ∧ y < 2^(cap/4) ∧ w < 2^((cap+4)/4) := by
  have hh : rank y ≤ cap ∧ rank w ≤ rank y+4 := by
    cases h with
    | left _ _ _ _ _ h1 h2 => exact ⟨h1,h2⟩
    | right _ _ _ _ _ _ _ _ _ _ _ h1 h2 => exact ⟨h1,h2⟩
  have states (q w r y : Nat) (he : Exit q w r y) : q < 6 ∧ r < 6 := by
    induction he with
    | left q w b r hr => exact ⟨(rule_valid hr).1,(rule_valid hr).2.2⟩
    | right q w b r r2 y r3 z hr _ _ _ ih2 => exact ⟨(rule_valid hr).1,ih2.2⟩
  obtain ⟨hq,hr⟩ := states _ _ _ _ (inverse_bounded_sound h)
  have hwy := (rank_width y).1
  have hww := (rank_width w).1
  exact ⟨hq,hr,
    Nat.lt_of_lt_of_le (width_bound y) (Nat.pow_le_pow_right (by decide) (by omega)),
    Nat.lt_of_lt_of_le (width_bound w) (Nat.pow_le_pow_right (by decide) (by omega))⟩

/-- Splice a completed first exit into an arbitrary extra left stack, then
    follow the supplied continuation. This proves the reverse direction of
    RawExit -> Exit without invoking termination or a head-space bound. -/
theorem raw_splice {t q w r y : Nat} {L : List Nat}
    (h : RawExit t L q w r y) (a : Nat) (T : List Nat)
    {u r' z : Nat} (k : RawExit u T r (2*y+a) r' z) :
    RawExit (t+u) (L++a::T) q w r' z := by
  induction h with
  | done q w b r hr =>
    simpa [Nat.add_comm] using (RawExit.left u q w b r a T r' z hr k)
  | left t q w b r b0 L r0 y hr _ ih =>
    have h1 := RawExit.left (t+u) q w b r b0 (L++a::T) r' z hr (ih k)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
  | right t q w b r L r0 y hr _ ih =>
    have h1 := RawExit.right (t+u) q w b r (L++a::T) r' z hr (ih k)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1

theorem exit_to_raw {q w r y} (h : Exit q w r y) : ∃ t, RawExit t [] q w r y := by
  induction h with
  | left q w b r hr => exact ⟨1,.done q w b r hr⟩
  | right q w b r r2 y r3 z hr _ _ ih1 ih2 =>
    obtain ⟨t,h1⟩ := ih1
    obtain ⟨u,h2⟩ := ih2
    have hs := raw_splice h1 b [] h2
    exact ⟨t+u+1,.right (t+u) q w b r [] r3 z hr hs⟩

theorem raw_inverse_iff (q w r y : Nat) :
    (∃ t, RawExit t [] q w r y) ↔ InverseBounded (rank y) q w r y :=
  ⟨fun ⟨_,h⟩ => (inverse_grammar_iff q w r y).1 (raw_to_exit h),
   fun h => exit_to_raw (inverse_bounded_sound h)⟩

#print axioms inverse_child_rank
#print axioms inverse_grammar_iff
#print axioms inverse_finite_universe
#print axioms raw_inverse_iff
end DExit
