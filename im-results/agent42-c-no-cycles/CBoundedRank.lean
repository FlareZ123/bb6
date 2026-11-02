import CNoCycles

namespace BB6Agent42

/-- Bounded-rank progress score, increasing on all live transitions whose
    target rank remains at most B. -/
def score (B : Nat) (s : S) : Nat :=
  rank s * (B+1) + (B - potential s)

theorem potential_le_rank (s : S) : potential s ≤ rank s := by
  rcases s with ⟨a,k,c⟩
  simp only [potential,rank]
  omega

theorem score_step_strict (B : Nat) (s t : S)
    (hb : rank t ≤ B) (h : nextC s = some t) :
    score B s < score B t := by
  have hs := strict_step s t h
  have hmono : rank s ≤ rank t := by
    unfold Strict at hs
    omega
  have hps : potential s ≤ B := by
    have hp := potential_le_rank s
    omega
  have hpt : potential t ≤ B := by
    have hp := potential_le_rank t
    omega
  unfold Strict at hs
  rcases hs with hlt | ⟨he,hp⟩
  · have hmul := Nat.mul_le_mul_right (B+1) (show rank s + 1 ≤ rank t by omega)
    have hadd : (rank s + 1)*(B+1) = rank s*(B+1)+(B+1) := by
      simp [Nat.add_mul]
    dsimp [score]
    omega
  · dsimp [score]
    rw [he]
    omega

theorem score_run_progress (B n : Nat) (s t : S)
    (hb : rank t ≤ B) (h : run n (some s) = some t) :
    score B s + n ≤ score B t := by
  induction n generalizing s t with
  | zero =>
      have he : s = t := by simpa [run] using h
      subst t
      omega
  | succ n ih =>
      cases hs : nextC s with
      | none => simp [run,hs,run_none] at h
      | some u =>
          have hr : run n (some u) = some t := by
            simpa [run,hs] using h
          have hu : rank u ≤ B := by
            have hm := rank_run_mono n u t hr
            omega
          have hstep := score_step_strict B s u hu hs
          have htail := ih u t hb hr
          omega

theorem score_bound (B : Nat) (s : S) (hs : rank s ≤ B) :
    score B s ≤ (B+1)*(B+1)-1 := by
  have hmul := Nat.mul_le_mul_right (B+1) hs
  have hpot : potential s ≤ B := by
    have hm := potential_le_rank s
    omega
  have hsq : (B+1)*(B+1) = B*(B+1)+(B+1) := by simp [Nat.add_mul]
  dsimp [score]
  omega

/-- A live run of (B+1)^2 accelerated steps must escape every state
    of weighted rank at most B, regardless of its starting configuration. -/
theorem escape_rank_by_square (B : Nat) (s t : S)
    (h : run ((B+1)*(B+1)) (some s) = some t) :
    B < rank t := by
  by_cases ht : B < rank t
  · exact ht
  · have hb : rank t ≤ B := by omega
    have hp := score_run_progress B ((B+1)*(B+1)) s t hb h
    have htbound := score_bound B t hb
    have hpos : 0 < (B+1)*(B+1) := Nat.mul_pos (by omega) (by omega)
    omega

/-- Splitting a deterministic finite execution after its first n calls. -/
theorem run_add (m n : Nat) (o : Option S) :
    run (m+n) o = run m (run n o) := by
  induction n generalizing o with
  | zero => simp [run]
  | succ n ih =>
      rw [Nat.add_succ]
      change run (m+n) (o.bind nextC) = run m (run n (o.bind nextC))
      exact ih _

/-- For an arbitrary target, global finite reachability reduces to a
    quadratic bounded simulation. No target can first appear once the
    accelerator has run (R+1)^2 calls, where R is its weighted rank. -/
theorem hit_target_iff_bounded (s target : S) :
    (∃ n, run n (some s) = some target) ↔
    (∃ n, n < (rank target+1)*(rank target+1) ∧
          run n (some s) = some target) := by
  constructor
  · rintro ⟨n, hn⟩
    by_cases hshort : n < (rank target+1)*(rank target+1)
    · exact ⟨n, hshort, hn⟩
    · have hlate : (rank target+1)*(rank target+1) ≤ n := by omega
      have he : n = (n-(rank target+1)*(rank target+1)) +
            (rank target+1)*(rank target+1) := by omega
      rw [he,run_add] at hn
      cases hm : run ((rank target+1)*(rank target+1)) (some s) with
      | none => simp [hm,run_none] at hn
      | some u =>
          have hhigh := escape_rank_by_square (rank target) s u hm
          have hmono := rank_run_mono (n-(rank target+1)*(rank target+1)) u target
            (by simpa [hm] using hn)
          omega
  · rintro ⟨n, _, hn⟩
    exact ⟨n, hn⟩

#print axioms hit_target_iff_bounded
#print axioms escape_rank_by_square
#print axioms score_run_progress
end BB6Agent42
