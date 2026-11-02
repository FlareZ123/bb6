import CBoundedRank

namespace BB6Agent42

/-- The number of permissible (rank, middle-counter) pairs at ranks below n,
    given the invariant 2*k ≤ rank. -/
def offset : Nat → Nat
  | 0 => 0
  | n+1 => offset n + n/2 + 1

/-- `offset` is monotone. -/
theorem offset_mono (a b : Nat) (hab : a ≤ b) : offset a ≤ offset b := by
  induction b with
  | zero =>
      have he : a=0 := by omega
      subst a
      omega
  | succ b ih =>
      by_cases ha : a ≤ b
      · have hh := ih ha
        rw [offset]
        omega
      · have hh : a=b+1 := by omega
        subst a
        omega

/-- An increase in rank separates all possible lower-rank positions. -/
theorem offset_dominates (a b : Nat) (hab : a < b) :
    offset a + a/2 < offset b := by
  have hp := offset_mono (a+1) b (by omega)
  rw [offset] at hp
  omega

def sharpScore (s : S) : Nat := offset (rank s) + s.2.1

theorem middle_le_half_rank (s : S) : s.2.1 ≤ rank s / 2 := by
  rcases s with ⟨a,k,c⟩
  simp only [rank]
  omega

theorem sharp_step (s t : S) (h : nextC s = some t) :
    sharpScore s < sharpScore t := by
  have hstrict := strict_step s t h
  rcases hstrict with hr | ⟨hr,hp⟩
  · have hb := offset_dominates (rank s) (rank t) hr
    have hk := middle_le_half_rank s
    dsimp [sharpScore]
    omega
  · have he : s.2.1 < t.2.1 := by
      rcases s with ⟨a,k,c⟩
      rcases t with ⟨a',k',c'⟩
      change k < k'
      simp only [rank,potential] at hr hp
      omega
    dsimp [sharpScore]
    rw [hr]
    omega

/-- Score increases by at least the length of any successful run. -/
theorem sharp_run (n : Nat) (s t : S)
    (h : run n (some s) = some t) : sharpScore s + n ≤ sharpScore t := by
  induction n generalizing s t with
  | zero =>
      have he : s=t := by simpa [run] using h
      subst t
      omega
  | succ n ih =>
      cases hs : nextC s with
      | none => simp [run,hs,run_none] at h
      | some u =>
          have hr : run n (some u) = some t := by
            simpa [run,hs] using h
          have hh := sharp_step s u hs
          have ht := ih u t hr
          omega

/-- Any rank-B state has position strictly inside the rank-prefix count. -/
theorem sharp_score_below (B : Nat) (s : S) (hb : rank s ≤ B) :
    sharpScore s < offset (B+1) := by
  have h1 := middle_le_half_rank s
  have h2 := offset_dominates (rank s) (B+1) (by omega)
  dsimp [sharpScore]
  omega

/-- The optimal rank-only counting bound on the number of live steps.
    It is approximately B^2/4, improving the quadratic bound by 4x. -/
theorem sharp_escape (B : Nat) (s t : S)
    (h : run (offset (B+1)) (some s) = some t) :
    B < rank t := by
  by_cases ht : B < rank t
  · exact ht
  have hb : rank t ≤ B := by omega
  have hscore := sharp_run (offset (B+1)) s t h
  have hbound := sharp_score_below B t hb
  omega

/-- Exact finite cutoff for reaching an arbitrary target, from any source. -/
theorem sharp_hit_target_iff_bounded (s target : S) :
    (∃ n, run n (some s) = some target) ↔
    (∃ n, n < offset (rank target + 1) ∧ run n (some s) = some target) := by
  constructor
  · rintro ⟨n, hn⟩
    by_cases hshort : n < offset (rank target+1)
    · exact ⟨n, hshort, hn⟩
    · have hlate : offset (rank target+1) ≤ n := by omega
      have he : n = (n-offset (rank target+1)) + offset (rank target+1) := by omega
      rw [he,run_add] at hn
      cases hm : run (offset (rank target+1)) (some s) with
      | none => simp [hm,run_none] at hn
      | some u =>
          have hh := sharp_escape (rank target) s u hm
          have hmono := rank_run_mono (n-offset (rank target+1)) u target
            (by simpa [hm] using hn)
          omega
  · rintro ⟨n,_,hn⟩
    exact ⟨n,hn⟩

/-- Closed forms for the rank-prefix cardinality. -/
theorem offset_even (q : Nat) : offset (2*q) = q*(q+1) := by
  induction q with
  | zero => simp [offset]
  | succ q ih =>
      have hfirst : offset (2*q+1) = offset (2*q)+q+1 := by
        rw [show 2*q+1=(2*q)+1 by omega, offset]
        have hd : (2*q)/2=q := by omega
        omega
      have hsecond : offset (2*(q+1)) = offset (2*q+1)+q+1 := by
        rw [show 2*(q+1)=(2*q+1)+1 by omega, offset]
        have hd : (2*q+1)/2=q := by omega
        omega
      rw [hsecond,hfirst,ih]
      simp only [Nat.mul_add,Nat.add_mul]
      omega

theorem offset_odd (q : Nat) : offset (2*q+1) = (q+1)*(q+1) := by
  rw [show 2*q+1=(2*q)+1 by omega, offset]
  rw [offset_even]
  have hd : (2*q)/2=q := by omega
  rw [hd]
  simp only [Nat.mul_add,Nat.add_mul]
  omega

/-- Exact closed form: the all-rank cutoff for rank B is
    floor((B+2)^2/4), a factor-four improvement in its quadratic term. -/
theorem cutoff_closed_form (B : Nat) :
    offset (B+1) = ((B+2)*(B+2))/4 := by
  rcases Nat.mod_two_eq_zero_or_one B with hb | hb
  · have he : B = 2*(B/2) := by omega
    rw [he,show 2*(B/2)+1=2*(B/2)+1 by omega, offset_odd]
    have hx : ((2*(B/2)+2)*(2*(B/2)+2))/4 = ((B/2)+1)*((B/2)+1) := by
      have hd : ((2*(B/2)+2)*(2*(B/2)+2))=4*(((B/2)+1)*((B/2)+1)) := by
        have he2 : 2*(B/2)+2 = 2*((B/2)+1) := by omega
        rw [he2]
        calc
          (2*(B/2+1))*(2*(B/2+1)) = (2*2)*((B/2+1)*(B/2+1)) := by ac_rfl
          _ = 4*((B/2+1)*(B/2+1)) := rfl
      rw [hd]
      simp
    omega
  · have he : B=2*(B/2)+1 := by omega
    rw [he,show (2*(B/2)+1)+1=2*((B/2)+1) by omega, offset_even]
    have hd : ((2*(B/2)+3)*(2*(B/2)+3))/4 = ((B/2)+1)*((B/2)+2) := by
      have hprod : (2*(B/2)+3)*(2*(B/2)+3)=4*(((B/2)+1)*((B/2)+2))+1 := by
        have hm : (2*(B/2))*(2*(B/2)) = 4*((B/2)*(B/2)) := by
          calc
            (2*(B/2))*(2*(B/2)) = (2*2)*((B/2)*(B/2)) := by ac_rfl
            _ = 4*((B/2)*(B/2)) := rfl
        simp only [Nat.mul_add,Nat.add_mul]
        rw [hm]
        omega
      rw [hprod]
      omega
    have he3 : 2*(B/2)+1+2=2*(B/2)+3 := by omega
    rw [he3,hd]

#print axioms sharp_hit_target_iff_bounded
#print axioms sharp_escape
end BB6Agent42
