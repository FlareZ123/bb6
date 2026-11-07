import SourceBridge

set_option maxHeartbeats 0

namespace A4Mod240

open A4Backward

/-- A coupled modulus-240 predecessor-closed cone for authentic Machine C.
    Its low phases have three paired residues, while its high phases
    have only two coupled congruences on all natural-number inputs. -/
def bad (a k c : Nat) : Prop :=
  if c = 0 then a % 240 = 5 ∧ k % 240 = 49
  else if c = 1 then a % 240 = 5 ∧ k % 240 = 48
  else if c = 3 then a % 240 = 5 ∧ k % 240 = 46
  else if 4 ≤ c then a % 120 = (c+2)%120 ∧ (a+k)%240 = 51
  else False

theorem one_back (a k : Nat) (h : bad a (k+1) 0) : bad a k 1 := by
  simp [bad] at h ⊢
  omega

theorem three_back (a k : Nat) (h : bad a (k+2) 1) : bad a k 3 := by
  simp [bad] at h ⊢
  omega

theorem zero_zero (k : Nat) : ¬ bad 1 0 (2*k+2) := by
  intro h
  by_cases hk : k=0
  · subst k
    simp [bad] at h
  · have hc : 4 ≤ 2*k+2 := by omega
    simp [bad, hc] at h

theorem zero_one_empty : ¬ bad 5 0 1 := by simp [bad]

theorem zero_one_pos (k : Nat) (hk : 0 < k) : ¬ bad 2 2 (2*k-1) := by
  intro h
  by_cases hk1 : k=1
  · subst k
    simp [bad] at h
  · by_cases hk2 : k=2
    · subst k
      simp [bad] at h
    · have hc : 4 ≤ 2*k-1 := by omega
      simp [bad,hc] at h

theorem zero_pos (a k : Nat) (_ha : 2 ≤ a) : ¬ bad (a-2) 1 (2*k+1) := by
  intro h
  by_cases hk0 : k=0
  · subst k
    simp [bad] at h
  · by_cases hk1 : k=1
    · subst k
      simp [bad] at h
    · have hc : 4 ≤ 2*k+1 := by omega
      simp [bad,hc] at h
      omega

theorem high_zero_even (k c : Nat) (hc : 4 ≤ c) (_he : k%2=0) :
    ¬ bad (2*k+2) 2 (c-3) := by
  intro h
  by_cases hc4 : c=4
  · subst c
    simp [bad] at h
  · by_cases hc5 : c=5
    · subst c
      simp [bad] at h
    · by_cases hc6 : c=6
      · subst c
        simp [bad] at h
      · have hcnext : 4 ≤ c-3 := by omega
        simp [bad,hcnext] at h
        omega

theorem high_zero_odd (k c : Nat) (hc : 4 ≤ c) (ho : k%2 ≠ 0) :
    ¬ bad (2*k+3) 0 c := by
  intro h
  simp [bad,hc] at h
  omega

theorem high_pos (a k c : Nat) (_ha : 0 < a) (hc : 4 ≤ c)
    (h : bad (a-1) (k+1) (c-1)) : bad a k c := by
  by_cases hc4 : c=4
  · subst c
    simp [bad] at h ⊢
    omega
  · have hcp : 4 ≤ c-1 := by omega
    have hn0 : c-1 ≠ 0 := by omega
    have hn1 : c-1 ≠ 1 := by omega
    have hn3 : c-1 ≠ 3 := by omega
    have hco0 : c ≠ 0 := by omega
    have hco1 : c ≠ 1 := by omega
    have hco3 : c ≠ 3 := by omega
    simp [bad,hn0,hn1,hn3,hcp,hco0,hco1,hco3,hc] at h ⊢
    omega

/-- Every original section-step predecessor of the coupled mod-240
    cone lies in the same cone. Exact exceptional c=0,1,2,3 and
    a=0 branches are handled universally. -/
theorem backward (a k c ap kp cp : Nat)
    (h : A4Backward.nextC (a,k,c)=some (ap,kp,cp))
    (hb : bad ap kp cp) : bad a k c := by
  by_cases hc1 : c=1
  · subst c
    simp [A4Backward.nextC] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact one_back a k hb
  by_cases hc2 : c=2
  · subst c
    simp [A4Backward.nextC] at h
  by_cases hc3 : c=3
  · subst c
    simp [A4Backward.nextC,hc1] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact three_back a k hb
  by_cases hc0 : c=0
  · subst c
    by_cases ha0 : a=0
    · subst a
      simp [A4Backward.nextC] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact False.elim (zero_zero k hb)
    by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · subst k
        simp [A4Backward.nextC] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_one_empty hb)
      · simp [A4Backward.nextC,ha0,hk0] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_one_pos k (by omega) hb)
    · simp [A4Backward.nextC,ha0,ha1] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact False.elim (zero_pos a k (by omega) hb)
  · have hc4 : 4 ≤ c := by omega
    by_cases ha0 : a=0
    · subst a
      by_cases he : k%2=0
      · simp [A4Backward.nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (high_zero_even k c hc4 he hb)
      · simp [A4Backward.nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (high_zero_odd k c hc4 he hb)
    · simp [A4Backward.nextC,hc1,hc2,hc3,hc0,ha0] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact high_pos a k c (by omega) hc4 hb

/-- All-time result for the genuine, unmodified BB6CLine.nextC blank
    root, using Agent4's already source-checked definitional bridge. -/
theorem source_blank_never_bad (s : Nat × Nat × Nat)
    (h : BB6CLine.Reach s) : ¬ bad s.1 s.2.1 s.2.2 := by
  induction h with
  | init => simp [bad]
  | next x y hx hs ih =>
      rcases x with ⟨a,k,c⟩
      rcases y with ⟨ap,kp,cp⟩
      intro hb
      have he : A4Backward.nextC (a,k,c) = some (ap,kp,cp) := by
        rw [A4Backward.nextC_source_equal]
        exact hs
      exact ih (backward a k c ap kp cp he hb)

/-- Entire genuine original-CLine reset cylinder (5,49) modulo 240
    is absent from the true blank-start accelerated orbit at every time. -/
theorem source_no_mod240_5_49 (a k : Nat)
    (ha : a%240=5) (hk : k%240=49)
    (hr : BB6CLine.Reach (a,k,0)) : False := by
  have hh := source_blank_never_bad (a,k,0) hr
  apply hh
  simp [bad,ha,hk]

#print axioms backward
#print axioms source_blank_never_bad
#print axioms source_no_mod240_5_49

end A4Mod240
