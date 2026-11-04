import BackwardMod
set_option maxHeartbeats 0
set_option maxRecDepth 4000
namespace A4Backward48
open A4Backward

/-- Compact 600-cell reverse-closed invariant in M48, with only two low
clauses and three high clauses. Genuine source root (5,0,1) lies outside. -/
def low (a k c : Nat) : Prop :=
  (a%16=3 ∧ (k+c)%24=7) ∨
  (a%16=11 ∧ (k+c)%24=19)

def high (a k c : Nat) : Prop :=
  let d := (a+24-c%24)%24
  let t := (a+k)%48
  (d=0 ∧ t%12=7) ∨
  (d=8 ∧ t%12=3) ∨
  (d=16 ∧ t%12=11)

def bad (a k c : Nat) : Prop :=
  if c<2 then low a k c else high a k c

theorem low_transfer (a k : Nat) :
    bad a (k+1) 0 → bad a k 1 := by
  intro h
  simpa [bad, low] using h

theorem high_to_low3 (a k : Nat) :
    bad a (k+2) 1 → bad a k 3 := by
  simp only [bad,show (1:Nat)<2 by omega,show ¬((3:Nat)<2) by omega,
    ↓reduceIte,low,high]
  intro h
  rcases h with h | h <;> omega

theorem zero_a0 (k : Nat) : ¬bad 1 0 (2*k+2) := by
  have hc : ¬(2*k+2<2) := by omega
  simp only [bad,hc,↓reduceIte,high]
  intro h
  rcases h with h | h | h <;> omega

theorem zero_a1_empty : ¬bad 5 0 1 := by
  simp [bad,low]

theorem zero_a1_pos (k : Nat) (hk : 0<k) :
    ¬bad 2 2 (2*k-1) := by
  by_cases hsmall:k=1
  · subst k
    simp [bad,low]
  · have hc : ¬(2*k-1<2) := by omega
    simp only [bad,hc,↓reduceIte,high]
    intro h
    rcases h with h | h | h <;> omega

theorem zero_a_pos (a k : Nat) (ha : 2≤a) :
    bad (a-2) 1 (2*k+1) → bad a k 0 := by
  intro h
  by_cases hk:k=0
  · subst k
    have hn : ¬low (a-2) 1 1 := by simp [low]
    exact False.elim (hn (by simpa [bad] using h))
  · have hc : ¬(2*k+1<2) := by omega
    have hh : high (a-2) 1 (2*k+1) := by
      simpa only [bad,hc,↓reduceIte] using h
    exfalso
    simp only [high] at hh
    rcases hh with hh | hh | hh <;> omega

theorem high_a0_even (k c : Nat) (hc : 4≤c) (hk : k%2=0) :
    bad (2*k+2) 2 (c-3) → bad 0 k c := by
  intro h
  by_cases hs:c=4
  · subst c
    have hn:¬low (2*k+2) 2 1 := by
      simp only [low]
      omega
    exact False.elim (hn (by simpa [bad] using h))
  · have hc2 : ¬(c-3<2) := by omega
    have hh : high (2*k+2) 2 (c-3) := by
      simpa only [bad,hc2,↓reduceIte] using h
    exfalso
    simp only [high] at hh
    rcases hh with hh | hh | hh <;> omega

theorem high_a0_odd (k c : Nat) (hc : 4≤c) (hk : k%2≠0) :
    bad (2*k+3) 0 c → bad 0 k c := by
  intro h
  have hhigh : ¬(c<2) := by omega
  have hh : high (2*k+3) 0 c := by
    simpa only [bad,hhigh,↓reduceIte] using h
  exfalso
  simp only [high] at hh
  rcases hh with hh | hh | hh <;> omega

theorem high_a_pos (a k c : Nat) (ha : 0<a) (hc : 4≤c) :
    bad (a-1) (k+1) (c-1) → bad a k c := by
  intro h
  have hc2 : ¬(c-1<2) := by omega
  have hd : (a-1+24-(c-1)%24)%24=(a+24-c%24)%24 := by omega
  have ht : ((a-1)+(k+1))%48=(a+k)%48 := by omega
  simp only [bad,hc2,show ¬(c<2) by omega,↓reduceIte,high] at h ⊢
  rw [hd,ht] at h
  exact h

theorem backward_step (a k c a' k' c' : Nat)
    (h : nextC (a,k,c)=some (a',k',c'))
    (hb : bad a' k' c') : bad a k c := by
  by_cases hc1:c=1
  · subst c
    simp [nextC] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact low_transfer a k hb
  by_cases hc2:c=2
  · subst c
    simp [nextC] at h
  by_cases hc3:c=3
  · subst c
    simp [nextC,hc1] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact high_to_low3 a k hb
  by_cases hc0:c=0
  · subst c
    by_cases ha0:a=0
    · subst a
      simp [nextC] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact False.elim (zero_a0 k hb)
    by_cases ha1:a=1
    · subst a
      by_cases hk0:k=0
      · subst k
        simp [nextC] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_a1_empty hb)
      · simp [nextC,ha0,hk0] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_a1_pos k (by omega) hb)
    · simp [nextC,ha0,ha1] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact zero_a_pos a k (by omega) hb
  · have hc4 : 4≤c := by omega
    by_cases ha0:a=0
    · subst a
      by_cases he:k%2=0
      · simp [nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact high_a0_even k c hc4 he hb
      · simp [nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact high_a0_odd k c hc4 he hb
    · simp [nextC,hc1,hc2,hc3,hc0,ha0] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact high_a_pos a k c (by omega) hc4 hb

#print axioms low_transfer
#print axioms high_to_low3
#print axioms zero_a_pos
#print axioms high_a0_even
#print axioms high_a0_odd
#print axioms backward_step
end A4Backward48
