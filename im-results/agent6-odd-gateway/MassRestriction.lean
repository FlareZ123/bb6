import ReachableOdd

namespace BB6Agent6

/-- Published drain's mass inequality, independently rechecked here. -/
theorem G_mass_lower (k c : Nat) :
    2*k+c+2 ≤ (G k c).1+(G k c).2 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h1 : c < 2*k
    · have hr : k - (c/2+1) < k := by omega
      have hrec := ih _ hr (2*c+3)
      rw [G]
      simp only [h1, dite_true]
      omega
    · by_cases h2 : c ≤ 2*k+1
      · rw [G]
        simp [h1,h2]
        omega
      · rw [G]
        simp [h1,h2]
        omega

theorem G_mass_one (k : Nat) :
    2*k+5 ≤ (G k 1).1+(G k 1).2 := by
  by_cases hk:k=0
  · subst k
    simp [G]
  · have hlow : 1 < 2*k := by omega
    have hr := G_mass_lower (k-1) 5
    rw [G]
    simp only [hlow, dite_true, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    omega

/-- Every successful step increases the sum of both counters. -/
theorem T_mass_strict (a c b d : Nat) (h : T a c = some (b,d)) :
    a+c < b+d := by
  unfold T at h
  by_cases hc0 : c=0
  · simp [hc0] at h
    omega
  · by_cases hc1 : c=1
    · simp [hc0,hc1] at h
      omega
    · by_cases ha : a%2=0
      · simp [hc0,hc1,ha] at h
        omega
      · by_cases hc2 : c=2
        · simp [hc0,hc1,ha,hc2] at h
        · by_cases hc3 : c=3
          · simp [hc0,hc1,ha,hc2,hc3] at h
            have hm := G_mass_one (a/2)
            have heq : (G (a/2) 1).1 = b ∧ (G (a/2) 1).2 = d := by
              exact Prod.mk.inj h
            rw [heq.1,heq.2] at hm
            omega
          · simp [hc0,hc1,ha,hc2,hc3] at h
            have hm := G_mass_lower (a/2+1) (c-2)
            have heq : (G (a/2+1) (c-2)).1 = b ∧
              (G (a/2+1) (c-2)).2 = d := by
              exact Prod.mk.inj h
            rw [heq.1,heq.2] at hm
            omega

/-- A surviving n-step trace increases its sum of counters by at least n. -/
theorem runT_mass (n : Nat) (s t : Nat × Nat)
    (h : runT n s = some t) :
    s.1+s.2+n ≤ t.1+t.2 := by
  induction n generalizing t with
  | zero =>
    simp only [runT, Option.some.injEq] at h
    subst t
    omega
  | succ n ih =>
    simp only [runT] at h
    cases hr : runT n s with
    | none => simp [hr] at h
    | some u =>
      simp only [hr, Option.bind_some] at h
      have hin := ih u hr
      rcases u with ⟨a,c⟩
      rcases t with ⟨b,d⟩
      have ht := T_mass_strict a c b d h
      simp only [Prod.fst, Prod.snd] at *
      omega

/-- Build the next finite trace certificate from a proved macro transition. -/
theorem runT_step (n : Nat) (start here after : Nat × Nat)
    (hp : runT n start = some here)
    (hs : T here.1 here.2 = some after) :
    runT (n+1) start = some after := by
  simp [runT, hp, hs]

/-- First fifteen exact blank-entry accelerated hubs. -/
theorem blank_at_0 :
    runT 0 (2,1) = some (2,1) := by
  rfl

theorem blank_at_1 :
    runT 1 (2,1) = some (4,0) := by
  exact runT_step 0 (2,1) (2,1) (4,0)
    blank_at_0 (by simp [T,G])

theorem blank_at_2 :
    runT 2 (2,1) = some (2,5) := by
  exact runT_step 1 (2,1) (4,0) (2,5)
    blank_at_1 (by simp [T,G])

theorem blank_at_3 :
    runT 3 (2,1) = some (5,3) := by
  exact runT_step 2 (2,1) (2,5) (5,3)
    blank_at_2 (by simp [T,G])

theorem blank_at_4 :
    runT 4 (2,1) = some (8,1) := by
  exact runT_step 3 (2,1) (5,3) (8,1)
    blank_at_3 (by simp [T,G])

theorem blank_at_5 :
    runT 5 (2,1) = some (10,0) := by
  exact runT_step 4 (2,1) (8,1) (10,0)
    blank_at_4 (by simp [T,G])

theorem blank_at_6 :
    runT 6 (2,1) = some (2,11) := by
  exact runT_step 5 (2,1) (10,0) (2,11)
    blank_at_5 (by simp [T,G])

theorem blank_at_7 :
    runT 7 (2,1) = some (5,9) := by
  exact runT_step 6 (2,1) (2,11) (5,9)
    blank_at_6 (by simp [T,G])

theorem blank_at_8 :
    runT 8 (2,1) = some (0,17) := by
  exact runT_step 7 (2,1) (5,9) (0,17)
    blank_at_7 (by simp [T,G])

theorem blank_at_9 :
    runT 9 (2,1) = some (3,15) := by
  exact runT_step 8 (2,1) (0,17) (3,15)
    blank_at_8 (by simp [T,G])

theorem blank_at_10 :
    runT 10 (2,1) = some (12,7) := by
  exact runT_step 9 (2,1) (3,15) (12,7)
    blank_at_9 (by simp [T,G])

theorem blank_at_11 :
    runT 11 (2,1) = some (15,5) := by
  exact runT_step 10 (2,1) (12,7) (15,5)
    blank_at_10 (by simp [T,G])

theorem blank_at_12 :
    runT 12 (2,1) = some (8,17) := by
  exact runT_step 11 (2,1) (15,5) (8,17)
    blank_at_11 (by simp [T,G])

theorem blank_at_13 :
    runT 13 (2,1) = some (11,15) := by
  exact runT_step 12 (2,1) (8,17) (11,15)
    blank_at_12 (by simp [T,G])

theorem blank_at_14 :
    runT 14 (2,1) = some (0,29) := by
  exact runT_step 13 (2,1) (11,15) (0,29)
    blank_at_13 (by simp [T,G])

theorem blank_at_15 :
    runT 15 (2,1) = some (3,27) := by
  exact runT_step 14 (2,1) (0,29) (3,27)
    blank_at_14 (by simp [T,G])

/-- The blank-start accelerated trajectory never visits the exceptional
    odd-counter gateway (2,15), regardless of orbit length. -/
theorem blank_ne_two_fifteen (n : Nat) :
    runT n (2,1) ≠ some (2,15) := by
  intro hh
  by_cases hsmall : n < 15
  · have hcases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 ∨ n=9 ∨ n=10 ∨ n=11 ∨ n=12 ∨ n=13 ∨ n=14 := by omega
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst n <;>
      simp [blank_at_0, blank_at_1, blank_at_2, blank_at_3, blank_at_4, blank_at_5, blank_at_6, blank_at_7, blank_at_8, blank_at_9, blank_at_10, blank_at_11, blank_at_12, blank_at_13, blank_at_14] at hh
  · have hm := runT_mass n (2,1) (2,15) hh
    simp only [Prod.fst, Prod.snd] at hm
    omega

#print axioms BB6Agent6.blank_ne_two_fifteen
#print axioms BB6Agent6.runT_mass
end BB6Agent6
