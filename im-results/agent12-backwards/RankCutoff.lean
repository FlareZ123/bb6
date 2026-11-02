import NoFourthTarget

namespace BB6.Agent12

/-- Strictly increasing two-counter rank for every nonhalting T call. -/
theorem G_mass_lower (k c : Nat) :
    2*k+c+2 ≤ (G k c).1+(G k c).2 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h : c < 2*k
    · have hrec := ih _ (by omega : k-(c/2+1)<k) (2*c+3)
      rw [G]
      simp only [h,dite_true]
      omega
    · by_cases h2 : c ≤ 2*k+1
      · rw [G]
        simp [h,h2]
        omega
      · rw [G]
        simp [h,h2]
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

theorem T_mass_increases (a c b d : Nat)
    (ht:T a c=some (b,d)) : a+c < b+d := by
  unfold T at ht
  by_cases h0:c=0
  · simp [h0] at ht
    omega
  · by_cases h1:c=1
    · simp [h0,h1] at ht
      omega
    · by_cases ha:a%2=0
      · simp [h0,h1,ha] at ht
        omega
      · by_cases h2:c=2
        · simp [h0,h1,ha,h2] at ht
        · by_cases h3:c=3
          · simp [h0,h1,ha,h2,h3] at ht
            have hm:=G_mass_one (a/2)
            have heq : (G (a/2) 1).1=b ∧ (G (a/2) 1).2=d := Prod.mk.inj ht
            rw [heq.1,heq.2] at hm
            omega
          · simp [h0,h1,ha,h2,h3] at ht
            have hm:=G_mass_lower (a/2+1) (c-2)
            have heq : (G (a/2+1) (c-2)).1=b ∧
              (G (a/2+1) (c-2)).2=d := Prod.mk.inj ht
            rw [heq.1,heq.2] at hm
            omega

/-- The complete reachable subset below rank 45 consists of the first
    24 configurations on the deterministic trajectory. -/
def earlyStates : List (Nat × Nat) :=
  [(2,1), (4,0), (2,5), (5,3), (8,1), (10,0), (2,11),
   (5,9), (0,17), (3,15), (12,7), (15,5), (8,17),
   (11,15), (0,29), (3,27), (12,19), (15,17),
   (4,31), (7,29), (20,17), (23,15), (24,17), (27,15)]

/-- Finite, kernel-computed transition-closure certificate for the low-rank set. -/
def earlyValid : Bool :=
  earlyStates.all fun p =>
    match T p.1 p.2 with
    | some q => decide (q∈earlyStates ∨ 45 ≤ q.1+q.2)
    | none => false

theorem earlyValid_true : earlyValid = true := by decide +kernel

theorem early_step (a c b d:Nat) (hmem:(a,c)∈earlyStates)
    (ht:T a c=some (b,d)) : (b,d)∈earlyStates ∨ 45≤b+d := by
  have h := (List.all_eq_true.mp earlyValid_true) (a,c) hmem
  have hcheck : decide ((b,d)∈earlyStates ∨ 45≤b+d) = true := by
    simpa [earlyValid, ht] using h
  exact of_decide_eq_true hcheck

/-- The exact blank trajectory cannot leave a rank>=45 region by going forward. -/
theorem blank_low_rank_complete (a c:Nat) (hr:BlankReach a c) :
    (a,c)∈earlyStates ∨ 45≤a+c := by
  induction hr with
  | init => left; decide
  | next a c b d _ ht ih =>
      rcases ih with hmem | hbig
      · exact early_step a c b d hmem ht
      · right
        have hinc := T_mass_increases a c b d ht
        omega

/-- First previously unclassified P1 critical target, n=2 (c=42),
    is excluded by a finite 24-state cut-off proof plus strict rank growth. -/
theorem blank_ne_third_critical : ¬BlankReach 2 42 := by
  intro hr
  have h:=blank_low_rank_complete 2 42 hr
  rcases h with hmem | hlarge
  · have hn : (2,42)∉earlyStates := by decide
    exact hn hmem
  · omega

#print axioms BB6.Agent12.blank_ne_third_critical

end BB6.Agent12
