import OddGatewayMod8

namespace BB6Agent6

/-- Every nested-drain result has its first coordinate divisible by four. -/
theorem G_first_mod4 (k c : Nat) : (G k c).1 % 4 = 0 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    rw [G]
    by_cases hsmall : c < 2*k
    · simp only [hsmall, dite_true]
      exact ih (k-(c/2+1)) (by omega) (2*c+3)
    · simp only [hsmall, dite_false]
      by_cases hmid : c ≤ 2*k+1
      · simp only [hmid, ite_true]
      · simp only [hmid, ite_false]
        omega

/-- The exact accelerated step from the published two-counter reduction. -/
def T (a c : Nat) : Option (Nat × Nat) :=
  if c = 0 then some (2,a+1)
  else if c = 1 then some (a+2,0)
  else if a % 2 = 0 then some (a+3,c-2)
  else if c = 2 then none
  else if c = 3 then some (G (a/2) 1)
  else some (G (a/2+1) (c-2))

/-- Every successor with both even left and odd right counters
    has left coordinate 2 or a multiple-of-four left coordinate. -/
theorem T_odd_image (a c b d : Nat)
    (h : T a c = some (b,d)) (hd : d % 2 = 1)
    (hbEven : b % 2 = 0) :
    b = 2 ∨ b % 4 = 0 := by
  by_cases hzero : c=0
  · simp [T,hzero] at h
    exact Or.inl h.1.symm
  · by_cases hone : c=1
    · simp [T,hzero,hone] at h
      omega
    · by_cases heven : a%2=0
      · simp [T,hzero,hone,heven] at h
        rcases h with ⟨hb, hd2⟩
        omega
      · by_cases htwo : c=2
        · simp [T,hzero,hone,heven,htwo] at h
        · by_cases hthree : c=3
          · simp only [T, if_neg hzero, if_neg hone, if_neg heven,
                if_neg htwo, if_pos hthree, Option.some.injEq,
                Prod.mk.injEq] at h
            right
            have hr := G_first_mod4 (a/2) 1
            have hb : (G (a/2) 1).1 = b := by simpa using congrArg Prod.fst h
            rw [hb] at hr
            exact hr
          · simp only [T, if_neg hzero, if_neg hone, if_neg heven,
                if_neg htwo, if_neg hthree, Option.some.injEq,
                Prod.mk.injEq] at h
            right
            have hr := G_first_mod4 (a/2+1) (c-2)
            have hb : (G (a/2+1) (c-2)).1 = b := by simpa using congrArg Prod.fst h
            rw [hb] at hr
            exact hr

/-- Finite iteration of the independently restated accelerator. -/
def runT : Nat → Nat × Nat → Option (Nat × Nat)
  | 0,s => some s
  | n+1,s => (runT n s).bind (fun q => T q.1 q.2)

/-- Every blank-start reachable odd-right hub with even left counter
    has left counter 2 or a left counter divisible by 4. -/
theorem blank_odd_section_restriction (n : Nat) (s : Nat × Nat)
    (h : runT n (2,1) = some s) (hc : s.2 % 2 = 1)
    (ha : s.1 % 2 = 0) : s.1 = 2 ∨ s.1 % 4 = 0 := by
  cases n with
  | zero =>
    simp only [runT, Option.some.injEq] at h
    subst s
    exact Or.inl rfl
  | succ n =>
    simp only [runT] at h
    cases he : runT n (2,1) with
    | none => simp [he] at h
    | some t =>
      simp only [he, Option.bind_some] at h
      rcases t with ⟨a,c⟩
      rcases s with ⟨b,d⟩
      exact T_odd_image a c b d h hc ha

/-- The only odd-input distinguished reset hub (2,c) whose odd-sector
    return immediately lands on right coordinate 3 is (2,15). -/
theorem U_two_right_three_iff (c : Nat) (hc : c % 2 = 1) :
    (U 2 c).2 = 3 ↔ c = 15 := by
  by_cases hlarge : 13 ≤ c
  · have h1 : c ≠ 1 := by omega
    have h3 : c ≠ 3 := by omega
    have h5 : c ≠ 5 := by omega
    have hbound : 2*3+2 ≤ c-4 := by omega
    have hsub : c-4-8 = c-12 := by omega
    have hbig : G 3 (c-4) = (16,c-12) := by
      rw [G]
      simp [show ¬(c-4 < 6) by omega, show ¬(c-4 ≤ 7) by omega,
        hsub]
    simp only [U, if_neg h1, if_neg h3, if_neg h5, hbig, Prod.snd]
    omega
  · have hcases : c=1 ∨ c=3 ∨ c=5 ∨ c=7 ∨ c=9 ∨ c=11 := by omega
    rcases hcases with h | h | h | h | h | h <;> subst c <;> simp [U, G]

#print axioms BB6Agent6.blank_odd_section_restriction
#print axioms BB6Agent6.U_two_right_three_iff
end BB6Agent6
