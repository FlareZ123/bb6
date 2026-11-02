import BlankCriterion

namespace BB6.HaltingFunnel

/-- G outputs have first counter divisible by four. -/
theorem G_left_mod_four (k c : Nat) : (G k c).1%4=0 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h : c<2*k
    · rw [G]
      simp only [h,dite_true]
      exact ih _ (by omega) _
    · by_cases h2 : c≤2*k+1
      · rw [G]
        simp only [h,dite_false,h2,ite_eq_left]
      · rw [G]
        simp [h,h2]

/-- A transition to positive c with even a has a=2 or a divisible 4. -/
theorem T_positive_even_invariant (a c b d : Nat)
    (ht : T a c=some (b,d)) (hd:0<d) (hb:b%2=0) :
    b=2 ∨ b%4=0 := by
  by_cases h0 : c=0
  · subst c
    have he : T a 0 = some (2,a+1) := by simp [T]
    have hb' : b=2 := (Prod.mk.inj (Option.some.inj (he.symm.trans ht))).1.symm
    exact Or.inl hb'
  · by_cases h1 : c=1
    · subst c
      simp [T] at ht
      omega
    · by_cases ha : a%2=0
      · have ht' : T a c = some (a+3,c-2) := T_even a c ha (by omega)
        have hfst : b=a+3 :=
          (Prod.mk.inj (Option.some.inj (ht'.symm.trans ht))).1.symm
        omega
      · by_cases h2 : c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3 : c=3
          · subst c
            have he : T a 3=some (G (a/2) 1) := by simp [T,ha]
            have hfst : b=(G (a/2) 1).1 :=
              (congrArg Prod.fst (Option.some.inj (he.symm.trans ht))).symm
            exact Or.inr (by rw [hfst]; exact G_left_mod_four _ _)
          · have he : T a c=some (G (a/2+1) (c-2)) := by
              simp [T,h0,h1,ha,h2,h3]
            have hfst : b=(G (a/2+1) (c-2)).1 :=
              (congrArg Prod.fst (Option.some.inj (he.symm.trans ht))).symm
            exact Or.inr (by rw [hfst]; exact G_left_mod_four _ _)

/-- Exact blank-entry reachability in forward inductive form. -/
inductive BlankReach : Nat → Nat → Prop where
  | init : BlankReach 2 1
  | next (a c b d : Nat) : BlankReach a c → T a c=some (b,d) → BlankReach b d

/-- All truly reachable positive-counter hubs with even left counter
    have left counter exactly 2, or divisible by 4. -/
theorem blank_even_left_invariant (a c : Nat) (hr : BlankReach a c)
    (hc : 0<c) (ha : a%2=0) : a=2 ∨ a%4=0 := by
  induction hr with
  | init => exact Or.inl rfl
  | next a c b d hreach ht ih => exact T_positive_even_invariant a c b d ht hc ha

/-- Equivalence of our forward reachability and the T reflexive/transitive
    reachability used in the formal blank halting criterion. -/
theorem blank_reach_to_T (a c : Nat) (h:BlankReach a c) :
    ReachT 2 1 a c := by
  induction h with
  | init => exact ReachT.refl 2 1
  | next a c b d hr ht ih =>
      exact reach_trans 2 1 a c b d ih
        (ReachT.next a c b d b d ht (ReachT.refl b d))

theorem reachT_to_blank (a c b d : Nat) (h:ReachT a c b d)
    (hs:BlankReach a c) : BlankReach b d := by
  induction h with
  | refl => exact hs
  | next a c b d e f ht hr ih =>
      exact ih (BlankReach.next a c b d hs ht)

theorem blank_reach_iff_T (a c:Nat) :
    BlankReach a c ↔ ReachT 2 1 a c := by
  constructor
  · exact blank_reach_to_T a c
  · intro h
    exact reachT_to_blank 2 1 a c h BlankReach.init

#print axioms BB6.HaltingFunnel.blank_even_left_invariant
end BB6.HaltingFunnel
