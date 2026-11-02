import OddReturn

namespace BB6.HaltingFunnel

/-- Starting at an odd right counter, the only non-odd successor is
    exactly the zero hub, necessarily from c=1. -/
theorem T_odd_exit (a c b d : Nat) (hc : c%2=1)
    (ht : T a c = some (b,d)) : d%2=1 ∨ (c=1 ∧ d=0) := by
  by_cases h1 : c=1
  · subst c
    simp [T] at ht
    right
    exact ⟨rfl, ht.2.symm⟩
  · have h0 : c≠0 := by omega
    by_cases ha : a%2=0
    · have hbig : 3≤c := by omega
      have he : T a c = some (a+3,c-2) := T_even a c ha (by omega)
      have hq : d = c-2 :=
        (congrArg Prod.snd (Option.some.inj (he.symm.trans ht))).symm
      left
      omega
    · by_cases h3 : c=3
      · subst c
        have hg : T a 3 = some (G (a/2) 1) := by
          simp [T, ha]
        have hh : (G (a/2) 1).2%2=1 := G_odd _ _ (by decide)
        have hd : d=(G (a/2) 1).2 :=
          (congrArg Prod.snd (Option.some.inj (hg.symm.trans ht))).symm
        left
        omega
      · have h5 : 5≤c := by omega
        have hg : T a c = some (G (a/2+1) (c-2)) := by
          simp [T, h0, h1, ha, h3, show c≠2 by omega]
        have hodd : (c-2)%2=1 := by omega
        have hh : (G (a/2+1) (c-2)).2%2=1 := G_odd _ _ hodd
        have hd : d=(G (a/2+1) (c-2)).2 :=
          (congrArg Prod.snd (Option.some.inj (hg.symm.trans ht))).symm
        left
        omega

/-- Positive even right-counter successor from an odd counter is impossible. -/
theorem T_odd_no_positive_even (a c b d : Nat) (hc:c%2=1)
    (ht : T a c = some (b,d)) (he : d%2=0) : d=0 ∧ c=1 := by
  rcases T_odd_exit a c b d hc ht with hodd | ⟨h1,h0⟩
  · omega
  · exact ⟨h0,h1⟩

/-- The unique positive-even counter entry from a zero-c hub is (2,a+1). -/
theorem T_zero_entry (a b d : Nat) (ht : T a 0 = some (b,d)) :
    b=2 ∧ d=a+1 := by
  simp [T] at ht
  exact ⟨ht.1.symm, ht.2.symm⟩

#print axioms BB6.HaltingFunnel.T_odd_no_positive_even
end BB6.HaltingFunnel
