import FatalFeederResidueArithmetic
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace BB746ForkCensus

def exceptional (r : Nat) : Prop :=
  r=113 ∨ r=400 ∨ r=526 ∨ r=599 ∨ r=886 ∨ r=887 ∨ r=1085 ∨ r=1372

instance (r : Nat) : Decidable (exceptional r) := by
  unfold exceptional
  infer_instance

/-- An exact finite theorem classifying all congruence classes modulo
1458 where an odd t=1 parent of the fatal height is admissible. -/
theorem coverage_154 : ∀ r : Fin 1458,
    (r.val%18=4 ∨ r.val%18=5) →
    (CascadeFatal46.good (r.val%486) ∨
      r.val%486=76 ∨ r.val%486=238 ∨
      r.val%486=275 ∨ r.val%486=437 ∨
      r.val=40 ∨ r.val=401 ∨ r.val=1012 ∨ r.val=1373 ∨
      exceptional r.val) := by
  decide

theorem count_admissible :
    ((List.range 1458).filter
      (fun r => decide (r%18=4 ∨ r%18=5))).length=162 := by
  decide

theorem count_excluded :
    ((List.range 1458).filter
      (fun r => decide ((r%18=4 ∨ r%18=5) ∧ ¬ exceptional r))).length=154 := by
  decide

/-- Universally transports the exact finite residue classification to
every unbounded index n. -/
theorem universal_154 (n : Nat)
    (hs : n%18=4 ∨ n%18=5)
    (he : ¬ exceptional (n%1458)) :
    CascadeFatal46.good (n%486) ∨
    n%486=76 ∨ n%486=238 ∨ n%486=275 ∨ n%486=437 ∨
    n%1458=40 ∨ n%1458=401 ∨ n%1458=1012 ∨ n%1458=1373 := by
  have hmod18 : (n%1458)%18=n%18 := by omega
  have hmod486 : (n%1458)%486=n%486 := by omega
  have hsource := coverage_154 ⟨n%1458,Nat.mod_lt _ (by decide)⟩
  have ht := hsource (by simpa only [hmod18] using hs)
  simp only [hmod486] at ht
  rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
  · exact Or.inl ht
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr (Or.inl ht))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ht)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht)))))))
  · exact False.elim (he ht)

#print axioms coverage_154
#print axioms count_admissible
#print axioms count_excluded
#print axioms universal_154
end BB746ForkCensus
