import PeriodPigeonhole
namespace PeriodCycle

/-- Equal states remain equal after any number of deterministic transitions. -/
theorem deterministic_forward (q : Nat → Nat) (step : Nat → Nat)
    (hs : ∀ n, q (n+1) = step (q n))
    (i j k : Nat) (heq : q i=q j) : q (i+k)=q (j+k) := by
  induction k with
  | zero => simpa using heq
  | succ k ih =>
    calc
      q (i+(k+1)) = step (q (i+k)) := by
        rw [show i+(k+1)=(i+k)+1 by omega, hs]
      _ = step (q (j+k)) := by rw [ih]
      _ = q (j+(k+1)) := by
        rw [show j+(k+1)=(j+k)+1 by omega, hs]

/-- A periodic deterministic orbit constrained to S-1 nonzero residues below S
    must close in fewer than S transitions. No invertibility assumption. -/
theorem shorter_return (S : Nat) (hS : 0<S)
    (q : Nat → Nat) (step : Nat → Nat)
    (hs : ∀ n, q (n+1)=step (q n))
    (hperiod : ∀ n, q (n+S)=q n)
    (hbound : ∀ i<S, 0<q i ∧ q i<S) :
    ∃ r, 0<r ∧ r<S ∧ q r=q 0 := by
  by_cases hret : ∃ r, 0<r ∧ r<S ∧ q r=q 0
  · exact hret
  · exfalso
    apply PeriodPigeonhole.no_primitive_full_cycle S hS q hbound
    intro i hi j hj heq
    by_cases hlt : i<j
    · have hh := deterministic_forward q step hs i j (S-i) heq
      have hl : i+(S-i)=S := by omega
      have hr : j+(S-i)=S+(j-i) := by omega
      rw [hl, hr] at hh
      have hroot : q S=q 0 := by simpa using hperiod 0
      have hjshift : q (S+(j-i))=q (j-i) := by
        simpa only [Nat.add_comm] using hperiod (j-i)
      rw [hroot, hjshift] at hh
      have ht : 0<j-i ∧ j-i<S ∧ q (j-i)=q 0 := by
        constructor
        · omega
        constructor
        · omega
        · exact hh.symm
      exact False.elim (hret ⟨j-i,ht⟩)
    · by_cases hequal : i=j
      · exact hequal
      · have hgt : j<i := by omega
        have hh := deterministic_forward q step hs j i (S-j) heq.symm
        have hl : j+(S-j)=S := by omega
        have hr : i+(S-j)=S+(i-j) := by omega
        rw [hl, hr] at hh
        have hroot : q S=q 0 := by simpa using hperiod 0
        have hishift : q (S+(i-j))=q (i-j) := by
          simpa only [Nat.add_comm] using hperiod (i-j)
        rw [hroot, hishift] at hh
        have ht : 0<i-j ∧ i-j<S ∧ q (i-j)=q 0 := by
          constructor
          · omega
          constructor
          · omega
          · exact hh.symm
        exact False.elim (hret ⟨i-j,ht⟩)

#print axioms shorter_return
end PeriodCycle
