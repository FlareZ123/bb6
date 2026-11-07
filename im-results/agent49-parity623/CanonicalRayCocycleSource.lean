import Agent49TernaryBufferSource
import Agent8BudgetSource

/-!
Canonical minimal ternary-budget ray coordinates for the four source-certified
#623 affine sectors.  Each theorem identifies the exact base transition and
the affine shift of its output.  This is a source-level cocycle representation,
not a blank-root cone-invariance theorem.
-/

namespace BB6.Agent49CanonicalRayCocycleSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49TernaryShiftSource
open BB6.Agent49TernaryBufferSource
open BB6.Agent8BudgetSource

/-- Least exponent whose ternary-ones budget covers d+3. -/
noncomputable def leftOddExponent (d : Nat) : Nat :=
  Nat.find (show ∃ k, d+3 ≤ ternaryOnes k from
    ⟨d+3, ternaryOnes_ge (d+3)⟩)

/-- Least exponent whose ternary-ones budget covers d+2. -/
noncomputable def leftEvenExponent (d : Nat) : Nat :=
  Nat.find (show ∃ k, d+2 ≤ ternaryOnes k from
    ⟨d+2, ternaryOnes_ge (d+2)⟩)

/-- Least parity-restricted exponent for the odd right ray. -/
noncomputable def rightOddExponent (a : Nat) : Nat :=
  Nat.find (show ∃ k, a-1 ≤ ternaryOnes (2*k+5) from
    ⟨a, by have h := ternaryOnes_ge (2*a+5); omega⟩)

/-- Least parity-restricted exponent for the even right ray. -/
noncomputable def rightEvenExponent (a : Nat) : Nat :=
  Nat.find (show ∃ k, a < ternaryOnes (2*k+3) from
    ⟨a, by have h := ternaryOnes_ge (2*a+3); omega⟩)

theorem leftOddExponent_spec (d : Nat) :
    d+3 ≤ ternaryOnes (leftOddExponent d) := by
  unfold leftOddExponent
  exact Nat.find_spec
    (show ∃ k, d+3 ≤ ternaryOnes k from
      ⟨d+3, ternaryOnes_ge (d+3)⟩)

theorem leftOddExponent_le (d m : Nat) (h : d+3 ≤ ternaryOnes m) :
    leftOddExponent d ≤ m := by
  unfold leftOddExponent
  exact Nat.find_min' h

theorem leftOddExponent_minimal (d j : Nat)
    (hj : j < leftOddExponent d) :
    ¬ d+3 ≤ ternaryOnes j := by
  intro h
  have hle := leftOddExponent_le d j h
  omega

theorem leftEvenExponent_spec (d : Nat) :
    d+2 ≤ ternaryOnes (leftEvenExponent d) := by
  unfold leftEvenExponent
  exact Nat.find_spec
    (show ∃ k, d+2 ≤ ternaryOnes k from
      ⟨d+2, ternaryOnes_ge (d+2)⟩)

theorem leftEvenExponent_le (d m : Nat) (h : d+2 ≤ ternaryOnes m) :
    leftEvenExponent d ≤ m := by
  unfold leftEvenExponent
  exact Nat.find_min' h

theorem leftEvenExponent_minimal (d j : Nat)
    (hj : j < leftEvenExponent d) :
    ¬ d+2 ≤ ternaryOnes j := by
  intro h
  have hle := leftEvenExponent_le d j h
  omega

theorem rightOddExponent_spec (a : Nat) :
    a-1 ≤ ternaryOnes (2*rightOddExponent a+5) := by
  unfold rightOddExponent
  exact Nat.find_spec
    (show ∃ k, a-1 ≤ ternaryOnes (2*k+5) from
      ⟨a, by have h := ternaryOnes_ge (2*a+5); omega⟩)

theorem rightOddExponent_le (a m : Nat)
    (h : a-1 ≤ ternaryOnes (2*m+5)) :
    rightOddExponent a ≤ m := by
  unfold rightOddExponent
  exact Nat.find_min' h

theorem rightOddExponent_minimal (a j : Nat)
    (hj : j < rightOddExponent a) :
    ¬ a-1 ≤ ternaryOnes (2*j+5) := by
  intro h
  have hle := rightOddExponent_le a j h
  omega

theorem rightEvenExponent_spec (a : Nat) :
    a < ternaryOnes (2*rightEvenExponent a+3) := by
  unfold rightEvenExponent
  exact Nat.find_spec
    (show ∃ k, a < ternaryOnes (2*k+3) from
      ⟨a, by have h := ternaryOnes_ge (2*a+3); omega⟩)

theorem rightEvenExponent_le (a m : Nat)
    (h : a < ternaryOnes (2*m+3)) :
    rightEvenExponent a ≤ m := by
  unfold rightEvenExponent
  exact Nat.find_min' h

theorem rightEvenExponent_minimal (a j : Nat)
    (hj : j < rightEvenExponent a) :
    ¬ a < ternaryOnes (2*j+3) := by
  intro h
  have hle := rightEvenExponent_le a j h
  omega

/-- A far-left odd state is the minimal boundary state plus a first-counter
shift, and its complete original-source transition is translated by the same
amount. -/
theorem leftOddCanonicalTransition (a d : Nat)
    (hd : d%2=1) (hbranch : d+5≤a)
    (hbudget : d+3≤ternaryOnes (a-d-5)) :
    ∃ B E,
      highLevelNext (.D a d) =
        some (.D (B + (a-d-5-leftOddExponent d)) E) ∧
      highLevelNext (.D (d+5+leftOddExponent d) d) =
        some (.D B E) := by
  classical
  let k := leftOddExponent d
  let t := a-d-5-k
  have hbaseBudget : d+3≤ternaryOnes k := leftOddExponent_spec d
  have hk : k≤a-d-5 := leftOddExponent_le d (a-d-5) hbudget
  have hdecomp : a=(d+5+k)+t := by dsimp [t]; omega
  have hbaseEq : highLevelNext (.D (d+5+k) d) = drainB k (d+3) 5 := by
    rw [highLevelNext]
    have h0 : d+5+k ≠ 0 := by omega
    have h1 : d%2=1 ∧ d+5+k≥d+5 := by omega
    simp only [if_neg h0, if_pos h1]
  obtain ⟨B,E,hBE⟩ := drainB_safe_ones (d+3) k 5 hbaseBudget
  have hbase : highLevelNext (.D (d+5+k) d) = some (.D B E) := by
    rw [hbaseEq,hBE]
  have hshift : highLevelNext (.D a d) =
      (highLevelNext (.D (d+5+k) d)).map (liftFirstState t) := by
    calc
      highLevelNext (.D a d) =
          highLevelNext (.D ((d+5+k)+t) d) := by rw [hdecomp]
      _ = (highLevelNext (.D (d+5+k) d)).map (liftFirstState t) :=
        highLevel_far_odd_shift_ones (d+5+k) d t hd (by omega) (by
          have harg : d+5+k-d-5=k := by omega
          rw [harg]
          exact hbaseBudget)
  refine ⟨B,E,?_,hbase⟩
  rw [hshift,hbase]
  rfl

/-- A far-left even state is the minimal boundary state plus a first-counter
shift, and its complete original-source transition is translated by the same
amount. -/
theorem leftEvenCanonicalTransition (a d : Nat)
    (hd : d%2=0) (hbranch : d+3≤a)
    (hbudget : d+2≤ternaryOnes (a-d-2)) :
    ∃ B E,
      highLevelNext (.D a d) =
        some (.D (B + (a-d-2-leftEvenExponent d)) E) ∧
      highLevelNext (.D (d+2+leftEvenExponent d) d) =
        some (.D B E) := by
  classical
  let k := leftEvenExponent d
  let t := a-d-2-k
  have hbaseBudget : d+2≤ternaryOnes k := leftEvenExponent_spec d
  have hk : k≤a-d-2 := leftEvenExponent_le d (a-d-2) hbudget
  have hkpos : 1≤k := by
    by_contra h
    have hk0 : k=0 := by omega
    subst k
    have hbad : d+2≤0 := by simpa [ternaryOnes] using hbaseBudget
    omega
  have hdecomp : a=(d+2+k)+t := by dsimp [t]; omega
  have hbaseEq : highLevelNext (.D (d+2+k) d) = drainB k (d+2) 2 := by
    rw [highLevelNext]
    have h0 : d+2+k ≠ 0 := by omega
    have h1neg : ¬(d%2=1 ∧ d+2+k≥d+5) := by omega
    have h1pos : d%2=0 ∧ d+2+k≥d+3 := by omega
    simp only [if_neg h0, if_neg h1neg, if_pos h1pos]
  obtain ⟨B,E,hBE⟩ := drainB_safe_ones (d+2) k 2 hbaseBudget
  have hbase : highLevelNext (.D (d+2+k) d) = some (.D B E) := by
    rw [hbaseEq,hBE]
  have hshift : highLevelNext (.D a d) =
      (highLevelNext (.D (d+2+k) d)).map (liftFirstState t) := by
    calc
      highLevelNext (.D a d) =
          highLevelNext (.D ((d+2+k)+t) d) := by rw [hdecomp]
      _ = (highLevelNext (.D (d+2+k) d)).map (liftFirstState t) :=
        highLevel_far_even_shift_ones (d+2+k) d t hd (by omega) (by
          have harg : d+2+k-d-2=k := by omega
          rw [harg]
          exact hbaseBudget)
  refine ⟨B,E,?_,hbase⟩
  rw [hshift,hbase]
  rfl

/-- A far-right odd state is the minimal boundary state plus a second-counter
shift by twice t, and its complete original-source transition translates the
first output counter by twice t. -/
theorem rightOddCanonicalTransition (a d : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=1) (hside : a≤d)
    (hbudget : a-1≤ternaryOnes (d+4-a)) :
    ∃ B E,
      highLevelNext (.D a d) =
        some (.D (B + 2*( (d-a-1)/2-rightOddExponent a)) E) ∧
      highLevelNext (.D a (a+1+2*rightOddExponent a)) =
        some (.D B E) := by
  classical
  let k := rightOddExponent a
  let m := (d-a-1)/2
  let t := m-k
  have hexp : 2*m+5=d+4-a := by omega
  have hbaseBudget : a-1≤ternaryOnes (2*k+5) := rightOddExponent_spec a
  have hmBudget : a-1≤ternaryOnes (2*m+5) := by rw [hexp]; exact hbudget
  have hk : k≤m := rightOddExponent_le a m hmBudget
  have hdBase : (a+1+2*k)%2=1 := by omega
  have hdecomp : d=(a+1+2*k)+2*t := by dsimp [t]; omega
  have hbaseEq : highLevelNext (.D a (a+1+2*k)) =
      drainB (2*k+5) (a-1) 3 := by
    rw [highLevelNext]
    have h0 : a ≠ 0 := by omega
    have h1 : ¬((a+1+2*k)%2=1 ∧ a≥a+1+2*k+5) := by omega
    have h2 : ¬((a+1+2*k)%2=0 ∧ a≥a+1+2*k+3) := by omega
    have hodd : a%2 ≠ 1 := by omega
    have heq : a ≠ a+1+2*k+2 := by omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg hodd, if_neg heq, if_pos hdBase]
    have harg : a+1+2*k+4-a=2*k+5 := by omega
    rw [harg]
  obtain ⟨B,E,hBE⟩ := drainB_safe_ones (a-1) (2*k+5) 3 hbaseBudget
  have hbase : highLevelNext (.D a (a+1+2*k)) = some (.D B E) := by
    rw [hbaseEq,hBE]
  have hshift : highLevelNext (.D a d) =
      (highLevelNext (.D a (a+1+2*k))).map (liftFirstState (2*t)) := by
    calc
      highLevelNext (.D a d) =
          highLevelNext (.D a ((a+1+2*k)+2*t)) := by rw [hdecomp]
      _ = (highLevelNext (.D a (a+1+2*k))).map (liftFirstState (2*t)) :=
        highLevel_right_odd_shift_ones a (a+1+2*k) t ha he hdBase (by omega) (by
          have harg : a+1+2*k+4-a=2*k+5 := by omega
          rw [harg]
          exact hbaseBudget)
  refine ⟨B,E,?_,hbase⟩
  rw [hshift,hbase]
  rfl

/-- A far-right even state is the minimal boundary state plus a second-counter
shift by twice t, and its complete original-source transition translates the
first output counter by twice t. -/
theorem rightEvenCanonicalTransition (a d : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=0) (hside : a≤d)
    (hbudget : a<ternaryOnes (d+1-a)) :
    ∃ B E,
      highLevelNext (.D a d) =
        some (.D (B + 2*(d/2-a/2-1-rightEvenExponent a)) E) ∧
      highLevelNext (.D a (a+2+2*rightEvenExponent a)) =
        some (.D B E) := by
  classical
  let k := rightEvenExponent a
  let m := d/2-a/2-1
  let t := m-k
  have hstrict : a+2≤d := by
    by_contra h
    have heq : d=a := by omega
    subst d
    simp [ternaryOnes] at hbudget
    omega
  have hdDiv : d=2*(d/2) := by
    have h := Nat.mod_add_div d 2
    rw [hd] at h
    omega
  have haDiv : a=2*(a/2) := by
    have h := Nat.mod_add_div a 2
    rw [he] at h
    omega
  have hexp : 2*m+3=d+1-a := by
    dsimp [m]
    rw [hdDiv,haDiv]
    omega
  have hbaseBudget : a<ternaryOnes (2*k+3) := rightEvenExponent_spec a
  have hmBudget : a<ternaryOnes (2*m+3) := by rw [hexp]; exact hbudget
  have hk : k≤m := rightEvenExponent_le a m hmBudget
  have hdecomp : d=(a+2+2*k)+2*t := by
    dsimp [t,m]
    rw [hdDiv,haDiv]
    omega
  have hdBase : (a+2+2*k)%2=0 := by omega
  have hdBaseNotOne : (a+2+2*k)%2 ≠ 1 := by omega
  have hbaseEq : highLevelNext (.D a (a+2+2*k)) =
      (evalA (2*k+3) a (2*a+5)).bind
        (fun p => drainB p.1 p.2.1 p.2.2) := by
    rw [highLevelNext]
    have h0 : a ≠ 0 := by omega
    have h1 : ¬((a+2+2*k)%2=1 ∧ a≥a+2+2*k+5) := by omega
    have h2 : ¬((a+2+2*k)%2=0 ∧ a≥a+2+2*k+3) := by omega
    have hodd : a%2 ≠ 1 := by omega
    have heq : a ≠ a+2+2*k+2 := by omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg hodd, if_neg heq, if_neg hdBaseNotOne]
    have harg : a+2+2*k+1-a=2*k+3 := by omega
    rw [harg]
  obtain ⟨x,b,y,hEval,hbudget'⟩ :=
    evalA_ones_budget (2*k+3) a (2*a+5) hbaseBudget
  obtain ⟨B,E,hBE⟩ := drainB_safe_ones b x y hbudget'
  have hbase : highLevelNext (.D a (a+2+2*k)) = some (.D B E) := by
    rw [hbaseEq,hEval]
    simp only [Option.bind_some]
    exact hBE
  have hshift : highLevelNext (.D a d) =
      (highLevelNext (.D a (a+2+2*k))).map (liftFirstState (2*t)) := by
    calc
      highLevelNext (.D a d) =
          highLevelNext (.D a ((a+2+2*k)+2*t)) := by rw [hdecomp]
      _ = (highLevelNext (.D a (a+2+2*k))).map (liftFirstState (2*t)) :=
        highLevel_right_even_shift_ones a (a+2+2*k) t ha he hdBase (by omega) (by
          have harg : a+2+2*k+1-a=2*k+3 := by omega
          rw [harg]
          exact hbaseBudget)
  refine ⟨B,E,?_,hbase⟩
  rw [hshift,hbase]
  rfl

/-- Every state in the four-sector new affine cone has a canonical minimal
ternary-budget base and an exact affine output cocycle. -/
theorem newAffine_canonicalRay (a d : Nat) (hcone : newAffineCone a d) :
    (∃ B E,
      highLevelNext (.D a d) =
        some (.D (B + (a-d-5-leftOddExponent d)) E) ∧
      highLevelNext (.D (d+5+leftOddExponent d) d) = some (.D B E)) ∨
    (∃ B E,
      highLevelNext (.D a d) =
        some (.D (B + (a-d-2-leftEvenExponent d)) E) ∧
      highLevelNext (.D (d+2+leftEvenExponent d) d) = some (.D B E)) ∨
    (∃ B E,
      highLevelNext (.D a d) =
        some (.D (B + 2*((d-a-1)/2-rightOddExponent a)) E) ∧
      highLevelNext (.D a (a+1+2*rightOddExponent a)) = some (.D B E)) ∨
    (∃ B E,
      highLevelNext (.D a d) =
        some (.D (B + 2*(d/2-a/2-1-rightEvenExponent a)) E) ∧
      highLevelNext (.D a (a+2+2*rightEvenExponent a)) = some (.D B E)) := by
  rcases hcone with h | h | h | h
  · rcases h with ⟨hd,hbranch,hbudget⟩
    exact Or.inl (leftOddCanonicalTransition a d hd hbranch hbudget)
  · rcases h with ⟨hd,hbranch,hbudget⟩
    exact Or.inr (Or.inl (leftEvenCanonicalTransition a d hd hbranch hbudget))
  · rcases h with ⟨ha,he,hside,hd,hbudget⟩
    exact Or.inr (Or.inr (Or.inl (rightOddCanonicalTransition a d ha he hd hside hbudget)))
  · rcases h with ⟨ha,he,hside,hd,hbudget⟩
    exact Or.inr (Or.inr (Or.inr (rightEvenCanonicalTransition a d ha he hd hside hbudget)))

#print axioms leftOddCanonicalTransition
#print axioms leftEvenCanonicalTransition
#print axioms rightOddCanonicalTransition
#print axioms rightEvenCanonicalTransition
#print axioms newAffine_canonicalRay

end BB6.Agent49CanonicalRayCocycleSource
