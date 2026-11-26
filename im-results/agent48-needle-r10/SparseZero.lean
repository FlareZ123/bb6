import Lean
namespace NeedleSparse

def value (acc : Int) : List (Nat × Int) → Int
  | [] => acc
  | (g,c)::xs => acc + (2:Int)^g * value c xs

def zero (acc : Int) : List (Nat × Int) → Bool
  | [] => acc == 0
  | (g,c)::xs => acc % (2:Int)^g == 0 && zero (acc / (2:Int)^g + c) xs

theorem value_add (a b : Int) (xs : List (Nat × Int)) :
    value (a+b) xs = a+value b xs := by
  cases xs with
  | nil => rfl
  | cons p xs => rcases p with ⟨g,c⟩; simp [value, Int.add_assoc]


theorem zero_iff (a : Int) (xs : List (Nat × Int)) : zero a xs = true ↔ value a xs = 0 := by
  induction xs generalizing a with
  | nil => simp [zero,value]
  | cons p xs ih =>
    rcases p with ⟨g,c⟩
    let D := (2:Int)^g
    have hD : D ≠ 0 := Int.pow_ne_zero (by decide)
    have hdiv : a % D + D * (a / D) = a := Int.emod_add_mul_ediv a D
    change ((a % D == 0) && zero (a / D + c) xs) = true ↔ a + D * value c xs = 0
    simp only [Bool.and_eq_true, beq_iff_eq, ih, value_add]
    constructor
    · rintro ⟨hr,hq⟩
      rw [hr, Int.zero_add] at hdiv
      rw [←hdiv, ←Int.mul_add, hq, Int.mul_zero]
    · intro h
      have he : a = D * (-value c xs) := by grind
      have hr : a % D = 0 := Int.emod_eq_zero_of_dvd ⟨_,he⟩
      refine ⟨hr,?_⟩
      rw [hr,Int.zero_add] at hdiv
      have hh : D * (a / D + value c xs) = 0 := by rw [Int.mul_add,hdiv,h]
      exact (Int.mul_eq_zero.mp hh).resolve_left hD
/-- No positive power larger than a nonzero integer's magnitude divides it. -/
theorem gap_reject {a : Int} {g : Nat} (ha : a ≠ 0) (hg : a.natAbs.log2 < g) :
    a % (2:Int)^g ≠ 0 := by
  intro h
  have habs := Int.natAbs_pos.mpr ha
  have hlt := (Nat.log2_lt (by omega : a.natAbs ≠ 0)).mp hg
  have hd := Int.natAbs_dvd_natAbs.mpr (Int.dvd_of_emod_eq_zero h)
  rw [Int.natAbs_pow] at hd
  change 2^g ∣ a.natAbs at hd
  have := Nat.le_of_dvd habs hd
  omega

/-- Exact gap-aware variant: powers are allocated only if bounded by |acc|. -/
def compactZero (acc : Int) : List (Nat × Int) → Bool
  | [] => acc == 0
  | (g,c)::xs =>
    if acc == 0 then compactZero c xs
    else if acc.natAbs.log2 < g then false
    else acc % (2:Int)^g == 0 && compactZero (acc / (2:Int)^g+c) xs

theorem compactZero_eq (a : Int) (xs : List (Nat × Int)) : compactZero a xs = zero a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨g,c⟩
    by_cases h : a = 0
    · subst a; simp [compactZero,zero,ih]
    · by_cases hg : a.natAbs.log2 < g
      · have hr := gap_reject h hg
        simp [compactZero,zero,h,hg,hr]
      · simp [compactZero,zero,h,hg,ih]

theorem compactZero_iff (a : Int) (xs : List (Nat × Int)) : compactZero a xs = true ↔ value a xs = 0 := by
  rw [compactZero_eq,zero_iff]

/-- Absolute exponents, in increasing order, as produced by a rotation. -/
def absoluteValue : List (Nat × Int) → Int
  | [] => 0
  | (e,c)::xs => (2:Int)^e*c + absoluteValue xs

def orderedFrom (e : Nat) : List (Nat × Int) → Prop
  | [] => True
  | (f,_)::xs => e ≤ f ∧ orderedFrom f xs

def gaps (e : Nat) : List (Nat × Int) → List (Nat × Int)
  | [] => []
  | (f,c)::xs => (f-e,c)::gaps f xs

theorem absolute_eq (e : Nat) (c : Int) (xs : List (Nat × Int))
    (h : orderedFrom e xs) : absoluteValue ((e,c)::xs) = (2:Int)^e * value c (gaps e xs) := by
  induction xs generalizing e c with
  | nil => simp [absoluteValue,value,gaps]
  | cons p xs ih =>
    rcases p with ⟨f,d⟩
    have hef : e ≤ f := h.1
    have hrest : orderedFrom f xs := h.2
    change (2:Int)^e*c + absoluteValue ((f,d)::xs) = (2:Int)^e*(c+(2:Int)^(f-e)*value d (gaps f xs))
    rw [ih f d hrest,Int.mul_add,←Int.mul_assoc,←Int.pow_add,Nat.add_sub_of_le hef]

def check : List (Nat × Int) → Bool
  | [] => true
  | (e,c)::xs => compactZero c (gaps e xs)

theorem check_iff (xs : List (Nat × Int)) (h : orderedFrom 0 xs) :
    check xs = true ↔ absoluteValue xs = 0 := by
  cases xs with
  | nil => simp [check,absoluteValue]
  | cons p xs =>
    rcases p with ⟨e,c⟩
    rw [check,compactZero_iff,absolute_eq e c xs h.2]
    have hp : (2:Int)^e ≠ 0 := Int.pow_ne_zero (by decide)
    simp [Int.mul_eq_zero,hp]

theorem absoluteValue_perm {xs ys : List (Nat × Int)} (h : xs.Perm ys) :
    absoluteValue xs = absoluteValue ys := by
  induction h with
  | nil => rfl
  | cons p h ih => rcases p with ⟨e,c⟩; simp [absoluteValue,ih]
  | swap p q xs => rcases p with ⟨e,c⟩; rcases q with ⟨f,d⟩; simp only [absoluteValue]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem ordered_of_pairwise (xs : List (Nat × Int)) (e : Nat)
    (h : List.Pairwise (fun a b => a.1 ≤ b.1) xs)
    (he : ∀ p ∈ xs, e ≤ p.1) : orderedFrom e xs := by
  induction xs generalizing e with
  | nil => trivial
  | cons p xs ih =>
    rcases p with ⟨f,c⟩
    have hh := List.pairwise_cons.mp h
    exact ⟨he (f,c) (by simp), ih f hh.2 hh.1⟩

def sortCheck (xs : List (Nat × Int)) : Bool :=
    check (xs.mergeSort fun a b => a.1 ≤ b.1)

theorem sortCheck_iff (xs : List (Nat × Int)) : sortCheck xs = true ↔ absoluteValue xs = 0 := by
  let le : (Nat × Int) → (Nat × Int) → Bool := fun a b => a.1 ≤ b.1
  have htrans : ∀ a b c, le a b = true → le b c = true → le a c = true := by
    intro a b c hab hbc
    simp [le] at *
    omega
  have htotal : ∀ a b, (le a b || le b a) = true := by
    intro a b; simp [le]; omega
  have hp := List.pairwise_mergeSort htrans htotal xs
  have hp' : List.Pairwise (fun a b => a.1 ≤ b.1) (xs.mergeSort le) := by
    apply hp.imp_of_mem
    intro a b _ _ hab
    simpa [le] using hab
  have ho := ordered_of_pairwise (xs.mergeSort le) 0 hp' (by simp)
  change check (xs.mergeSort le) = true ↔ absoluteValue xs = 0
  rw [check_iff _ ho, absoluteValue_perm (List.mergeSort_perm xs le)]

#print axioms sortCheck_iff
#print axioms check_iff
#print axioms zero_iff
#print axioms compactZero_iff
end NeedleSparse
