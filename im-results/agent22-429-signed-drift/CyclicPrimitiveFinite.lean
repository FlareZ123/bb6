import ValuationPacking

namespace FiniteCyclicValuation
open ValuationPacking

def succ {n : Nat} (hn : 0<n) (i : Fin n) : Fin n :=
  if h : i.val+1<n then ⟨i.val+1,h⟩ else ⟨0,hn⟩

def pred {n : Nat} (hn : 0<n) (i : Fin n) : Fin n :=
  if h : i.val=0 then ⟨n-1,by omega⟩ else ⟨i.val-1,by omega⟩

theorem succ_pred {n : Nat} (hn : 0<n) (i : Fin n) :
    succ hn (pred hn i)=i := by
  apply Fin.ext
  unfold pred
  split
  · rename_i h0
    have hnsub : n-1+1=n := by omega
    unfold succ
    simp only [Fin.val_mk]
    split
    · rename_i hlt
      rw [hnsub] at hlt
      omega
    · exact h0.symm
  · rename_i h0
    have hipos : 0<i.val := by omega
    have hsub : i.val-1+1=i.val := by omega
    have hlt : i.val-1+1<n := by omega
    unfold succ
    simp only [Fin.val_mk]
    split
    · omega
    · rename_i hnot
      exact False.elim (hnot hlt)

def predIter {n : Nat} (hn : 0<n) : Nat → Fin n → Fin n
| 0, i => i
| k+1, i => pred hn (predIter hn k i)

/-- Finite cyclic primitivity stated in the exact backward-separation form
    needed by predecessor uniqueness. This is equivalent to absence of a
    nontrivial rotational period for the exponent schedule. -/
def CyclicPrimitive {n : Nat} (hn : 0<n) (j : Fin n → Nat) : Prop :=
  ∀ a b : Fin n, a≠b → ∃ k : Nat, 0<k ∧ k≤n ∧
    j (predIter hn k a) ≠ j (predIter hn k b)

def CyclicWitness (K : Nat) {n : Nat} (hn : 0<n)
    (v j : Fin n → Nat) : Prop :=
  ∀ i : Fin n, Witness K (v i) (j i) (v (succ hn i))

theorem backwards_unique_one (K : Nat) {n : Nat} (hn : 0<n)
    (v j : Fin n → Nat) (h : CyclicWitness K hn v j)
    (a b : Fin n) (hab : v a=v b) :
    v (pred hn a)=v (pred hn b) ∧ j (pred hn a)=j (pred hn b) := by
  have ha := h (pred hn a)
  have hb := h (pred hn b)
  rw [succ_pred hn a] at ha
  rw [succ_pred hn b] at hb
  rw [←hab] at hb
  exact quotient_injective K _ _ _ _ (v a) ha hb

theorem backwards_unique_iter (K : Nat) {n : Nat} (hn : 0<n)
    (v j : Fin n → Nat) (h : CyclicWitness K hn v j)
    (a b : Fin n) (hab : v a=v b) :
    ∀ k : Nat, v (predIter hn k a)=v (predIter hn k b) ∧
      (0<k → j (predIter hn k a)=j (predIter hn k b)) := by
  intro k
  induction k with
  | zero =>
      constructor
      · simpa [predIter] using hab
      · intro hk
        omega
  | succ k ih =>
      have hs := backwards_unique_one K hn v j h
        (predIter hn k a) (predIter hn k b) ih.1
      constructor
      · simpa [predIter] using hs.1
      · intro _
        simpa [predIter] using hs.2

/-- A primitive finite cyclic exponent schedule has pairwise distinct slope
    sources in every legal valuation cycle. -/
theorem source_injective (K : Nat) {n : Nat} (hn : 0<n)
    (v j : Fin n → Nat) (h : CyclicWitness K hn v j)
    (hprim : CyclicPrimitive hn j) : Function.Injective v := by
  intro a b hab
  by_cases heq : a=b
  · exact heq
  obtain ⟨k,hkpos,hkle,hneq⟩ := hprim a b heq
  have he := (backwards_unique_iter K hn v j h a b hab k).2 hkpos
  exact False.elim (hneq he)

theorem singleton_primitive (j : Fin 1 → Nat) :
    CyclicPrimitive (by decide : 0<(1:Nat)) j := by
  intro a b hab
  exact False.elim (hab (Subsingleton.elim a b))

#print axioms singleton_primitive
#print axioms source_injective
end FiniteCyclicValuation
