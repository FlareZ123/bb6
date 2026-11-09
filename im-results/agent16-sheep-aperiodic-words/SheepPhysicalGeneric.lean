import SheepAperiodic

namespace SheepPhysicalGeneric
open SheepAffine SheepAperiodic

/-- Explicit generic first-even branch from the actual Sheep section formula. -/
def GenericEdge (a h x y : Nat) : Prop :=
  ∃ u v : Nat, 5 ≤ u ∧ 1 ≤ v ∧ x = 2^a*u ∧ y = 1+3^h*v ∧
    (2^(a+1)+1)*u+2*a=2^(h+1)*v+3

private theorem strict_from_equation (a h u v : Nat)
    (hu : 5≤u)
    (he : (2^(a+1)+1)*u+2*a=2^(h+1)*v+3) :
    2^a*u < 1+3^h*v := by
  have hpow : 2^h≤3^h := Nat.pow_le_pow_left (by decide) h
  have hmul : 2^h*v≤3^h*v := Nat.mul_le_mul_right v hpow
  have he' : 2*(2^a*u)+u+2*a=2*(2^h*v)+3 := by
    simpa [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he
  omega

theorem generic_edge_holds (a h x y : Nat) (he : GenericEdge a h x y) :
    Holds (branchParams (a,h)) x y := by
  obtain ⟨u,v,hu,hv,hx,hy,heq⟩ := he
  subst x
  subst y
  exact original_generic_algebra a h u v heq

theorem generic_edge_strict (a h x y : Nat) (he : GenericEdge a h x y) : x < y := by
  obtain ⟨u,v,hu,hv,hx,hy,heq⟩ := he
  subst x
  subst y
  exact strict_from_equation a h u v hu heq

/-- Actual path semantics for a finite list of ordered, nonexceptional branch letters. -/
def GenericWordPath : List (Nat×Nat) → Nat → Nat → Prop
  | [],x,y => x=y
  | b::bs,x,y => ∃ z, GenericEdge b.1 b.2 x z ∧ GenericWordPath bs z y

theorem word_path_of_generic (w : List (Nat×Nat)) (x y : Nat)
    (h : GenericWordPath w x y) : WordPath w x y := by
  induction w generalizing x y with
  | nil => simpa [GenericWordPath,WordPath] using h
  | cons b bs ih =>
      obtain ⟨z,hb,ht⟩ := h
      exact ⟨z,generic_edge_holds b.1 b.2 x z hb,ih z y ht⟩

theorem generic_word_nondecreasing (w : List (Nat×Nat)) (x y : Nat)
    (h : GenericWordPath w x y) : x ≤ y := by
  induction w generalizing x y with
  | nil =>
      have hxy : x=y := h
      omega
  | cons b bs ih =>
      obtain ⟨z,hb,ht⟩ := h
      have hxz : x<z := generic_edge_strict _ _ _ _ hb
      have hzy : z≤y := ih z y ht
      omega

theorem generic_word_strict {w : List (Nat×Nat)} (hw : w ≠ [])
    {x y : Nat} (h : GenericWordPath w x y) : x<y := by
  cases w with
  | nil => contradiction
  | cons b bs =>
      obtain ⟨z,hb,ht⟩ := h
      have hxz : x < z := generic_edge_strict _ _ _ _ hb
      have hzy : z ≤ y := generic_word_nondecreasing bs z y ht
      omega

theorem no_infinite_genuine_generic_word
    (w : List (Nat×Nat)) (hw : w ≠ [])
    (x : Nat → Nat)
    (h : ∀ i, GenericWordPath w (x i) (x (i+1))) : False := by
  apply no_infinite_repeated_word w hw x
  · intro i
    exact word_path_of_generic w (x i) (x (i+1)) (h i)
  · intro i
    exact generic_word_strict hw (h i)

#print axioms generic_edge_strict
#print axioms no_infinite_genuine_generic_word
end SheepPhysicalGeneric
