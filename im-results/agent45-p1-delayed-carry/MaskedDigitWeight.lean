import ReverseBlock

namespace BB6.Agent45ReverseBlock

/-- The fixed C++ digit-index masks, shifted to a starting bit offset. -/
def maskedWeight (o B : Nat) : Nat :=
  (B &&& (0xAAAAAAAAAAAAAAAA >>> o)) +
  2*(B &&& (0xCCCCCCCCCCCCCCCC >>> o)) +
  4*(B &&& (0xF0F0F0F0F0F0F0F0 >>> o)) +
  8*(B &&& (0xFF00FF00FF00FF00 >>> o)) +
  16*(B &&& (0xFFFF0000FFFF0000 >>> o)) +
  32*(B &&& (0xFFFFFFFF00000000 >>> o))

private theorem and_split (x y : Nat) : x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2) := by
  have h := Nat.div_add_mod (x &&& y) 2
  rw [Nat.and_div_two] at h
  have hm := Nat.and_mod_two_eq_one (a:=x) (b:=y)
  have hx : x%2=0 ∨ x%2=1 := by omega
  have hy : y%2=0 ∨ y%2=1 := by omega
  have he : (x &&& y)%2 = (x%2)*(y%2) := by
    by_cases hxy : x%2=1 ∧ y%2=1
    · rw [hm.mpr hxy, hxy.1,hxy.2]
    · have hn := fun h => hxy (hm.mp h)
      have hz : (x &&& y)%2=0 := by omega
      rcases hx with hx|hx <;> rcases hy with hy|hy <;> simp [hx,hy,hz] at hxy ⊢
  rw [he] at h
  exact h.symm

private theorem shr_div (x o : Nat) : (x >>> o)/2 = x >>> (o+1) := by
  simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.pow_succ]

private theorem maskIndex : ∀ i : Fin 64, maskedWeight i.val 1 = i.val := by decide

theorem weight_step (o B : Nat) (ho : o<64) :
    maskedWeight o B = 2*maskedWeight (o+1) (B/2) + o*(B%2) := by
  have hi := maskIndex ⟨o,ho⟩
  simp only [maskedWeight] at hi ⊢
  rw [and_split B, and_split B, and_split B, and_split B, and_split B, and_split B]
  simp only [shr_div]
  rw [and_split 1, and_split 1, and_split 1, and_split 1, and_split 1, and_split 1] at hi
  simp at hi
  rcases (show B%2=0 ∨ B%2=1 by omega) with hb|hb <;> simp only [hb, Nat.mul_zero, Nat.zero_mul, Nat.one_mul, Nat.add_zero] <;> omega

/-- The six masks compute the original reverse-block correction without
    a recursive bit traversal. The only enumeration checks 64 mask bits. -/
theorem weight_corr (o k B : Nat) (hk : o+k≤64) (hB : B<2^k) :
    maskedWeight o B + corr k B = (o+k)*B := by
  induction k generalizing o B with
  | zero =>
    have : B=0 := by simpa using hB
    subst B
    simp [maskedWeight,corr]
  | succ k ih =>
    have hh : B/2<2^k := by rw [Nat.pow_succ] at hB; omega
    have he := ih (o+1) (B/2) (by omega) hh
    rw [weight_step o B (by omega),corr]
    have hb := Nat.div_add_mod B 2
    calc
      _ = 2*(maskedWeight (o+1) (B/2)+corr k (B/2)) + (o+k+1)*(B%2) := by simp [Nat.add_mul]; omega
      _ = _ := by rw [he]; rw [show o+1+k=o+(k+1) by omega]; rw [show o+k+1=o+(k+1) by omega]; rw [←Nat.mul_assoc, Nat.mul_comm 2 (o+(k+1)), Nat.mul_assoc, ←Nat.mul_add, hb]

def maskedCandidate (F k X B : Nat) : Option Nat :=
  let C := k*B-maskedWeight 0 B
  if B<2^k ∧ F*B≤X+C ∧ X+C-F*B<F-k then some (X+C-F*B) else none

theorem maskedCandidate_eq (F k X B : Nat) (hk : k≤64) :
    maskedCandidate F k X B = candidate F k X B := by
  by_cases hb : B<2^k
  · have he := weight_corr 0 k B (by omega) hb
    have hC : k*B-maskedWeight 0 B = corr k B := by simp only [Nat.zero_add] at he; omega
    simp [maskedCandidate,candidate,hC]
  · simp [maskedCandidate,candidate,hb]

def maskedFast (F k X : Nat) : Option Nat :=
  match maskedCandidate F k X (X/F) with
  | some r => some r
  | none => maskedCandidate F k X (X/F+1)

theorem maskedFast_eq (F k X : Nat) (hk : k≤64) : maskedFast F k X = fast F k X := by
  simp [maskedFast,fast,maskedCandidate_eq _ _ _ _ hk]

theorem maskedFast_iff_walk (F z : Nat) (ys : List Nat) (r : Nat)
    (hys : ∀ y∈ys, y≤1) (hfit : 2^(ys.length+1)≤F) (hk : ys.length≤64) :
    maskedFast F ys.length (2^ys.length*z+digits ys)=some r ↔ Walk F z ys r := by
  rw [maskedFast_eq _ _ _ hk]
  exact fast_iff_walk F z ys r hys hfit

#print axioms weight_corr
#print axioms maskedCandidate_eq
#print axioms maskedFast_eq
#print axioms maskedFast_iff_walk

end BB6.Agent45ReverseBlock
