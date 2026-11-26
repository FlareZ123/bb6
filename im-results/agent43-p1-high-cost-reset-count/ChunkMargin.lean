import ChunkProduct
import RunMarginFast

namespace BB6.Agent43P1Complement
open BB6.Agent43ChunkProduct BB6.Agent45.DelayedCarry

/-- Symbolic transfer to the existing packed-window interface: only local
    product checks are evaluated, never the represented global integer. -/
theorem chunkProduct_powRunOK (w k t f : Nat) (xs ys : List Nat)
    (hkw : 2^k≤w) (ht : t≤w*xs.length) (hy : bounded w ys)
    (hc : MulChain w 7 0 xs ys f) (hw : ChunkOK w k t ys) :
    PowRunOK t k (7*join w xs) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and,Nat.testBit_two_pow_sub_one]
    by_cases hi : i<t+1-2^k
    · have h := (product_windows w k t 7 f xs ys hkw ht hy hc hw i (by omega)).1
      rw [(windowOrPow_iff _ _ _).2 h]; simp [hi]
    · simp [hi]
  · apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and,Nat.testBit_two_pow_sub_one]
    by_cases hi : i<t+1-2^k
    · have h := (product_windows w k t 7 f xs ys hkw ht hy hc hw i (by omega)).2
      rw [(windowAndPow_iff _ _ _).2 h]; simp
    · simp [hi]

/-- The huge exponent in the safety bound may be replaced by a fixed,
    numerically checkable lower exponent. -/
theorem chunk_safe (n K k e : Nat) (he : e≤n-2^k)
    (hsmall : (n+K+2)*marginSize n K<6*2^e) :
    (n+K+2)*marginSize n K<6*2^(n-2^k) :=
  Nat.lt_of_lt_of_le hsmall (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_right (by decide : 0<2) he))

/-- Existing original delayed-carry margin obligations, discharged by local
    multiplication and overlapping-window certificates. -/
theorem allBlockMargins_of_chunkProduct (n K s h w k : Nat) (qs : List Prefix)
    (hkw : 2^k≤w) (hgn : 2^k≤n)
    (hsafe : (n+K+2)*marginSize n K<6*2^(n-2^k))
    (hcheck : ∀ C c, (C,c)∈qs → C%2=1 ∧
      ∃ xs ys f, C=join w xs ∧ s+h≤w*xs.length ∧ bounded w ys ∧
        MulChain w 7 0 xs ys f ∧ ChunkOK w k (s+h) ys) :
    AllBlockMargins n K s h qs := by
  apply allBlockMargins_of_powRunOK n K s h k qs hgn hsafe
  intro C c hmem
  obtain ⟨hodd,xs,ys,f,rfl,ht,hy,hc,hw⟩ := hcheck C c hmem
  exact ⟨hodd,chunkProduct_powRunOK w k (s+h) f xs ys hkw ht hy hc hw⟩

#print axioms chunkProduct_powRunOK
#print axioms chunk_safe
#print axioms allBlockMargins_of_chunkProduct
end BB6.Agent43P1Complement
