module

public import Agent18BReduction

@[expose] public section

namespace BB6.OneDim
open BReduction

/-- A two-branch affine map that encodes the original parity-memory transducer. -/
def G (z : Nat) : Nat := 3*(z/2)+4+5*(z%2)

def encode (s : Nat × Nat) : Nat := 2*s.2 + 3*s.1

/-- Conjugacy on the actual two-state parity domain. -/
theorem F_enc (p d : Nat) (hp : p ≤ 1) :
    encode (F (p,d)) = G (encode (p,d)) := by
  have hc : p=0 ∨ p=1 := by omega
  rcases hc with rfl | rfl
  · simp only [encode, F, G]
    omega
  · simp only [encode, F, G]
    omega

def iterG : Nat → Nat → Nat
  | 0,z => z
  | n+1,z => iterG n (G z)

theorem conj_iter (n : Nat) (p d : Nat) (hp : p≤1) :
    encode (iterF n (p,d)) = iterG n (encode (p,d)) := by
  induction n generalizing p d with
  | zero => rfl
  | succ n ih =>
      change encode (iterF n (F (p,d))) = iterG n (G (encode (p,d)))
      rw [←F_enc p d hp]
      exact ih (F (p,d)).1 (F (p,d)).2 (bit_F (p,d))

theorem enc_parity (p d : Nat) (hp:p≤1) :
    encode (p,d)%2=p := by
  have hc : p=0 ∨ p=1 := by omega
  rcases hc with rfl | rfl <;> simp [encode]

/-- The scalar index sequence is internally defined without referring to a pair. -/
def scalarA : Nat → Nat
  | 0 => 3
  | n+1 =>
      let z := iterG (scalarA n) 0
      z+9-3*(z%2)

theorem iterG_sample_bit (n : Nat) :
    (iterG (resetA n) 0)%2 = (sample n).1 := by
  have h := conj_iter (resetA n) 0 0 (by omega)
  have h0 : encode (0,0) = 0 := rfl
  rw [h0] at h
  change encode (sample n) = iterG (resetA n) 0 at h
  rw [←h]
  exact enc_parity (sample n).1 (sample n).2 (sample_bit n)

theorem scalarA_eq_resetA (n : Nat) : scalarA n = resetA n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [scalarA, resetA, ih]
      have h := conj_iter (resetA n) 0 0 (by omega)
      have h0 : encode (0,0)=0 := rfl
      rw [h0] at h
      change encode (sample n) = iterG (resetA n) 0 at h
      rw [←h]
      rw [enc_parity (sample n).1 (sample n).2 (sample_bit n)]
      change encode (sample n)+9-3*(sample n).1 = 2*(sample n).2+9
      simp only [encode]
      omega

/-- A complete one-dimensional scalar criterion for the partial three-counter map. -/
theorem raw_criterion_local :
    Halts (3,0,0) ↔ ∃ n : Nat, (iterG (scalarA n) 0)%2=0 := by
  rw [blank_halts_iff_sample_zero]
  constructor
  · rintro ⟨n,h0⟩
    exact ⟨n,by rw [scalarA_eq_resetA,iterG_sample_bit]; exact h0⟩
  · rintro ⟨n,h0⟩
    refine ⟨n, ?_⟩
    rw [scalarA_eq_resetA, iterG_sample_bit] at h0
    exact h0

#print axioms F_enc
#print axioms conj_iter
#print axioms scalarA_eq_resetA
#print axioms raw_criterion_local
end BB6.OneDim
