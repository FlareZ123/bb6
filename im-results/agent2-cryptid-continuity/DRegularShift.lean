import Lean.Elab.Tactic.Omega
import DRegular

set_option linter.unusedSimpArgs false

namespace BB6.DRegularShift
open DRegular

def bumpInput (s : L) (p : Nat) : L := {s with a := s.a + 3*p}
def bumpOutput (p : Nat) (s : L) : L := {s with a := s.a + 8*p}

/-- The actual eleven-case source-certified regular section model
    is unconditionally affine-equivariant on every a≥2 input:
    adding 3p unary cells changes one defined successor by exactly
    8p cells and preserves the entire suffix or language exit. -/
theorem next_shift (s : L) (h : 2 ≤ s.a) (p : Nat) :
    next (bumpInput s p) = (next s).map (bumpOutput p) := by
  cases s with
  | mk a q b =>
    change 2 ≤ a at h
    have hrem : (a + 3*p) % 3 = a % 3 := by omega
    have hdiv : (a + 3*p) / 3 = a/3+p := by omega
    by_cases c2 : a%3=2
    · by_cases z0 : q=0
      · simp [next, bumpInput, bumpOutput, hrem, hdiv, c2, z0]
        omega
      · by_cases z1 : q=1
        · simp [next, bumpInput, bumpOutput, hrem, hdiv, c2, z0, z1]
          omega
        · simp [next, bumpInput, bumpOutput, hrem, hdiv, c2, z0, z1]
          omega
    · have hge : 3 ≤ a := by omega
      have hsub : (a+3*p)/3 - 1 = (a/3-1)+p := by omega
      by_cases c0 : a%3=0
      · by_cases z0 : q=0
        · simp [next, bumpInput, bumpOutput, hrem, hdiv, hsub, c2, c0, z0]
          omega
        · by_cases b0 : (b+1)%3=0
          · simp [next, bumpInput, bumpOutput, hrem, hdiv, hsub, c2, c0, z0, b0]
            omega
          · by_cases b1 : (b+1)%3=1
            · simp [next, bumpInput, bumpOutput, hrem, hdiv, hsub, c2, c0, z0, b0, b1]
              omega
            · simp [next, bumpInput, bumpOutput, hrem, hdiv, hsub, c2, c0, z0, b0, b1]
              omega
      · by_cases z0 : q=0
        · simp [next, bumpInput, bumpOutput, hrem, hdiv, hsub, c2, c0, z0]
          omega
        · by_cases b0 : b=0
          · simp [next, bumpInput, bumpOutput, hrem, hdiv, hsub, c2, c0, z0, b0]
            omega
          · by_cases b1 : b=1
            · simp [next, bumpInput, bumpOutput, hrem, hdiv, hsub, c2, c0, z0, b0, b1]
            · by_cases b2 : b=2
              · simp [next, bumpInput, bumpOutput, hrem, hdiv, hsub, c2, c0, z0, b0, b1, b2]
                omega
              · simp [next, bumpInput, bumpOutput, hrem, hdiv, hsub, c2, c0, z0, b0, b1, b2]
                omega

def shiftNat (s : L) (d : Nat) : L := {s with a := s.a + d}

theorem next_shift_raw (s : L) (h : 2 ≤ s.a) (p : Nat) :
    next (shiftNat s (3*p)) = (next s).map (fun t => shiftNat t (8*p)) := by
  change next (bumpInput s p) = (next s).map (bumpOutput p)
  exact next_shift s h p

/-- Full 3-adic finite-prefix synchronisation of the ORIGINAL arithmetic
    DRegular.next table. For any k, all 3^k unary lifts have identical
    definedness and identical entire suffix at the k-th checkpoint.
    The terminal unary offset is exactly 8^k*p. This theorem has NO
    shift/equivariance hypothesis and NO numerical cutoff. -/
theorem run_shift (k : Nat) : ∀ (s : L) (p : Nat), Canon s →
    DRegular.run k (shiftNat s (3^k*p)) =
      (DRegular.run k s).map (fun t => shiftNat t (8^k*p)) := by
  induction k with
  | zero =>
    intro s p hs
    simp [shiftNat,DRegular.run]
  | succ k ih =>
    intro s p hs
    have hpower3 : 3^(k+1)*p = 3*(3^k*p) := by
      simp only [Nat.pow_succ]
      ac_rfl
    have hpower8 : 8^(k+1)*p = 8^k*(8*p) := by
      simp only [Nat.pow_succ]
      ac_rfl
    rw [hpower3, hpower8]
    change (next (shiftNat s (3*(3^k*p)))).bind (DRegular.run k) =
      ((next s).bind (DRegular.run k)).map (fun t => shiftNat t (8^k*(8*p)))
    rw [next_shift_raw s hs.1 (3^k*p)]
    cases hnext : next s with
    | none => simp [hnext]
    | some t =>
      have hcanon := DRegular.next_canon s t hs hnext
      have hin : shiftNat t (8*(3^k*p)) = shiftNat t (3^k*(8*p)) := by
        simp only [shiftNat]
        congr 1
        ac_rfl
      simp only [hnext, Option.map_some, Option.bind_some, hin]
      exact ih t (8*p) hcanon

#print axioms next_shift
#print axioms next_shift_raw
#print axioms run_shift
end BB6.DRegularShift
