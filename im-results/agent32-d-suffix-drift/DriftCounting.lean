import Lean

namespace BB6.DriftCounting

variable {S : Type} (a e b : S → Option S) (V : S → Nat)

def pot : Option S → Nat
  | none => 0
  | some s => V s

def alive : Nat → Option S → Nat
  | _, none => 0
  | 0, some _ => 1
  | t+1, some s => alive t (a s) + alive t (e s) + alive t (b s)

def weight : Nat → Option S → Nat
  | _, none => 0
  | 0, some s => V s
  | t+1, some s => weight t (a s) + weight t (e s) + weight t (b s)

def visits : Nat → Option S → Nat
  | _, none => 0
  | 0, some _ => 0
  | t+1, some s => 3^(t+1) + visits t (a s) + visits t (e s) + visits t (b s)

theorem alive_le (t : Nat) (c : Option S) : alive a e b t c ≤ 3^t := by
  induction t generalizing c with
  | zero => cases c <;> simp [alive]
  | succ t ih =>
    cases c with
    | none => simp [alive]
    | some s =>
      simp only [alive, Nat.pow_succ]
      have h₁ := ih (a s)
      have h₂ := ih (e s)
      have h₃ := ih (b s)
      omega

/-- The scaled occupation count includes every active step before t,
    over all words of length t. -/
theorem alive_mul_le_visits (t : Nat) (c : Option S) :
    t * alive a e b t c ≤ visits a e b t c := by
  induction t generalizing c with
  | zero => simp
  | succ t ih =>
    cases c with
    | none => simp [alive, visits]
    | some s =>
      simp only [alive, visits, Nat.succ_mul, Nat.mul_add, Nat.pow_succ]
      have h₁ := ih (a s)
      have h₂ := ih (e s)
      have h₃ := ih (b s)
      have h₄ := alive_le a e b t (a s)
      have h₅ := alive_le a e b t (e s)
      have h₆ := alive_le a e b t (b s)
      -- The initial state contributes one visit per word of length t+1.
      omega

/-- A uniform two-unit ternary drift gives a finite-horizon occupation bound. -/
theorem occupation_bound
    (h : ∀ s, pot V (a s) + pot V (e s) + pot V (b s) + 2 ≤ 3 * V s)
    (t : Nat) (c : Option S) :
    2 * visits a e b t c + 3 * weight a e b V t c ≤ 3^(t+1) * pot V c := by
  induction t generalizing c with
  | zero => cases c <;> simp [visits, weight, pot]
  | succ t ih =>
    cases c with
    | none => simp [visits, weight, pot]
    | some s =>
      have h₁ := ih (a s)
      have h₂ := ih (e s)
      have h₃ := ih (b s)
      have hd := Nat.mul_le_mul_left (3^(t+1)) (h s)
      simp only [Nat.mul_add, ← Nat.mul_assoc] at hd
      simp only [visits, weight, pot]
      rw [show 3^(t+1+1) = 3^(t+1)*3 from Nat.pow_succ 3 (t+1)]
      omega

theorem tail_bound
    (h : ∀ s, pot V (a s) + pot V (e s) + pot V (b s) + 2 ≤ 3 * V s)
    (t : Nat) (c : Option S) :
    2 * (t * alive a e b t c) ≤ 3^(t+1) * pot V c := by
  have hv := Nat.mul_le_mul_left 2 (alive_mul_le_visits a e b t c)
  have hb := occupation_bound a e b V h t c
  omega

#print axioms alive_le
#print axioms alive_mul_le_visits
#print axioms occupation_bound
#print axioms tail_bound
end BB6.DriftCounting
