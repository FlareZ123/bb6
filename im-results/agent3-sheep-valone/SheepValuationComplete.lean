import Std
namespace SheepValuationComplete

inductive Step : Nat → Nat → Prop where
  | special (a : Nat) : Step (3*2^a) (3*2^a+a+3)
  | generic (a u : Nat) (odd : u%2=1) (large : 5≤u) :
      Step (2^a*u) (2^a*u+a+(u-1)/2)

/-- For every w≥2 the genuine generic Sheep section step is already even. -/
theorem generic_one (w : Nat) (hw : 2≤w) :
    Step (2*(2*w+1)) (5*w+3) := by
  have ho : (2*w+1)%2=1 := by omega
  have hl : 5≤2*w+1 := by omega
  have h := Step.generic 1 (2*w+1) ho hl
  have heq : 2*(2*w+1)+1+((2*w+1)-1)/2 = 5*w+3 := by omega
  simpa only [show (2:Nat)^1=2 by decide, heq] using h

/-- Explicit quotient of (16^q - 1)/5 without division. -/
def S : Nat → Nat
  | 0 => 0
  | q+1 => 16*S q+3

theorem S_power (q : Nat) : 5*S q+1=16^q := by
  induction q with
  | zero => decide
  | succ q ih =>
      simp only [S, Nat.pow_succ]
      omega

theorem S_succ_ge (q : Nat) : 3≤S (q+1) := by
  simp only [S]
  omega

theorem pow_four (q r : Nat) : 2^(4*q+r) = 16^q * 2^r := by
  rw [Nat.pow_add, Nat.pow_mul]

/-- From v2=1, a single section step reaches exactly valuation 4q. -/
theorem step_mod0 (q : Nat) (hq : 1≤q) :
    Step (2*(2*(3*S q)+1)) (2^(4*q)*3) := by
  have hs : 3≤S q := by
    cases q with
    | zero => omega
    | succ k => exact S_succ_ge k
  have h := generic_one (3*S q) (by omega)
  have hs0 := S_power q
  have hp := pow_four q 0
  simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one] at hp
  have heq : 5*(3*S q)+3 = 2^(4*q)*3 := by
    rw [hp]
    omega
  rw [heq] at h
  exact h

/-- From v2=1, a single section step reaches exactly valuation 4q+1. -/
theorem step_mod1 (q : Nat) :
    Step (2*(2*(18*S q+3)+1)) (2^(4*q+1)*9) := by
  have h := generic_one (18*S q+3) (by omega)
  have hs := S_power q
  have hp := pow_four q 1
  simp only [show (2:Nat)^1=2 by decide] at hp
  have heq : 5*(18*S q+3)+3 = 2^(4*q+1)*9 := by
    rw [hp]
    omega
  rw [heq] at h
  exact h

/-- From v2=1, a single section step reaches exactly valuation 4q+2. -/
theorem step_mod2 (q : Nat) :
    Step (2*(2*(28*S q+5)+1)) (2^(4*q+2)*7) := by
  have h := generic_one (28*S q+5) (by omega)
  have hs := S_power q
  have hp := pow_four q 2
  simp only [show (2:Nat)^2=4 by decide] at hp
  have heq : 5*(28*S q+5)+3 = 2^(4*q+2)*7 := by
    rw [hp]
    omega
  rw [heq] at h
  exact h

/-- From v2=1, a single section step reaches exactly valuation 4q+3. -/
theorem step_mod3 (q : Nat) :
    Step (2*(2*(88*S q+17)+1)) (2^(4*q+3)*11) := by
  have h := generic_one (88*S q+17) (by omega)
  have hs := S_power q
  have hp := pow_four q 3
  simp only [show (2:Nat)^3=8 by decide] at hp
  have heq : 5*(88*S q+17)+3 = 2^(4*q+3)*11 := by
    rw [hp]
    omega
  rw [heq] at h
  exact h

/-- Every positive target valuation is attained from valuation-one section inputs. -/
theorem all_target_valuations (b : Nat) (hb : 1≤b) :
    ∃ w c, 2≤w ∧ c%2=1 ∧ Step (2*(2*w+1)) (2^b*c) := by
  let q := b/4
  have hdiv : b = 4*q+b%4 := by
    dsimp [q]
    omega
  have hr : b%4=0 ∨ b%4=1 ∨ b%4=2 ∨ b%4=3 := by omega
  rcases hr with h0|h1|h2|h3
  · have hbq : 1≤q := by omega
    have h := step_mod0 q hbq
    refine ⟨3*S q, 3, ?_, by decide, ?_⟩
    · have hp : 16 ≤ 16^q := by
        have hpow := Nat.pow_le_pow_right (n:=16) (by decide) hbq
        simpa only [show (16:Nat)^1=16 by decide] using hpow
      have hs : 3 ≤ S q := by
        have hpow := S_power q
        omega
      omega
    · have hbeq : b = 4*q := by omega
      rw [hbeq]
      exact h
  · have h := step_mod1 q
    refine ⟨18*S q+3, 9, by omega, by decide, ?_⟩
    have hbeq : b = 4*q + 1 := by omega
    rw [hbeq]
    exact h
  · have h := step_mod2 q
    refine ⟨28*S q+5, 7, by omega, by decide, ?_⟩
    have hbeq : b = 4*q + 2 := by omega
    rw [hbeq]
    exact h
  · have h := step_mod3 q
    refine ⟨88*S q+17, 11, by omega, by decide, ?_⟩
    have hbeq : b = 4*q + 3 := by omega
    rw [hbeq]
    exact h

/-- No global predicate depending only on the positive 2-adic valuation
    can contain the authentic seed valuation 1, be forward inductive under
    every legal generic even section return, and omit any target valuation. -/
theorem valuation_only_invariant_full (P : Nat → Prop)
    (hone : P 1)
    (hclosed : ∀ (a b u v : Nat), 1 ≤ a → u%2=1 → 5≤u →
        v%2=1 → Step (2^a*u) (2^b*v) → P a → P b) :
    ∀ b, 1≤b → P b := by
  intro b hb
  obtain ⟨w,c,hw,hc,hstep⟩ := all_target_valuations b hb
  have hu : (2*w+1)%2=1 := by omega
  have hlarge : 5≤2*w+1 := by omega
  have hs : Step (2^1*(2*w+1)) (2^b*c) := by
    simpa only [show (2:Nat)^1=2 by decide] using hstep
  exact hclosed 1 b (2*w+1) c (by decide) hu hlarge hc hs hone

#print axioms valuation_only_invariant_full

#print axioms all_target_valuations
end SheepValuationComplete
