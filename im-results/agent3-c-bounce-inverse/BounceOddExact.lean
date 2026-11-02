import BounceInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Reverse odd-bounce middle-counter recursion. -/
def oddLiftK (K : Nat) : Nat → Nat
  | 0 => K
  | n+1 => oddLiftK (2*K+3) n

/-- Reverse odd-bounce height recursion, with terminal right counter y. -/
def oddLiftC (K : Nat) : Nat → Nat → Nat
  | 0,y => y
  | n+1,y => 2*K+3+oddLiftC (2*K+3) n y

theorem oddLiftC_lower (K n y : Nat) : y≤oddLiftC K n y := by
  induction n generalizing K with
  | zero => simp [oddLiftC]
  | succ n ih =>
    simp only [oddLiftC]
    have hh := ih (2*K+3)
    omega

theorem oddLiftK_odd (K n : Nat) (hK:K%2=1) :
    (oddLiftK K n)%2=1 := by
  induction n generalizing K with
  | zero => simpa [oddLiftK] using hK
  | succ n ih => simpa only [oddLiftK] using ih (2*K+3) (by omega)

theorem oddLiftK_closed (K n : Nat) :
    oddLiftK K n +3=2^n*(K+3) := by
  induction n generalizing K with
  | zero => simp [oddLiftK]
  | succ n ih =>
    simp only [oddLiftK, Nat.pow_succ]
    calc
      oddLiftK (2*K+3) n +3 = 2^n*(2*K+3+3) := ih (2*K+3)
      _ = 2^n*(2*(K+3)) := by congr 1 <;> omega
      _ = 2^n*2*(K+3) := by ac_rfl

theorem oddLiftC_closed (K n y : Nat) :
    oddLiftC K n y+2*(K+3)+3*n = y+2^(n+1)*(K+3) := by
  induction n generalizing K with
  | zero => simp [oddLiftC]
  | succ n ih =>
    simp only [oddLiftC]
    have hh := ih (2*K+3)
    have hp : 2^(n+1)*(2*K+3+3) = 2^(n+1+1)*(K+3) := by
      rw [Nat.pow_succ, Nat.pow_succ]
      calc
        2^n*2*(2*K+3+3) = 2^n*2*(2*(K+3)) := by congr 1 <;> omega
        _ = 2^n*2*2*(K+3) := by ac_rfl
    rw [hp] at hh
    omega

/-- Every syntactically reverse-constructed odd bounce follows the original
    recursive source, for arbitrary recursion depth n. -/
theorem odd_bounce_lift (K n y : Nat) (hK : K%2=1) (hy : 4≤y) :
    (bounce K (oddLiftC K n y)).2=(bounce (oddLiftK K n) y).2 := by
  induction n generalizing K with
  | zero => simp [oddLiftC,oddLiftK]
  | succ n ih =>
    have hC : 4≤oddLiftC (2*K+3) n y := by
      have hh := oddLiftC_lower (2*K+3) n y
      omega
    have hlow : ¬(2*K+3+oddLiftC (2*K+3) n y<4) := by omega
    have hhigh : ¬(2*K+3+oddLiftC (2*K+3) n y≤2*K+6) := by omega
    simp only [oddLiftC,oddLiftK]
    rw [bounce]
    simp only [if_neg hlow,if_pos hK,if_neg hhigh]
    have hsub : 2*K+3+oddLiftC (2*K+3) n y-(2*K+3)=
        oddLiftC (2*K+3) n y := by omega
    rw [hsub]
    exact ih (2*K+3) (by omega)

theorem odd_bounce_direct (K y : Nat) (hK : K%2=1) (hy : 4≤y)
    (hu : y≤2*K+6) :
    (bounce K y).2=some (2*K+6-y,y) := by
  have hlow : ¬y<4 := by omega
  simp [bounce,hlow,hK,hu]

/-- Converse to the previously known invariant: two power-cost equations
    characterize genuine odd-bounce success for every possible depth. -/
theorem odd_bounce_sufficient (K c x y n : Nat) (hK : K%2=1)
    (hy : 4≤y) (hs : x+y=2^n*(2*K+6))
    (hc : c+(2*K+6)+3*n=x+2*y) :
    (bounce K c).2=some (x,y) := by
  have hpow : 2^(n+1)*(K+3)=x+y := by
    calc
      2^(n+1)*(K+3)=2^n*2*(K+3) := by rw [Nat.pow_succ]
      _ = 2^n*(2*(K+3)) := by ac_rfl
      _ = 2^n*(2*K+6) := by congr 1 <;> omega
      _ = x+y := hs.symm
  have hin : oddLiftC K n y=c := by
    have hh := oddLiftC_closed K n y
    rw [hpow] at hh
    omega
  rw [←hin]
  rw [odd_bounce_lift K n y hK hy]
  have hko := oddLiftK_odd K n hK
  have hz : 2*(oddLiftK K n)+6=2^n*(2*K+6) := by
    have hh := oddLiftK_closed K n
    calc
      2*(oddLiftK K n)+6=2*(2^n*(K+3)) := by omega
      _ = 2^n*(2*(K+3)) := by ac_rfl
      _ = 2^n*(2*K+6) := by congr 1 <;> omega
  have hbound : y≤2*(oddLiftK K n)+6 := by omega
  rw [odd_bounce_direct (oddLiftK K n) y hko hy hbound]
  have hx : 2*(oddLiftK K n)+6-y=x := by omega
  simp [hx]

/-- Full exact iff for the original odd-middle bounce, y>=4. -/
theorem bounce_odd_output_exact (K c x y : Nat)
    (hK : K%2=1) (hy : 4≤y) :
    (bounce K c).2=some (x,y) ↔
    ∃ n : Nat, x+y=2^n*(2*K+6) ∧
      c+(2*K+6)+3*n=x+2*y := by
  constructor
  · exact bounce_odd_output_invariants c K x y hK
  · rintro ⟨n,hs,hc⟩
    exact odd_bounce_sufficient K c x y n hK hy hs hc

#print axioms odd_bounce_sufficient
#print axioms bounce_odd_output_exact
end BB6.Agent46
