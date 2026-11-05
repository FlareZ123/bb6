import PosEvenForm

namespace BB6.Agent8Lift
open BB6.Agent1

/-- Exact original accelerated G big-output branch. -/
theorem source_G_big (k c : Nat) (h : 2*k+2 ≤ c) :
    G k c = (4*k+4, c-(2*k+2)) := by
  rw [G]
  simp [show ¬c < 2*k by omega, show ¬c ≤ 2*k+1 by omega]

/-- Complete two-action high-counter doubling, for every even a,c in its regime. -/
theorem source_T_even_double (a c : Nat) (ha : a%2=0)
    (hc : c%2=0) (hlarge : a+10≤c) :
    T a c = some (a+3,c-2) ∧
    T (a+3) (c-2) = some (2*a+12,c-a-10) := by
  have hclow : 2≤c := by omega
  have hpar : (a+3)%2≠0 := by omega
  have hzero : c-2≠0 := by omega
  have hone : c-2≠1 := by omega
  have htwo : c-2≠2 := by omega
  have hthree : c-2≠3 := by omega
  have hk : (a+3)/2+1 = a/2+2 := by omega
  have hbound : 2*((a+3)/2+1)+2 ≤ c-4 := by omega
  constructor
  · simp [T, show c≠0 by omega, show c≠1 by omega, ha]
  · simp only [T, if_neg hzero, if_neg hone, if_neg hpar,
      if_neg htwo, if_neg hthree]
    have hsub : c-2-2 = c-4 := by omega
    rw [hsub, source_G_big _ _ hbound]
    simp only [Option.some.injEq]
    have hev : a=2*(a/2) := by omega
    apply Prod.ext <;> omega

/-- Explicit even left counter after j doubling stages. -/
def E : Nat → Nat
  | 0 => 2
  | j+1 => 2*E j+12

theorem E_even (j : Nat) : E j%2=0 := by
  induction j with
  | zero => decide
  | succ j ih => simp [E]

theorem E_closed (j : Nat) : E j+12=14*2^j := by
  induction j with
  | zero => decide
  | succ j ih =>
      rw [E, Nat.pow_succ]
      omega

/-- Synthetic reset counter that produces even hub (E_j,c+4). -/
def seed : Nat → Nat → Nat
  | 0, c => c+4
  | j+1, c => seed j (c+E j+10)

theorem seed_closed (j c : Nat) :
    seed j c + 2*j + 10 = c+14*2^j := by
  induction j generalizing c with
  | zero => simp [seed]
  | succ j ih =>
      have hp := ih (c+E j+10)
      have he := E_closed j
      simp only [seed, Nat.pow_succ]
      omega

/-- Exact finite-run relation for genuine P1 source T. -/
inductive Run : Nat → Nat → Nat → Nat → Nat → Prop where
  | refl (a c : Nat) : Run 0 a c a c
  | cons (t a c b d x y : Nat) :
      T a c = some (b,d) → Run t b d x y → Run (t+1) a c x y

theorem Run.trans (t u a c b d x y : Nat)
    (hab : Run t a c b d) (hbc : Run u b d x y) :
    Run (t+u) a c x y := by
  induction hab with
  | refl => simpa using hbc
  | cons t a c b d x y ht hrest ih =>
      have hh := Run.cons (t+u) a c b d _ _ ht (ih hbc)
      simpa only [show (t+1)+u=t+u+1 by omega] using hh

/-- Any even precursor (E_j,c+4) is constructible from its explicit
    synthetic reset using exactly 2j defined T actions. -/
theorem synthetic_even_hub (j c : Nat) (hc : c%2=0) :
    Run (2*j) 2 (seed j c) (E j) (c+4) := by
  induction j generalizing c with
  | zero =>
      simp only [Nat.mul_zero, seed, E]
      exact Run.refl 2 (c+4)
  | succ j ih =>
      have hc' : (c+E j+10)%2=0 := by
        have he := E_even j
        omega
      have hp : Run (2*j) 2 (seed j (c+E j+10))
        (E j) (c+E j+14) := by
        simpa only [show c+E j+10+4=c+E j+14 by omega] using
          ih (c+E j+10) hc'
      have he := E_even j
      have heven : (c+E j+14)%2=0 := by omega
      have hlarge : E j+10≤c+E j+14 := by omega
      obtain ⟨ht1,ht2⟩ :=
        source_T_even_double (E j) (c+E j+14) he heven hlarge
      have hr : Run 2 (E j) (c+E j+14) (E (j+1)) (c+4) := by
        have hend : Run 0 (2*E j+12) (c+4) (2*E j+12) (c+4) :=
          Run.refl _ _
        have hfirst : T (E j) (c+E j+14) =
            some (E j+3,c+E j+12) := by
          simpa only [show c+E j+14-2=c+E j+12 by omega] using ht1
        have hsecond : T (E j+3) (c+E j+12) =
            some (2*E j+12,c+4) := by
          have hsub : c+E j+14-2 = c+E j+12 := by omega
          rw [hsub] at ht2
          simpa only [show c+E j+14-(E j)-10=c+4 by omega] using ht2
        simpa only [E] using
          Run.cons 1 (E j) (c+E j+14) (E j+3) (c+E j+12)
            (2*E j+12) (c+4) hfirst
            (Run.cons 0 (E j+3) (c+E j+12) (2*E j+12) (c+4)
              (2*E j+12) (c+4) hsecond hend)
      have hresult := Run.trans (2*j) 2 2 (seed j (c+E j+10))
        (E j) (c+E j+14) (E (j+1)) (c+4) hp hr
      simpa only [seed, show 2*(j+1)=2*j+2 by omega] using hresult

#print axioms source_T_even_double
#print axioms seed_closed
#print axioms synthetic_even_hub
end BB6.Agent8Lift
