import Lean
namespace BB6.Agent12ReverseAverage

/-- Inverse bit dynamics: all lanes update simultaneously, the terminal
    lane is pinned. The division is natural-number floor. -/
def pass (c : Nat → Nat) (endpoint : Nat) (prev : Nat → Nat) : Nat → Nat
  | 0 => endpoint
  | j+1 => (prev j+c j)/2

def iterate (c : Nat → Nat) (endpoint : Nat) (init : Nat → Nat) : Nat → Nat → Nat
  | 0 => init
  | w+1 => pass c endpoint (iterate c endpoint init w)

/-- If an integer trace exists and the initial guesses are bounded above it,
    the simultaneous inverse update halves the error at every lane. The
    number of iterations needed depends on the value width, not trace length. -/
theorem error_bound (c target init : Nat → Nat) (N U w : Nat)
    (hstep : ∀ j<N, 2*target (j+1)=target j+c j)
    (hinit : ∀ j≤N, target j≤init j ∧ init j≤target j+U) :
    ∀ j≤N, target j≤iterate c (target 0) init w j ∧
      iterate c (target 0) init w j≤target j+U/2^w := by
  induction w with
  | zero => simpa [iterate] using hinit
  | succ w ih =>
    intro j hj
    cases j with
    | zero => simp [iterate,pass]
    | succ j =>
      obtain ⟨hl,hu⟩:=ih j (by omega)
      have ht:=hstep j (by omega)
      have he : U/2^(w+1)=U/2^w/2 := by rw [Nat.div_div_eq_div_mul,Nat.pow_succ]
      simp only [iterate,pass,he]
      omega

theorem exact_after_width (c target init : Nat → Nat) (N U w : Nat)
    (hstep : ∀ j<N, 2*target (j+1)=target j+c j)
    (hinit : ∀ j≤N, target j≤init j ∧ init j≤target j+U)
    (hU : U<2^w) (j : Nat) (hj : j≤N) :
    iterate c (target 0) init w j=target j := by
  obtain ⟨hl,hu⟩:=error_bound c target init N U w hstep hinit j hj
  rw [Nat.div_eq_of_lt hU] at hu
  omega

#print axioms error_bound
#print axioms exact_after_width
end BB6.Agent12ReverseAverage
