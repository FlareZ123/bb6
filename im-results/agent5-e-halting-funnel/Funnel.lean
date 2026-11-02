import Lean.Elab.Tactic.Omega

namespace BB6.EFunnel

/-- Exact standalone copy of DeepMind's certified high-level map. -/
def nextE : Nat × Nat → Option (Nat × Nat)
  | (b, d) =>
    let c := d + 1
    let m := d / 2
    if b > m then
      if b = m + 1 then some (0, 2 * c + 3)
      else if b = m + 2 then some (2, 2 * c + 1)
      else some (b - m - 3, 2 * c + 5)
    else
      let rem := c - 2 * b
      if rem ≤ 2 then some (0, 2 * c + 2)
      else if rem = 3 then none
      else if rem ≤ 6 then some (2 * b + 2, 2 * rem - 7)
      else some (2 * b + 4, rem - 7)

/-- Danger coordinate: a state `(b, 2b + danger n b)` reaches the halt gate after n
surviving accelerated steps, then one halting call. -/
def danger : Nat → Nat → Nat
  | 0, _ => 2
  | n + 1, b => 4*b + 14 + danger n (2*b + 4)

/-- One large-remainder step peels one layer from the synthetic danger family. -/
theorem nextE_danger_succ (n b : Nat) :
    nextE (b, 2*b + danger (n+1) b) =
      some (2*b+4, 2*(2*b+4) + danger n (2*b+4)) := by
  unfold nextE
  have hd : danger (n+1) b = 4*b + 14 + danger n (2*b+4) := rfl
  have hdiv : (2*b + danger (n+1) b) / 2 ≥ b := by
    rw [hd]
    omega
  simp only [show ¬ b > (2*b + danger (n+1) b) / 2 by omega, ↓reduceIte]
  have hrem : (2*b + danger (n+1) b + 1) - 2*b = danger (n+1) b + 1 := by omega
  rw [hrem, hd]
  have h6 : ¬ (4*b + 14 + danger n (2*b+4) + 1 ≤ 2) := by omega
  simp only [h6, ↓reduceIte]
  have h3 : 4*b + 14 + danger n (2*b+4) + 1 ≠ 3 := by omega
  simp only [h3, ↓reduceIte]
  have h6b : ¬ (4*b + 14 + danger n (2*b+4) + 1 ≤ 6) := by omega
  simp only [h6b, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

/-- The base danger state is exactly the high-level halting gate. -/
theorem nextE_danger_zero (b : Nat) : nextE (b, 2*b + danger 0 b) = none := by
  unfold nextE danger
  have hdiv : (2*b + 2) / 2 = b+1 := by omega
  simp only [hdiv]
  simp only [show ¬ b > b+1 by omega, ↓reduceIte]
  have hrem : (2*b + 2 + 1) - 2*b = 3 := by omega
  rw [hrem]
  simp

/-- Forward executor. -/
def run {α : Type} (f : α → Option α) : Nat → α → Option α
  | 0, s => some s
  | n+1, s => (f s).bind (run f n)

/-- First coordinate after n large-remainder steps. -/
def grow : Nat → Nat → Nat
  | 0, b => b
  | n+1, b => grow n (2*b+4)

/-- Exact n-step funnel into the high-level halt gate. -/
theorem run_danger (n b : Nat) :
    run nextE n (b, 2*b + danger n b) =
      some (grow n b, 2*(grow n b) + 2) := by
  induction n generalizing b with
  | zero => simp [run, danger, grow]
  | succ n ih =>
      simp only [run]
      rw [nextE_danger_succ]
      simp only [Option.bind_some]
      rw [ih (2*b+4)]
      rfl

/-- The synthetic family halts on the next call after its n-step funnel. -/
theorem danger_halts (n b : Nat) :
    (run nextE n (b, 2*b + danger n b)).bind nextE = none := by
  rw [run_danger]
  simp only [Option.bind_some]
  exact nextE_danger_zero (grow n b)

/-- A source state with t=0 enters the danger funnel exactly when its reset size matches. -/
theorem source_zero_to_danger (b n : Nat) (h : 4*b+4 = danger n 0) :
    nextE (b, 2*b) = some (0, danger n 0) := by
  unfold nextE
  have hdiv : (2*b) / 2 = b := by omega
  simp only [hdiv, show ¬ b > b by omega, ↓reduceIte]
  have hrem : (2*b+1) - 2*b = 1 := by omega
  rw [hrem]
  simp only [show 1 ≤ 2 by omega, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

/-- A source state with t=1 enters the danger funnel exactly when its reset size matches. -/
theorem source_one_to_danger (b n : Nat) (h : 4*b+6 = danger n 0) :
    nextE (b, 2*b+1) = some (0, danger n 0) := by
  unfold nextE
  have hdiv : (2*b+1) / 2 = b := by omega
  simp only [hdiv, show ¬ b > b by omega, ↓reduceIte]
  have hrem : (2*b+1+1) - 2*b = 2 := by omega
  rw [hrem]
  simp only [show 2 ≤ 2 by omega, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

#print axioms BB6.EFunnel.nextE_danger_succ
#print axioms BB6.EFunnel.nextE_danger_zero
#print axioms BB6.EFunnel.run_danger
#print axioms BB6.EFunnel.danger_halts
#print axioms BB6.EFunnel.source_zero_to_danger
#print axioms BB6.EFunnel.source_one_to_danger
end BB6.EFunnel
