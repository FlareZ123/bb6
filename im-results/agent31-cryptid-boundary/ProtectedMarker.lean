import Lean.Elab.Tactic.Omega
import A1100

namespace CryptidBoundary
set_option maxHeartbeats 5000000
set_option maxRecDepth 1024
set_option linter.unusedSimpArgs false

def attachTail (pad : List Bool) (c : Cfg) : Cfg :=
  { c with l := c.l ++ pad ++ [true,true] }

/-- One-step spatial frame rule: appending a protected far-left suffix does
not affect the machine while at least one earlier left cell remains. -/
theorem step_protected (c : Cfg) (pad : List Bool) (h : c.l ≠ []) :
    step (attachTail pad c) = attachTail pad (step c) := by
  rcases c with ⟨l,hd,rs,st⟩
  cases l with
  | nil => contradiction
  | cons b bs =>
    cases rs with
    | nil =>
      cases hd <;> simp [attachTail,step,goL,goR,List.append_assoc] <;>
        split <;> simp_all [attachTail,goL,goR,List.append_assoc]
    | cons x xs =>
      cases hd <;> simp [attachTail,step,goL,goR,List.append_assoc] <;>
        split <;> simp_all [attachTail,goL,goR,List.append_assoc]

/-- Exact simulation of any prescribed finite pre-marker corridor.
The guard ensures the stripped machine has not reached its left boundary. -/
theorem run_protected (n : Nat) (c : Cfg) (pad : List Bool)
    (h : ∀ t, t < n → (run t c).l ≠ []) :
    run n (attachTail pad c) = attachTail pad (run n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpre : ∀ t, t<n → (run t c).l ≠ [] := by
      intro t ht
      exact h t (by omega)
    have hs : (run n c).l ≠ [] := h n (by omega)
    calc
      run (n+1) (attachTail pad c) =
          step (run n (attachTail pad c)) := by rw [run_add]; rfl
      _ = step (attachTail pad (run n c)) := by rw [ih hpre]
      _ = attachTail pad (step (run n c)) := step_protected _ pad hs
      _ = attachTail pad (run (n+1) c) := by rw [run_add]; rfl

/-- A stripped original-machine left-stack representation before its marker. -/
def markerCore (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false::pairs m, false, ys, 0⟩

theorem marker_small (m : Nat) (ys : List Bool) :
    aBoundary m ys = attachTail [] (markerCore m ys) := by
  simp [aBoundary, attachTail, markerCore, List.append_assoc]

theorem marker_plus_four (m : Nat) (ys : List Bool) :
    aBoundary (m+4) ys = attachTail (pairs 4) (markerCore m ys) := by
  simp [aBoundary, attachTail, markerCore, pairs_add, List.append_assoc]

/-- Both genuine original-machine A-boundary trajectories agree on all
unprotected tape cells while the common stripped run has left cells. -/
theorem coupled_until_marker (n m : Nat) (ys : List Bool)
    (h : ∀ t, t < n → (run t (markerCore m ys)).l ≠ []) :
    run n (aBoundary m ys) = attachTail [] (run n (markerCore m ys)) ∧
    run n (aBoundary (m+4) ys) =
       attachTail (pairs 4) (run n (markerCore m ys)) := by
  constructor
  · rw [marker_small]
    exact run_protected n _ [] h
  · rw [marker_plus_four]
    exact run_protected n _ (pairs 4) h

/-- The far-left sentinel is physically nonzero in every framed state. -/
theorem marker_one (c : Cfg) (pad : List Bool) :
    true ∈ (attachTail pad c).l := by
  simp [attachTail]

/-- An original A-boundary cannot make a physical blank-left return
before, or exactly when, the stripped machine first empties its left list. -/
theorem coupled_no_physical_return (n m : Nat) (ys : List Bool)
    (h : ∀ t, t < n → (run t (markerCore m ys)).l ≠ []) :
    ∀ t, t ≤ n →
      (∀ b, b ∈ (run t (aBoundary m ys)).l → b = false) → False := by
  intro t ht hblank
  have hpre : ∀ u, u < t → (run u (markerCore m ys)).l ≠ [] := by
    intro u hu
    exact h u (by omega)
  have hs := run_protected t (markerCore m ys) [] hpre
  rw [← marker_small m ys] at hs
  rw [hs] at hblank
  have hone := marker_one (run t (markerCore m ys)) []
  have hf := hblank true hone
  cases hf

#print axioms step_protected
#print axioms run_protected
#print axioms coupled_until_marker
#print axioms coupled_no_physical_return
end CryptidBoundary
