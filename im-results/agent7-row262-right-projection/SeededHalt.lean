import PrefixWindowNoGo
set_option maxRecDepth 8000
set_option maxHeartbeats 20000000

namespace BB6.Row262.Window

open BB6.Row262

/-- A full physical tape with ten blank nearest-left cells, blank head
    and blank entire right tape. Farther left has a finite nonblank seed. -/
def syntheticSeedLeft : List Bool :=
  List.replicate 10 false ++ [true,false,true,false,false,true,false,true]

def syntheticSeed : Cfg := ⟨0, syntheticSeedLeft, false, []⟩

/-- A real 598-primitive-step halting witness from this nonblank tape. -/
theorem synthetic_seed_halts :
    (run 598 syntheticSeed).st = 5 ∧ (run 598 syntheticSeed).head = true := by
  decide

/-- The actual A/0 + right11 gate exactly two primitive steps earlier. -/
theorem synthetic_seed_reaches_gate :
    (run 596 syntheticSeed).st = 0 ∧
    (run 596 syntheticSeed).head = false ∧
    (trimRight (run 596 syntheticSeed).right).headD false = true ∧
    (trimRight (run 596 syntheticSeed).right).tail.headD false = true := by
  decide

/-- Invariant closure under every A-to-A interval, including multiple
    first returns, with all farther-left physical tape contexts quantified. -/
def AllWindowClosed (k : Nat) (P : List Bool → Bool → List Bool → Prop) : Prop :=
  ∀ (ls : List Bool) (h : Bool) (rs : List Bool) (n : Nat),
    P (windowLeft k ls) h (trimRight rs) →
    (run n ⟨0, ls, h, rs⟩).st = 0 →
    P (windowLeft k (run n ⟨0, ls, h, rs⟩).left)
      (run n ⟨0, ls, h, rs⟩).head
      (trimRight (run n ⟨0, ls, h, rs⟩).right)

/-- Contradiction for a ten-left-cell universally all-return-closed
    predicate: this counterexample uses ONE genuine seeded full-tape run. -/
theorem no_safe_ten_window_all_return
    (P : List Bool → Bool → List Bool → Prop)
    (hblank : P (windowLeft 10 []) false [])
    (hclosed : AllWindowClosed 10 P)
    (hsafe : ∀ ls rs, ¬ P ls false (true :: true :: rs)) : False := by
  have hinit : windowLeft 10 syntheticSeedLeft = windowLeft 10 ([] : List Bool) := by decide
  have hpseed : P (windowLeft 10 syntheticSeedLeft) false (trimRight []) := by
    simpa [hinit, trimRight] using hblank
  let target := run 596 syntheticSeed
  have hreached : P (windowLeft 10 target.left) target.head (trimRight target.right) := by
    exact hclosed syntheticSeedLeft false [] 596 hpseed (by decide)
  have hhead : target.head = false := by decide
  have hright : trimRight target.right = true :: true :: (trimRight target.right).tail.tail := by decide
  rw [hhead, hright] at hreached
  exact hsafe (windowLeft 10 target.left) ((trimRight target.right).tail.tail) hreached

end BB6.Row262.Window

#print axioms BB6.Row262.Window.synthetic_seed_halts
#print axioms BB6.Row262.Window.synthetic_seed_reaches_gate
#print axioms BB6.Row262.Window.no_safe_ten_window_all_return
