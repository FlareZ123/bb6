import PrefixDrift
import EntryControlAudit

namespace BB6Coverage

/-- Complete a partial table by placing genuine halt outcomes in the
    unassigned rows. This is a proof witness, never a machine-pruning rule. -/
def oneTurnWitness (p : PartialMachine) : Machine :=
  fun slot => (p slot).getD none

theorem oneTurnWitness_compatible (p : PartialMachine) :
    compatible p (oneTurnWitness p) := by
  intro slot t hp
  simp [oneTurnWitness, hp]

/-- A particularly reusable genuine-root prefix-ray lemma. From the true
    blank A-root, A/0 writes zero and moves in some direction to a state q.
    If the assigned q-subgraph has an opposite-direction closed fresh-ray
    certificate, the machine never halts. The theorem covers arbitrary
    further state transitions, arbitrary writes on the ray, and all
    completions of the still-free table slots. -/
theorem oneTurnRay_cover (p : PartialMachine) (q : Fin 6) (dir : Bool)
    (states : Fin 6 → Prop) (B : Nat)
    (hA : p initialSlot = some (some ⟨false, dir, q⟩))
    (hq : states q)
    (hclosed : PartialDriftClosed p states (!dir)) :
    Cover (DecidedBelow B) p := by
  let w := oneTurnWitness p
  let a : Move := ⟨false, dir, q⟩
  let c := applyMove blank a
  have hw : compatible p w := oneTurnWitness_compatible p
  have hwa : w initialSlot = some a := by
    simpa [w, a, oneTurnWitness, hA]
  have hentry : run w 1 blank = some c := by
    change (w initialSlot).map (applyMove blank) = some c
    rw [hwa]
    rfl
  have hknown :
      ∀ i, i < 1 → ∀ d, run w i blank = some d →
        p (readSlot d) = some (w (readSlot d)) := by
    intro i hi d hd
    have hi0 : i = 0 := by omega
    subst i
    have hd0 : d = blank := by
      have hs : some blank = some d := by simpa [run] using hd
      exact (Option.some.inj hs).symm
    subst d
    change p initialSlot = some (w initialSlot)
    rw [hA, hwa]
    rfl
  have hblank : ∀ x, Ahead (!dir) c.head x → c.tape x = false := by
    intro x _
    by_cases hx : x = 0 <;> simp [c, applyMove, blank, a, hx]
  exact prefix_drift_cover p w states (!dir) 1 c B
    hw hknown hentry hq hblank hclosed

#print axioms oneTurnWitness_compatible
#print axioms oneTurnRay_cover

end BB6Coverage
