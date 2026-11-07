import LowTowerFamilies
import Lean.Elab.Tactic.Omega

namespace BB6.Agent5LowTower

/-- A low-branch dyadic stopping gate at inverse depth n.
    The quotient is the r from Agent19's source theorem, so the gate
    is a purely arithmetic predicate on (n,m). -/
def lowTowerGate (n m : Nat) : Prop :=
  2 ≤ n ∧ n % 2 = 0 ∧ n + 4 ≤ m ∧
    (9*m + 13 + 5*2^(n+2)) % 2^(n+4) = 0 ∧
    (9*m + 13 + 5*2^(n+2)) / 2^(n+4) ≤ m

instance (n m : Nat) : Decidable (lowTowerGate n m) := by
  unfold lowTowerGate
  infer_instance

/-- There is a low dyadic stopping depth. The depth is bounded by m
    because the gate itself requires n+4 ≤ m. -/
def lowTowerExcluded (m : Nat) : Prop :=
  ∃ n, lowTowerGate n m

/-- Executable finite scan for the complete low dyadic stopping family. -/
def lowTowerExcludedBool (m : Nat) : Bool :=
  (List.range (m+1)).any (fun n => decide (lowTowerGate n m))

theorem lowTowerExcludedBool_iff (m : Nat) :
    lowTowerExcludedBool m = true ↔ lowTowerExcluded m := by
  simp only [lowTowerExcludedBool, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨n, _, hgate⟩
    exact ⟨n, hgate⟩
  · rintro ⟨n, hgate⟩
    have hn : n < m+1 := by
      rcases hgate with ⟨_, _, hbound, _, _⟩
      omega
    exact ⟨n, hn, hgate⟩

private theorem lowBound (m : Nat) : 3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3 = (2*m+3)+2 := by omega
      rw [he, Nat.pow_add, show (2:Nat)^2=4 by decide]
      omega

/-- Every parameter caught by the all-depth low gate is excluded from
    the authentic Machine C blank section orbit. This is the general
    (all n) form of Agent19's three explicit depth progressions. -/
theorem lowTowerExcluded_no_root (m : Nat) :
    lowTowerExcluded m →
      ¬ BB6.Agent3.CReach 1 (2^(2*m+3)-(3*m+4)) := by
  rintro ⟨n, hn, hne, hm, hmod, hr⟩
  let num := 9*m+13+5*(2:Nat)^(n+2)
  let den := (2:Nat)^(n+4)
  let r := num / den
  have hdiv : den * (num / den) = num := by
    have h := Nat.mod_add_div num den
    rw [hmod] at h
    simpa using h
  have hlin : 9*m+13+5*(2:Nat)^(n+2) = r*2^(n+4) := by
    dsimp [r, num, den]
    calc
      9*m+13+5*2^(n+2) =
          2^(n+4) * ((9*m+13+5*2^(n+2))/2^(n+4)) := by
            simpa using hdiv.symm
      _ = ((9*m+13+5*2^(n+2))/2^(n+4)) * 2^(n+4) := by ac_rfl
  have hstop :
      (2^(2*m+3)-(3*m+4))+3*m+4=2^(2*m+3) :=
    Nat.sub_add_cancel (lowBound m)
  exact BB6.Agent19SixCone.low_linear_stop_no_root n m
    (2^(2*m+3)-(3*m+4)) r hn hne hm
    (by simpa [r, num, den] using hr) hlin hstop

theorem lowTowerExcludedBool_no_root (m : Nat)
    (h : lowTowerExcludedBool m = true) :
    ¬ BB6.Agent3.CReach 1 (2^(2*m+3)-(3*m+4)) :=
  lowTowerExcluded_no_root m ((lowTowerExcludedBool_iff m).mp h)

#guard lowTowerExcludedBool 11 == true
#guard lowTowerExcludedBool 75 == true
#guard lowTowerExcludedBool 112 == false
#guard lowTowerExcludedBool 219 == true
#guard lowTowerExcludedBool 539 == true

#print axioms lowTowerExcludedBool_iff
#print axioms lowTowerExcluded_no_root

end BB6.Agent5LowTower
