import BusyBeaver.BB6.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

def haltTower : Nat → Nat
  | 0 => 0
  | k+1 => 2*(haltTower k+1)

def oddTower (q : Nat) : Nat → Nat
  | 0 => 2*q+1
  | k+1 => 2*(oddTower q k+1)

/-- For any k, the collapsed even sweep reaches the halt on the exact
power-of-two family d+2=2^(k+1). -/
theorem scan_haltTower (k b : Nat) : scanEven (haltTower k) b = none := by
  induction k generalizing b with
  | zero => simp [haltTower,scanEven]
  | succ k ih =>
      change scanEven (2*(haltTower k+1)) b = none
      have he : 2*(haltTower k+1) ≠ 0 := by omega
      have hx : (2*(haltTower k+1))/2-1 = haltTower k := by omega
      rw [scanEven]
      simp only [Nat.mul_mod_right, ite_true, if_neg he]
      rw [hx]
      exact ih _

/-- Every odd-tail branch has a closed exact output after k halving steps. -/
theorem scan_oddTower (q k b : Nat) :
    scanEven (oddTower q k) b =
      some (.N (b+oddTower q k+k+3*(q+1))) := by
  induction k generalizing b with
  | zero =>
      cases q with
      | zero => simp [oddTower,scanEven]
      | succ q => simp [oddTower,scanEven]; omega
  | succ k ih =>
      have he : 2*(oddTower q k+1) ≠ 0 := by omega
      have hx : (2*(oddTower q k+1))/2-1 = oddTower q k := by omega
      change scanEven (2*(oddTower q k+1)) b =
        some (.N (b+(2*(oddTower q k+1))+(k+1)+3*(q+1)))
      rw [scanEven]
      simp only [Nat.mul_mod_right, ite_true, if_neg he]
      rw [hx,ih]
      have hd : 2*(oddTower q k+1)/2 = oddTower q k+1 := by omega
      rw [hd]
      simp only [Option.some.injEq, HighLevelState.N.injEq]
      omega

/-- Every natural counter splits into a power-of-two halting tower or a
nonhalting odd-tail tower. This is a complete integer partition. -/
theorem classify_d (d : Nat) :
    (∃ k, d = haltTower k) ∨ (∃ q k, d = oddTower q k) := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
      by_cases hz : d = 0
      · left
        exact ⟨0, by simp [hz, haltTower]⟩
      by_cases he : d % 2 = 0
      · have hl : d/2-1 < d := by omega
        rcases ih (d/2-1) hl with ⟨k,hk⟩ | ⟨q,k,hq⟩
        · left
          refine ⟨k+1, ?_⟩
          simp only [haltTower]
          omega
        · right
          refine ⟨q,k+1, ?_⟩
          simp only [oddTower]
          omega
      · right
        refine ⟨d/2,0, ?_⟩
        simp only [oddTower]
        omega

/-- Complete finite symbolic decision of any single high-level scan: the
power-of-two tower halts; otherwise the positive drift is exactly given. -/
theorem scanEven_classification (d b : Nat) :
    (∃ k, d=haltTower k ∧ scanEven d b=none) ∨
    (∃ q k, d=oddTower q k ∧
       scanEven d b=some (.N (b+d+k+3*(q+1)))) := by
  rcases classify_d d with ⟨k,hk⟩ | ⟨q,k,hq⟩
  · left
    exact ⟨k,hk,by rw [hk]; exact scan_haltTower k b⟩
  · right
    exact ⟨q,k,hq,by rw [hq]; exact scan_oddTower q k b⟩

/-- A complete arithmetic characterization of the exact stopping set. -/
theorem scanEven_none_iff (d b : Nat) :
    scanEven d b = none ↔ ∃ k, d=haltTower k := by
  constructor
  · intro hn
    rcases classify_d d with ⟨k,hk⟩ | ⟨q,k,hq⟩
    · exact ⟨k,hk⟩
    · rw [hq, scan_oddTower] at hn
      contradiction
  · rintro ⟨k,hk⟩
    rw [hk]
    exact scan_haltTower k b

/-- A strict monotonicity property on every surviving high-level return. -/
theorem scanEven_strict (d b e : Nat)
    (h : scanEven d b = some (.N e)) : d < e := by
  rcases classify_d d with ⟨k,hk⟩ | ⟨q,k,hq⟩
  · rw [hk,scan_haltTower] at h
    contradiction
  · rw [hq,scan_oddTower] at h
    cases h
    omega

/-- The published single-counter high-level successor is strictly increasing
whenever it is defined, excluding every nontrivial directed cycle. -/
theorem highLevelNext_strict (d e : Nat)
    (h : highLevelNext (.N d) = some (.N e)) : d<e := by
  exact scanEven_strict d 0 e h

#print axioms scan_haltTower
#print axioms scan_oddTower
#print axioms classify_d
#print axioms scanEven_classification
#print axioms scanEven_none_iff
#print axioms scanEven_strict
#print axioms highLevelNext_strict
end BB6.Agent48.SpaceNeedle
