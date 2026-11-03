import ReturnLadder
import EscapeRay
import Lean.Elab.Tactic.Omega

/-!
Two closed-form infinite nonhalting root-counter families for BB429's
source-transcribed accelerated map. Each starts from a synthetic root counter,
not from the genuine blank-origin highLevelStart (0,0).
-/
namespace BB429EscapeRoot
open BB429 BB429Escape BB429Ladder BB429ElevenExtension

def rootU (k : Nat) := rayDemand k+rayU k+8
def rootV (k : Nat) := demandV k+rayV k+8

theorem rayU_mod (k : Nat) (hk : 2 ≤ k) : rayU k % 4 = 1 := by
  cases k with
  | zero => omega
  | succ j =>
    cases j with
    | zero => omega
    | succ n => simp only [rayU]; omega

theorem rayU_big (k : Nat) (hk : 3 ≤ k) : 17 ≤ rayU k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hp : 3 ≤ k
    · have h := ih hp
      simp only [rayU]
      omega
    · have hp2 : k = 2 := by omega
      subst k
      decide

theorem rayV_mod (k : Nat) (hk : 1 ≤ k) : rayV k % 4 = 1 := by
  cases k with
  | zero => omega
  | succ n =>
    have ho := vU_odd n
    simp only [rayV]
    omega

theorem rayV_big (k : Nat) (hk : 1 ≤ k) : 17 ≤ rayV k := by
  cases k with
  | zero => omega
  | succ n =>
    have ho := vU_large n
    simp only [rayV]
    omega

theorem rootU_entry (k : Nat) :
    run k (0,rootU k) = some (rayU k,rayU k+8) := by
  have h : rayDemand k ≤ rootU k := by unfold rootU; omega
  have hr := ray_run k (rootU k) h
  have hs : rootU k-rayDemand k = rayU k+8 := by unfold rootU; omega
  simpa only [hs] using hr

theorem rootV_entry (k : Nat) :
    run k (11,rootV k) = some (rayV k,rayV k+8) := by
  have h : demandV k ≤ rootV k := by unfold rootV; omega
  have hr := v_run k (rootV k) h
  have hs : rootV k-demandV k = rayV k+8 := by unfold rootV; omega
  simpa only [hs] using hr

/-- Infinite nonhalting family of root-0 configurations. -/
theorem rootU_never (k n : Nat) (hk : 3 ≤ k) :
    run n (0,rootU k) ≠ none :=
  line_entry_never (0,rootU k) (rayU k) k n
    (rayU_big k hk) (rayU_mod k (by omega)) (rootU_entry k)

/-- Infinite nonhalting family of root-11 configurations. -/
theorem rootV_never (k n : Nat) (hk : 1 ≤ k) :
    run n (11,rootV k) ≠ none :=
  line_entry_never (11,rootV k) (rayV k) k n
    (rayV_big k hk) (rayV_mod k hk) (rootV_entry k)

theorem rayU_pow (k : Nat) : rayU k+3 = 3*2^k := by
  induction k with
  | zero => decide
  | succ n ih =>
    simp only [rayU,Nat.pow_succ]
    omega

theorem rayV_pow (k : Nat) : rayV k+3 = 14*2^k := by
  induction k with
  | zero => decide
  | succ n ih =>
    simp only [rayV,Nat.pow_succ]
    omega

/-- rootU k = 9*2^k - 3*k - 1, with equality stated in Nat. -/
theorem rootU_formula (k : Nat) : rootU k+3*k+1=9*2^k := by
  have hb := ray_balance k
  have hu := rayU_pow k
  unfold rootU
  omega

/-- rootV k = 42*2^k - 3*k - 23, with equality stated in Nat. -/
theorem rootV_formula (k : Nat) : rootV k+3*k+23=42*2^k := by
  have hb := v_balance k
  have hv := rayV_pow k
  unfold rootV
  omega

#print axioms rootU_never
#print axioms rootV_never
#print axioms rootU_formula
#print axioms rootV_formula
end BB429EscapeRoot
