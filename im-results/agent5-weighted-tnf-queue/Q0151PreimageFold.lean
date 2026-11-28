import Q0151Preimage

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151PreimageFold
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151Preimage

/-!
A two-mode run-list preimage/fold adjunction: the mask of a suffix of
arbitrary length accepts a mode precisely when the corresponding forward
run automaton ends in a mode accepted by the final mask. This is the
source-independent algebra for the right half of segConcat.
-/

theorem dnext_live (g : Int) (n : Nat) (hg : LiveMode g) :
    LiveMode (dnext g n) := by
  rcases hg with h | h | h
  · subst g
    simp [LiveMode,dnext]
  · subst g
    by_cases h1 : n % 4 = 1
    · simp [LiveMode,dnext,h1]
    · by_cases h0 : n % 4 = 0
      · simp [LiveMode,dnext,h1,h0]
      · by_cases h2 : n % 4 = 2
        · simp [LiveMode,dnext,h1,h0,h2]
        · simp [LiveMode,dnext,h1,h0,h2]
  · subst g
    by_cases h1 : n % 4 = 1
    · simp [LiveMode,dnext,h1]
    · by_cases h0 : n % 4 = 0
      · simp [LiveMode,dnext,h1,h0]
      · by_cases h2 : n % 4 = 2
        · simp [LiveMode,dnext,h1,h0,h2]
        · simp [LiveMode,dnext,h1,h0,h2]

def forward (runs : List Nat) (g : Int) : Int :=
  runs.foldl (fun m n => dnext m n) g

def backward (runs : List Nat) (t : Nat) : Nat :=
  runs.foldr pre t

theorem backward_forward (runs : List Nat) (t : Nat)
    (g : Int) (hg : LiveMode g) :
    maskAccept (backward runs t) g =
      maskAccept t (forward runs g) := by
  induction runs generalizing g with
  | nil => rfl
  | cons n ns ih =>
      change maskAccept (pre n (backward ns t)) g =
        maskAccept t (forward ns (dnext g n))
      rw [mask_pre_mode g n (backward ns t) hg]
      exact ih (dnext g n) (dnext_live g n hg)

#print axioms dnext_live
#print axioms backward_forward
end BB6.Agent5Q0151PreimageFold
