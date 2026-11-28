import Std
import Q0151MacroSteps

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151ResidueSemantics

/-!
Exact finite-state suffix semantics for the q0-151 macro-language candidate.
The two modes are the grammar's N (false) and P (true), not TM states.
They recognize run lengths; no statement about original-source nonhalting
is implied without a source macro/stack bridge.
-/

def gateStep (mode : Bool) (length : Nat) : Option Bool :=
  if length % 4 = 1 then some mode
  else if length % 4 = 0 then some true
  else if length % 4 = 2 then (if mode then some false else none)
  else none

def gateRun : Bool → List Nat → Option Bool
  | mode, [] => some mode
  | mode, length :: xs =>
      (gateStep mode length).bind (fun mode' => gateRun mode' xs)

theorem gateStep_one (mode : Bool) : gateStep mode 1 = some mode := by
  cases mode <;> rfl

theorem gateRun_units (mode : Bool) (k : Nat) (suffix : List Nat) :
    gateRun mode (List.replicate k 1 ++ suffix) = gateRun mode suffix := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa [List.replicate_succ, gateRun, gateStep_one] using ih

theorem gateRun_insert (mode : Bool) (preRuns suffix : List Nat) (k : Nat) :
    gateRun mode (preRuns ++ List.replicate k 1 ++ suffix) =
      gateRun mode (preRuns ++ suffix) := by
  induction preRuns generalizing mode with
  | nil => simpa using gateRun_units mode k suffix
  | cons length preRuns ih =>
      simp only [List.cons_append, gateRun]
      cases h : gateStep mode length with
      | none => simp [h]
      | some mode' => simpa [h] using ih mode'

structure GateMask where
  acceptsN : Bool
  acceptsP : Bool
  deriving DecidableEq, Repr

def gateMask (xs : List Nat) : GateMask :=
  ⟨(gateRun false xs).isSome, (gateRun true xs).isSome⟩

theorem gateMask_insert (preRuns suffix : List Nat) (k : Nat) :
    gateMask (preRuns ++ List.replicate k 1 ++ suffix) =
      gateMask (preRuns ++ suffix) := by
  simp only [gateMask, gateRun_insert]

def cat (n : Nat) : Nat :=
  if n ≤ 4 then n else 5 + (n - 1) % 4

theorem cat_mod (n : Nat) : cat n % 4 = n % 4 := by
  unfold cat
  split_ifs <;> omega

theorem cat_idempotent (n : Nat) : cat (cat n) = cat n := by
  unfold cat
  split_ifs <;> omega

theorem cat_add (a b : Nat) :
    cat (cat a + cat b) = cat (a + b) := by
  unfold cat
  split_ifs <;> omega

theorem gateStep_cat (mode : Bool) (n : Nat) :
    gateStep mode (cat n) = gateStep mode n := by
  simp only [gateStep, cat_mod]

theorem gateRun_cats (mode : Bool) (xs : List Nat) :
    gateRun mode (xs.map cat) = gateRun mode xs := by
  induction xs generalizing mode with
  | nil => rfl
  | cons length xs ih =>
      simp only [List.map_cons, gateRun, gateStep_cat]
      cases h : gateStep mode length with
      | none => simp [h]
      | some mode' => simpa [h] using ih mode'

theorem gateMask_cats (xs : List Nat) :
    gateMask (xs.map cat) = gateMask xs := by
  simp only [gateMask, gateRun_cats]

theorem gateRun_forbidden_three (mode : Bool) (n : Nat) (xs : List Nat)
    (h : n % 4 = 3) : gateRun mode (n :: xs) = none := by
  simp [gateRun, gateStep, h]

#print axioms gateRun_insert
#print axioms gateMask_insert
#print axioms cat_mod
#print axioms cat_idempotent
#print axioms cat_add
#print axioms gateRun_cats
#print axioms gateMask_cats
#print axioms gateRun_forbidden_three

end BB6.Agent5Q0151ResidueSemantics
