import Generic
import Boundary

namespace BB6.BoundaryPadding
open BB6.Padding

/-- The D-start Cryptid transition table, including explicit state-6 halt. -/
def delta : Nat → Bool → Option Instr
 | 0,false => some (true, Dir.right, 1)
 | 0,true  => some (false, Dir.right, 4)
 | 1,false => some (true, Dir.left, 2)
 | 1,true  => some (false, Dir.right, 0)
 | 2,false => some (true, Dir.left, 0)
 | 2,true  => some (true, Dir.left, 3)
 | 3,false => some (true, Dir.left, 2)
 | 3,true  => some (true, Dir.left, 5)
 | 4,false => some (false, Dir.left, 2)
 | 4,true  => some (false, Dir.left, 1)
 | 5,false => some (true, Dir.left, 4)
 | 5,true  => some (true, Dir.stay, 6)
 | _,_ => none

def represent (c : CryptidBoundary.Cfg) : Config :=
  ⟨c.l, c.h, c.r, c.st⟩

/-- Left/right halves represent identical infinite blank-extended tapes. -/
def ObsEq (c d : CryptidBoundary.Cfg) : Prop :=
  CfgEq (represent c) (represent d)

/-- Exact original-source semantics in the generic machine model. -/
theorem source_step (c : CryptidBoundary.Cfg) :
  represent (CryptidBoundary.step c) = step delta (represent c) := by
  rcases c with ⟨left, bit, right, st⟩
  rcases st with _ | _ | _ | _ | _ | _ | _ | st <;>
    cases bit <;> cases left <;> cases right <;>
    rfl

theorem source_run (n : Nat) (c : CryptidBoundary.Cfg) :
  represent (CryptidBoundary.run n c) = run delta n (represent c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CryptidBoundary.run_add n 1]
    change represent (CryptidBoundary.step (CryptidBoundary.run n c)) = _
    rw [source_step, ih]
    rfl

/-- Exact physical-tape bisimulation for the original raw Cryptid machine. -/
theorem source_congr (n : Nat) {c d : CryptidBoundary.Cfg}
    (h : ObsEq c d) :
    ObsEq (CryptidBoundary.run n c) (CryptidBoundary.run n d) := by
  change CfgEq (represent (CryptidBoundary.run n c))
    (represent (CryptidBoundary.run n d))
  rw [source_run, source_run]
  exact run_congr delta n h

/-- Explicit zero padding at either far tape end cannot change the physical
    machine trajectory at any finite time. -/
theorem source_pad (n p q : Nat) (c : CryptidBoundary.Cfg) :
    ObsEq (CryptidBoundary.run n c)
      (CryptidBoundary.run n
        ⟨c.l ++ List.replicate p false, c.h,
         c.r ++ List.replicate q false, c.st⟩) := by
  apply source_congr
  exact ⟨tapeEq_pad _ _, rfl, tapeEq_pad _ _, rfl⟩

/-- Compose original-source certificates modulo physically irrelevant far blanks. -/
theorem source_chain (n m : Nat) (c middle target : CryptidBoundary.Cfg)
    (first : ObsEq (CryptidBoundary.run n c) middle)
    (second : ObsEq (CryptidBoundary.run m middle) target) :
    ObsEq (CryptidBoundary.run (n+m) c) target := by
  rw [CryptidBoundary.run_add]
  exact cfgEq_trans (source_congr m first) second

/-- Transfer any exact original-machine macro across equivalent representations. -/
theorem source_transport (n : Nat) (c c2 d d2 : CryptidBoundary.Cfg)
    (hinput : ObsEq c c2) (hexact : CryptidBoundary.run n c = d)
    (houtput : ObsEq d d2) : ObsEq (CryptidBoundary.run n c2) d2 := by
  apply cfgEq_trans (source_congr n (cfgEq_symm hinput))
  rw [hexact]
  exact houtput

#print axioms source_chain
#print axioms source_transport
/-- Initial F-section tapes can be padded with any number of blank cells. -/
theorem source_init_pad (n q : Nat) (xs : List Bool) :
    ObsEq (CryptidBoundary.run n (CryptidBoundary.init xs))
      (CryptidBoundary.run n
        (CryptidBoundary.init (xs ++ List.replicate q false))) := by
  apply source_congr
  exact ⟨tapeEq_refl _, rfl,
    tapeEq_cons true (tapeEq_cons true (tapeEq_pad xs q)), rfl⟩

/-- Exact halting equivalence for all explicitly padded initial configurations. -/
theorem source_init_halt_iff (n q : Nat) (xs : List Bool) :
    (CryptidBoundary.run n (CryptidBoundary.init xs)).st = 6 ↔
    (CryptidBoundary.run n
      (CryptidBoundary.init (xs ++ List.replicate q false))).st = 6 := by
  have h := (source_init_pad n q xs).2.2.2
  change (CryptidBoundary.run n (CryptidBoundary.init xs)).st =
    (CryptidBoundary.run n
      (CryptidBoundary.init (xs ++ List.replicate q false))).st at h
  constructor
  · intro hs
    rw [← h]
    exact hs
  · intro hs
    rw [h]
    exact hs

#print axioms source_init_pad
#print axioms source_init_halt_iff
#print axioms source_step
#print axioms source_run
#print axioms source_congr
#print axioms source_pad
end BB6.BoundaryPadding
