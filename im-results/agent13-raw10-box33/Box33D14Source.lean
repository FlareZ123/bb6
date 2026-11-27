import Box33SourceBridge
import Box17AuditCore
import Box33D14Growth
import Box33D14Growth1
import Box33D14Growth23
import Box33D14Growth45
import Box33D14Counter

namespace BB6.Agent13.Box33D14Source
open BB6Coverage
open Box17 (index decode)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

inductive Hard where
  | m0
  | m1
  | m2
  | m3
  | m4
  | m5
  | b0
  | b1
  deriving DecidableEq

def codes : Hard → List (Fin 25)
  | .m0 => [8,24,11,6,1,13,14,17,3,11,4,0]
  | .m1 => [8,14,11,24,1,13,14,17,3,15,4,0]
  | .m2 => [8,24,11,6,1,13,14,17,12,11,4,0]
  | .m3 => [8,24,11,6,1,13,14,17,24,11,4,0]
  | .m4 => [8,10,11,7,1,13,14,17,24,21,4,0]
  | .m5 => [8,10,11,7,1,13,14,17,24,23,4,0]
  | .b0 => [8,0,11,24,1,13,14,17,22,9,19,4]
  | .b1 => [8,0,11,24,1,13,14,17,22,17,19,4]

def table (h : Hard) : Machine := fun s => decode ((codes h).getD (index s).val 0)
def step (h : Hard) (c : C9Pair.Config) : Option C9Pair.Config :=
  match h with
  | .m0 => Box33D14Growth.step c
  | .m1 => Box33D14Growth1.step c
  | .m2 => Box33D14Growth23.step false c
  | .m3 => Box33D14Growth23.step true c
  | .m4 => Box33D14Growth45.step false c
  | .m5 => Box33D14Growth45.step true c
  | .b0 => Box33D14Counter.step false c
  | .b1 => Box33D14Counter.step true c
def localRun (h : Hard) (n : Nat) (c : C9Pair.Config) : Option C9Pair.Config :=
  match h with
  | .m0 => Box33D14Growth.run n c
  | .m1 => Box33D14Growth1.run n c
  | .m2 => Box33D14Growth23.run false n c
  | .m3 => Box33D14Growth23.run true n c
  | .m4 => Box33D14Growth45.run false n c
  | .m5 => Box33D14Growth45.run true n c
  | .b0 => Box33D14Counter.run false n c
  | .b1 => Box33D14Counter.run true n c

theorem localRun_add (h : Hard) (m n : Nat) (c : C9Pair.Config) :
    localRun h (m+n) c = (localRun h m c).bind (localRun h n) := by
  cases h
  · exact Box33D14Growth.run_add m n c
  · exact Box33D14Growth1.run_add m n c
  · exact Box33D14Growth23.run_add false m n c
  · exact Box33D14Growth23.run_add true m n c
  · exact Box33D14Growth45.run_add false m n c
  · exact Box33D14Growth45.run_add true m n c
  · exact Box33D14Counter.run_add false m n c
  · exact Box33D14Counter.run_add true m n c

theorem localRun_one (h : Hard) (c : C9Pair.Config) : localRun h 1 c = step h c := by
  cases h <;> simp [localRun,step,Box33D14Growth.run,Box33D14Growth1.run,Box33D14Growth23.run,Box33D14Growth45.run,Box33D14Counter.run]

abbrev project := Box33Source.project false

theorem map_step (h : Hard) (z : Config) :
    (rawStep (table h) z).map project =
      match table h (readSlot z) with
      | none => none
      | some mv => some (if mv.right then C9Pair.right (Box33Source.q false mv.next) mv.write (project z)
                         else C9Pair.left (Box33Source.q false mv.next) mv.write (project z)) := by
  unfold rawStep
  cases ht : table h (readSlot z) with
  | none => rfl
  | some mv => simp only [Option.map_some,Box33Source.project_applyMove]

theorem project_step (h : Hard) (z : Config) :
    (rawStep (table h) z).map project = step h (project z) := by
  rw [map_step]
  rcases z with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;> cases h <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem project_run (h : Hard) (n : Nat) (z : Config) :
    (run (table h) n z).map project = localRun h n (project z) := by
  induction n with
  | zero => cases h <;> rfl
  | succ n ih =>
    rw [localRun_add h n 1,← ih]
    simp only [run]
    cases ht : run (table h) n z with
    | none => rfl
    | some c =>
      simp only [Option.bind_some,Option.map_some,localRun_one]
      exact project_step h c

theorem never (h : Hard) : NeverHalts (table h) := by
  intro n
  have he := project_run h n blank
  have hn : localRun h n (project blank) ≠ none := by
    cases h
    · exact Box33D14Growth.never_blank n
    · exact Box33D14Growth1.never_blank n
    · exact Box33D14Growth23.never_blank false n
    · exact Box33D14Growth23.never_blank true n
    · exact Box33D14Growth45.never_blank false n
    · exact Box33D14Growth45.never_blank true n
    · exact Box33D14Counter.never_blank false n
    · exact Box33D14Counter.never_blank true n
  cases hr : run (table h) n blank with
  | none =>
    rw [hr] at he
    exact False.elim (hn he.symm)
  | some c => rfl

def partialTable (h : Hard) : PartialMachine := fun s => some (table h s)
theorem compatible_never (h : Hard) (m : Machine) (hm : compatible (partialTable h) m) : NeverHalts m := by
  have he : m = table h := funext fun s => hm s _ rfl
  rw [he]
  exact never h
#print axioms never
#print axioms compatible_never
end BB6.Agent13.Box33D14Source
