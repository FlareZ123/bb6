import Lean.Elab.Tactic.Omega
import ACodeFirstReturn
import CodeHalt

set_option maxHeartbeats 80000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent37CodeHaltFirst

open CryptidBoundary BB6.Agent35 BB6.Agent37CodeHalt
open BB6.CryptidACodeFirstReturn
open BB6.CryptidPrefixFirstReturn

/-- The first physical F/0 return requires *every left cell* to be 0;
    syntactic left-list emptiness is insufficient. -/
def physicalF0 (c : Cfg) : Prop :=
  c.st = 5 ∧ c.h = false ∧ c.l.all (fun b => !b) = true

/-- The 69-step fixed A halting suffix has no physical F/0 event at
    any earlier time, uniformly in the untouched arbitrary left/right tails.
    At t=27 it visits F/0, but there are generated 1s to its left. -/
theorem terminal_no_physical (L ys : List Bool) (t : Nat)
    (ht : t < 69) :
    ¬physicalF0 (run t
      (⟨L,false,BB6.CryptidAHalt.haltWord ++ ys,0⟩ : Cfg)) := by
  intro hp
  have hcases : t=0 ∨
    t=1 ∨
    t=2 ∨
    t=3 ∨
    t=4 ∨
    t=5 ∨
    t=6 ∨
    t=7 ∨
    t=8 ∨
    t=9 ∨
    t=10 ∨
    t=11 ∨
    t=12 ∨
    t=13 ∨
    t=14 ∨
    t=15 ∨
    t=16 ∨
    t=17 ∨
    t=18 ∨
    t=19 ∨
    t=20 ∨
    t=21 ∨
    t=22 ∨
    t=23 ∨
    t=24 ∨
    t=25 ∨
    t=26 ∨
    t=27 ∨
    t=28 ∨
    t=29 ∨
    t=30 ∨
    t=31 ∨
    t=32 ∨
    t=33 ∨
    t=34 ∨
    t=35 ∨
    t=36 ∨
    t=37 ∨
    t=38 ∨
    t=39 ∨
    t=40 ∨
    t=41 ∨
    t=42 ∨
    t=43 ∨
    t=44 ∨
    t=45 ∨
    t=46 ∨
    t=47 ∨
    t=48 ∨
    t=49 ∨
    t=50 ∨
    t=51 ∨
    t=52 ∨
    t=53 ∨
    t=54 ∨
    t=55 ∨
    t=56 ∨
    t=57 ∨
    t=58 ∨
    t=59 ∨
    t=60 ∨
    t=61 ∨
    t=62 ∨
    t=63 ∨
    t=64 ∨
    t=65 ∨
    t=66 ∨
    t=67 ∨
    t=68 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [physicalF0, BB6.CryptidAHalt.haltWord,
    run, step, goL, goR] at hp

/-- The original six-state machine, from a *synthetic* F/0 input with
    arbitrary 10/111 codeword before the certified A halt cylinder,
    encounters no positive-time physical F/0 until it enters halt state6.
    The target endpoint is a genuine first event under the strengthened
    all-zero physical-left predicate. -/
theorem full_code_first_physical_event
    (k : Nat) (ws ys : List Bool) (t : Nat)
    (hpos : 0 < t) (ht : t < codeTime k ws) :
    ¬physicalF0 (run t (codeInput k ws ys)) := by
  let P : Nat := 12*k*k+41*k+32
  let C : Nat := CryptidA.wordCost (4*k+3) ws
  have hprefix :
      run P (codeInput k ws ys) =
        aBoundary (4*k+3)
          (CryptidA.wordCode ws ++ (BB6.CryptidAHalt.haltWord ++ ys)) := by
    dsimp [P, codeInput]
    rw [prefix_A]
    rfl
  have hcode :
      run C (aBoundary (4*k+3)
        (CryptidA.wordCode ws ++ (BB6.CryptidAHalt.haltWord ++ ys))) =
      aBoundary (4*k+3+CryptidA.wordInc ws)
        (BB6.CryptidAHalt.haltWord ++ ys) :=
    a_code_return (4*k+3) ws (BB6.CryptidAHalt.haltWord ++ ys)
  intro hp
  by_cases hbefore : t < P
  · have hF := prefixA_positive_noF k
      (CryptidA.wordCode ws ++ (BB6.CryptidAHalt.haltWord ++ ys))
      t hpos hbefore
    exact hF hp.1
  · have hdecomp : t = P + (t-P) := by omega
    rw [hdecomp, run_add, hprefix] at hp
    by_cases hword : t-P < C
    · have hF := original_word_noF (4*k+3) ws
        (BB6.CryptidAHalt.haltWord ++ ys) (t-P) hword
      exact hF hp.1
    · have hsplit : t-P = C + (t-P-C) := by omega
      rw [hsplit, run_add, hcode] at hp
      have htail : t-P-C < 69 := by
        dsimp [P,C,codeTime] at *
        omega
      have hlocal := terminal_no_physical
        (false :: pairs (4*k+3+CryptidA.wordInc ws) ++ [true,true])
        ys (t-P-C) htail
      exact hlocal (by simpa only [aBoundary] using hp)

#print axioms terminal_no_physical
#print axioms full_code_first_physical_event
end BB6.Agent37CodeHaltFirst
