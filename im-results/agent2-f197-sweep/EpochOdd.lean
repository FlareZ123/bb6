import EpochCycle
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace F197.MixedCarry
open JCarry

/-- Finite schedules for both parity entrances and the odd-parity bulk cycle.
Each schedule is checked by the existing suffix-parametric certificate theorem. -/
def oddW : Word := [false,false,false,true,false,true,false,true,false,false,false,true,true,false,false,false,true]
def entryEvenPrefix : Word := [false,false,false,true,false,true,false,true,false,true,false,false,false,true]
def entryEvenInput : Word := entryEvenPrefix ++ [false,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,true,false,false,false,true]
def entryEvenSchedule : List Instr := [
  ⟨[], false, 1⟩,
  ⟨[.q,.at,.at], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.at,.at], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.at,.p], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.at], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.at,.q,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p,.p,.p], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p,.p,.tt], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p,.q], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.at], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p,.at,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p,.at,.p], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p,.at], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p,.at,.tt], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p,.p,.at], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p,.p,.p], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p,.p,.q,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.tt,.p], true, 0⟩]
def entryEvenRows := mkRows entryEvenInput entryEvenSchedule

theorem entryEvenOK : certOK entryEvenInput entryEvenRows = true := by decide

theorem entryEven (n : Nat) (l : Tape) (hl : l 0 = true) :
    run (68*n*76+109618) (b (leadP n (tapeOf entryEvenInput l)) e) =
      some (b (leadP (n+38) (tapeOf cycleW l)) e) := by
  have he : certEnd entryEvenInput entryEvenRows = cycleW := by decide
  have hd : certDelta entryEvenRows = 38 := by decide
  have hk : entryEvenRows.length = 76 := by decide
  have hc : certCost entryEvenRows = 109618 := by decide
  have H := cert_sound entryEvenInput entryEvenRows entryEvenOK n l hl
  rw [he,hd,hk,hc] at H
  exact H

#print axioms entryEven

def entryOddPrefix : Word := [false,false,false,true,false,true,false,false,true,false,false,true,false,true,false,false,false,true]
def entryOddInput : Word := entryOddPrefix ++ [false,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,true,false,false,false,true]
def entryOddSchedule : List Instr := [
  ⟨[], false, 1⟩,
  ⟨[.q,.p,.p,.at], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p,.p,.at], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p,.p,.p], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p,.p,.q,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.tt,.p], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩]
def entryOddRows := mkRows entryOddInput entryOddSchedule

theorem entryOddOK : certOK entryOddInput entryOddRows = true := by decide

theorem entryOdd (n : Nat) (l : Tape) (hl : l 0 = true) :
    run (68*n*28+17584) (b (leadP n (tapeOf entryOddInput l)) e) =
      some (b (leadP (n+14) (tapeOf oddW l)) e) := by
  have he : certEnd entryOddInput entryOddRows = oddW := by decide
  have hd : certDelta entryOddRows = 14 := by decide
  have hk : entryOddRows.length = 28 := by decide
  have hc : certCost entryOddRows = 17584 := by decide
  have H := cert_sound entryOddInput entryOddRows entryOddOK n l hl
  rw [he,hd,hk,hc] at H
  exact H

#print axioms entryOdd

def oddCyclePrefix : Word := [false,false,false,true,false,true,false,true,false,false,false,true,true,false,false,false,true]
def oddCycleInput : Word := oddCyclePrefix ++ [false,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,true,false,false,false,true,false,false,true,false,false,false,true]
def oddCycleSchedule : List Instr := [
  ⟨[], false, 1⟩,
  ⟨[.q,.at], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.at,.tt], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p,.at], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p,.p], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p,.q,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.tt,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.at,.p], true, 0⟩]
def oddCycleRows := mkRows oddCycleInput oddCycleSchedule

theorem oddCycleOK : certOK oddCycleInput oddCycleRows = true := by decide

theorem oddCycle (n : Nat) (l : Tape) (hl : l 0 = true) :
    run (68*n*36+26828) (b (leadP n (tapeOf oddCycleInput l)) e) =
      some (b (leadP (n+18) (tapeOf oddW l)) e) := by
  have he : certEnd oddCycleInput oddCycleRows = oddW := by decide
  have hd : certDelta oddCycleRows = 18 := by decide
  have hk : oddCycleRows.length = 36 := by decide
  have hc : certCost oddCycleRows = 26828 := by decide
  have H := cert_sound oddCycleInput oddCycleRows oddCycleOK n l hl
  rw [he,hd,hk,hc] at H
  exact H

#print axioms oddCycle

def oddRepeat : Nat → Tape → Tape
  | 0,l => l
  | k+1,l => tapeOf cycleR4 (oddRepeat k l)

def oddSum : Nat → Nat → Nat
  | _,0 => 0
  | n,k+1 => (68*n*36+26828) + oddSum (n+18) k

theorem oddRepeat_first (k : Nat) (l : Tape) (hl : l 0 = true) : oddRepeat k l 0 = true := by
  cases k with
  | zero => exact hl
  | succ k => rfl

theorem oddCycle_many (n k : Nat) (l : Tape) (hl : l 0 = true) :
    run (oddSum n k) (b (leadP n (tapeOf oddW (oddRepeat k l))) e) =
      some (b (leadP (n+18*k) (tapeOf oddW l)) e) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    change run ((68*n*36+26828) + oddSum (n+18) k)
      (b (leadP n (tapeOf oddW (tapeOf cycleR4 (oddRepeat k l)))) e) = _
    have hs : tapeOf oddCycleInput (oddRepeat k l) =
        tapeOf oddW (tapeOf cycleR4 (oddRepeat k l)) := by
      change tapeOf (oddW ++ cycleR4) (oddRepeat k l) = _
      exact tapeOf_append _ _ _
    have h1 := oddCycle n _ (oddRepeat_first k l hl)
    rw [hs] at h1
    rw [run_add, h1]
    simp only [Option.bind_some]
    rw [show n+18*(k+1) = (n+18)+18*k by omega]
    exact ih (n+18)

#print axioms oddCycle_many
end F197.MixedCarry
