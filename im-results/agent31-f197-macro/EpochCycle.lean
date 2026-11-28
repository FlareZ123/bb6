import CycleCert
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace F197.MixedCarry
open JCarry

def cycleW : Word := [false,false,false,true,false,false,true,false,true,false,false,false,true,true,false,false,false,true]
def cycleR : Word := [false,false,true,false,false,false,true]
def cycleR4 : Word := cycleR ++ cycleR ++ cycleR ++ cycleR
structure Instr where
  tokens : List Token
  terminal : Bool
  delta : Nat

def mkRow (w : Word) (i : Instr) : Row :=
  let rest := w.drop (wordIn i.tokens i.terminal).length
  ⟨i.tokens,i.terminal,rest,i.delta,(wordOut i.tokens i.terminal ++ rest).drop (3*i.delta)⟩

def mkRows : Word → List Instr → List Row
  | _,[] => []
  | w,i::is => let r := mkRow w i; r :: mkRows r.next is

def schedule : List Instr := [
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.at], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.at,.tt], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p,.at], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p,.p], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.p,.q,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.tt], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.tt,.p], false, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[], true, 0⟩,
  ⟨[], false, 1⟩,
  ⟨[.q,.at,.p], true, 0⟩]

def cycleRows := mkRows (cycleW ++ cycleR4) schedule

theorem cycleOK : certOK (cycleW ++ cycleR4) cycleRows = true := by decide

theorem cycle (n : Nat) (l : Tape) (hl : l 0 = true) :
    run (2448*n + 26828) (b (leadP n (tapeOf cycleW (tapeOf cycleR4 l))) e) =
      some (b (leadP (n+18) (tapeOf cycleW l)) e) := by
  have he : certEnd (cycleW ++ cycleR4) cycleRows = cycleW := by decide
  have hd : certDelta cycleRows = 18 := by decide
  have hk : cycleRows.length = 36 := by decide
  have hc : certCost cycleRows = 26828 := by decide
  have H := cert_sound (cycleW ++ cycleR4) cycleRows cycleOK n l hl
  rw [he,hd,hk,hc,tapeOf_append] at H
  rw [show 2448*n+26828 = 68*n*36+26828 by omega]
  exact H

def repeat4 : Nat → Tape → Tape
  | 0,l => l
  | k+1,l => tapeOf cycleR4 (repeat4 k l)

def cycleSum : Nat → Nat → Nat
  | _,0 => 0
  | n,k+1 => (2448*n+26828) + cycleSum (n+18) k

theorem repeat4_first (k : Nat) (l : Tape) (hl : l 0 = true) : repeat4 k l 0 = true := by
  cases k with
  | zero => exact hl
  | succ k => rfl

theorem cycle_many (n k : Nat) (l : Tape) (hl : l 0 = true) :
    run (cycleSum n k) (b (leadP n (tapeOf cycleW (repeat4 k l))) e) =
      some (b (leadP (n+18*k) (tapeOf cycleW l)) e) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    change run ((2448*n+26828) + cycleSum (n+18) k)
      (b (leadP n (tapeOf cycleW (tapeOf cycleR4 (repeat4 k l)))) e) = _
    rw [run_add, cycle n _ (repeat4_first k l hl)]
    simp only [Option.bind_some]
    rw [show n+18*(k+1) = (n+18)+18*k by omega]
    exact ih (n+18)

#print axioms cycle
#print axioms cycle_many
end F197.MixedCarry
