import Raw54OneRDBankAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace BB6.Agent8Raw54.TwoHoleGrowth
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay

/-- Literal six-state partial table
    1RB---_1RC0RD_0RD1RF_1LD0LE_1LB1RD_0RB---.
    A1 and F1 are free; no assigned instruction is a halting transition. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true  => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | _,_     => none

/-- Tape words are nearest-head first. The scanned cell belongs to the
    left zipper list, so our stationary B configurations use an empty
    left word and a leading 1 on the right. -/
def block : List Bool := [false,false,false,true,true]
def tail (k : Nat) : List Bool := rep block k ++ [false,true,true]
def familyS (k : Nat) : Z0 :=
  ⟨1,[],[true] ++ List.replicate 11 false ++ [true,true] ++ tail k⟩
def familyT (k : Nat) : Z0 :=
  ⟨1,[],[true] ++ [false,false,false,true,true] ++
        List.replicate 7 false ++ [true,true] ++ tail k⟩

/-- Original blank tape reaches S_0 in 207 defined primitive steps. -/
theorem entry : run0 table 207 ⟨0,[],[]⟩ = some (familyS 0) := by decide +kernel

/-- The first short pass costs exactly 15 steps, independent of k. -/
theorem S_to_T (k : Nat) : run0 table 15 (familyS k) = some (familyT k) := by rfl

def leftPrefix : List Bool := [false,false,true,true,true,true]
def transfer : List Bool := [false,true,true,true,true]
def leftBase : List Bool := [true,true,true,true]
def familyU (k : Nat) : Z0 :=
  ⟨1,leftPrefix ++ leftBase, [true] ++ rep block (k+1) ++ [false,true,true]⟩
def familyV (k : Nat) : Z0 :=
  ⟨1,leftPrefix ++ rep transfer k ++ leftBase, [true] ++ block ++ [false,true,true]⟩

theorem T_to_U (k : Nat) : run0 table 41 (familyT k) = some (familyU k) := by rfl

/-- One rightward block is converted into a leftward counter block in 13 steps.
    The proof is uniform over all untouched left and right tails. -/
theorem transfer_one (L R : List Bool) :
    run0 table 13 ⟨1,leftPrefix ++ L,[true] ++ block ++ R⟩ =
      some ⟨1,leftPrefix ++ transfer ++ L,[true] ++ R⟩ := by rfl

theorem U_to_V (k : Nat) : run0 table (13*k) (familyU k) = some (familyV k) := by
  have H := sweepR table 1 leftPrefix [true] block transfer 13
    transfer_one k leftBase (block ++ [false,true,true])
  simpa only [familyU,familyV,rep,List.append_assoc,←rep_snoc block k] using H

def rightPrefix : List Bool := [true] ++ List.replicate 7 false ++ [true,true]
def finishPrefix : List Bool := [true] ++ List.replicate 11 false ++ [true,true]
def familyW (k : Nat) : Z0 :=
  ⟨1,rep transfer k ++ leftBase, rightPrefix ++ block ++ [false,true,true]⟩

theorem V_to_W (k : Nat) : run0 table 94 (familyV k) = some (familyW k) := by rfl

/-- One leftward block consumes a transfer word and emits a new right block
    in exactly 27 steps, again for arbitrary untouched tails. -/
theorem left_one (L R : List Bool) :
    run0 table 27 ⟨1,transfer ++ L,rightPrefix ++ R⟩ =
      some ⟨1,L,rightPrefix ++ block ++ R⟩ := by rfl

def familyX (k : Nat) : Z0 :=
  ⟨1,leftBase,rightPrefix ++ rep block k ++ block ++ [false,true,true]⟩

theorem W_to_X (k : Nat) : run0 table (27*k) (familyW k) = some (familyX k) := by
  have H := sweepL table 1 [] rightPrefix transfer block 27
    left_one k leftBase (block ++ [false,true,true])
  simpa only [familyW,familyX,List.nil_append,List.append_assoc] using H

theorem finish_one (R : List Bool) :
    run0 table 12 ⟨1,leftBase,rightPrefix ++ R⟩ =
      some ⟨1,[],finishPrefix ++ R⟩ := by rfl

theorem X_to_S (k : Nat) : run0 table 12 (familyX k) = some (familyS (k+1)) := by
  have H := finish_one (rep block k ++ block ++ [false,true,true])
  simpa only [familyX,familyS,tail,finishPrefix,rep,List.append_assoc,rep_snoc] using H

/-- The second pass is 41 + 13k + 94 + 27k + 12 = 147 + 40k steps. -/
theorem T_to_next (k : Nat) : run0 table (147+40*k) (familyT k) =
    some (familyS (k+1)) := by
  have a := T_to_U k
  have b := U_to_V k
  have c := V_to_W k
  have d := W_to_X k
  have e := X_to_S k
  have H := join0 (join0 (join0 (join0 a b) c) d) e
  rw [show 147+40*k=41+13*k+94+27*k+12 by omega]
  exact H

/-- Exact nonhalting return: S_k advances to S_(k+1), with positive duration. -/
theorem epoch (k : Nat) : run0 table (162+40*k) (familyS k) =
    some (familyS (k+1)) := by
  have H := join0 (S_to_T k) (T_to_next k)
  rw [show 162+40*k=15+(147+40*k) by omega]
  exact H

/-- The two undefined instructions A1 and F1 are never requested by the
    infinite blank run. Every ordinary completion therefore never halts. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table familyS 207 (fun k => 162+40*k) entry
    (by intro k; omega) epoch m hm

theorem cover : Cover (WeightedBound 1006) table := by
  apply Cover.leaf
  intro m hm
  exact weighted_never 1006 m (never m hm)

#print axioms epoch
#print axioms never
#print axioms cover
end BB6.Agent8Raw54.TwoHoleGrowth
