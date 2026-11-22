/- WITHDRAWN AS A #490 ROOT MODEL (2026-11-22): step490 is defined as
   swap (step85 (swap state)), an extra stack reversal. The actual #490
   blank-root projected successor is the no-extra-swap #85 relation after
   the evaluator double-reversal cancellation. This file only models the
   alternate extra-swap transition system; its 260-step seed and growth
   theorem are not connected to the #490 blank start. -/

import Lean
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace RootMacroModel

inductive Mode where
  | CR | EL | DL | DR
  deriving DecidableEq, Repr

structure Cfg where
  mode : Mode
  L : List Nat
  R : List Nat
  deriving DecidableEq, Repr

def bump : List Nat → List Nat
  | [] => [1]
  | a :: xs => (a + 1) :: xs

def bumpN : List Nat → Nat → List Nat
  | xs, 0 => xs
  | xs, n+1 => bumpN (bump xs) n

def swap (s : Cfg) : Cfg := ⟨s.mode, s.R, s.L⟩

/-- Source-transcribed #85 outer successor. Token branches are marked none;
    the only token event in the 260-step root prefix is separately represented
    by rootAfterToken below. The 76-step growth macro has no token branches. -/
def step85 (s : Cfg) : Option Cfg :=
  match s.mode with
  | .CR =>
    match s.L with
    | [] => some ⟨.EL, [0], bump s.R⟩
    | a :: t =>
      if a == 0 then some ⟨.CR, t, bumpN s.R 2⟩
      else if a == 1 then
        match t with
        | [] => some ⟨.EL, [0], 0 :: bumpN s.R 3⟩
        | b :: r =>
          if b == 0 then some ⟨.CR, 1 :: r, 0 :: 0 :: bump s.R⟩
          else if b == 1 then
            match r with
            | [] => some ⟨.EL, [0,0,0,0], [1,0] ++ s.R⟩
            | _ => some ⟨.EL, [0,0,0,0] ++ r, 0 :: 0 :: bump s.R⟩
          else some ⟨.DR, 0 :: r, 1 :: (b - 2) :: s.R⟩
      else none
  | .EL =>
    match s.R with
    | [] => some ⟨.CR, s.L, [0]⟩
    | a :: t =>
      if a == 0 then some ⟨.EL, 0 :: s.L, t⟩
      else some ⟨.DL, s.L, (a - 1) :: t⟩
  | .DL =>
    match s.R with
    | [] => some ⟨.CR, s.L, [2]⟩
    | a :: t =>
      if a == 0 then some ⟨.EL, 0 :: bump s.L, t⟩
      else if a == 1 then none
      else some ⟨.DR, s.L, 1 :: (a - 2) :: t⟩
  | .DR =>
    match s.L with
    | [] => some ⟨.EL, [0], s.R⟩
    | a :: t =>
      match s.R with
      | [] =>
        if a == 0 then some ⟨.EL, bump t, [0]⟩
        else some ⟨.DR, (a - 1) :: t, [0]⟩
      | b :: r =>
        if b == 0 then none
        else if a == 0 then some ⟨.DR, t, 1 :: (b - 1) :: r⟩
        else some ⟨.CR, (a - 1) :: t, 0 :: (b - 1) :: r⟩

def step490 (s : Cfg) : Option Cfg := (step85 (swap s)).map swap

def run : Nat → Cfg → Option Cfg
  | 0, s => some s
  | n+1, s => (step490 s).bind (run n)

def rootBlock : List Nat := [0,2,0,0,0,2,0,0,0,16,0,0]
def rootRight : List Nat := [0,1,0,0,0,0,0,0,0,0,1,0,0,0]
def rootStart (T : List Nat) : Cfg := ⟨.DR, 1 :: rootBlock ++ T, rootRight⟩
def rootFinish (T : List Nat) : Cfg := ⟨.DR, 1 :: rootBlock ++ rootBlock ++ T, rootRight⟩

theorem root_growth_76 (T : List Nat) :
    run 76 (rootStart T) = some (rootFinish T) := by
  rfl

def pairBlock : List (Nat × Nat) :=
  [(0,0),(2,0),(0,0),(0,0),(0,0),(2,0),(0,0),(0,0),(0,0),(16,0),(0,0),(0,0)]

def pairRight : List (Nat × Nat) :=
  [(0,0),(1,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(1,0),(0,0),(0,0),(0,0)]

theorem root_growth_76_pairs (T : List (Nat × Nat)) :
    run 76
      ⟨.DR, ((1,0) :: pairBlock ++ T).map Prod.fst, pairRight.map Prod.fst⟩ =
    some ⟨.DR, ((1,0) :: pairBlock ++ pairBlock ++ T).map Prod.fst, pairRight.map Prod.fst⟩ := by
  rfl

def rootInitial : Cfg := ⟨.DR, [0,0], [1]⟩
/-- Endpoint of the initial source token closure; the appended source theorem
    checks this endpoint with execute 29. -/
def rootAfterToken : Cfg := ⟨.CR, [1], [0,0,0,1]⟩

def rootSeed : Cfg := ⟨.DR,
  [1,0,2,0,0,0,2,0,0,0,16,0,0,0,12,0,0,0,12,0,0,0,12,0,0,0,2,0,0,0,0],
  [0,1,0,0,0,0,0,0,0,0,1,0,0,0]⟩

def stepRoot (s : Cfg) : Option Cfg :=
  if s = rootInitial then some rootAfterToken else step490 s

def runRoot : Nat → Cfg → Option Cfg
  | 0, s => some s
  | n+1, s => (stepRoot s).bind (runRoot n)

theorem root_prefix_260 : runRoot 260 rootInitial = some rootSeed := by
  rfl

def rootPrefixOrdinaryCost : Nat :=
  42 * 2 + 2 * 6 + 59 * 2 + 40 * 1 + 14 * 4 + 31 * 4 +
  4 * 1 + 26 * 6 + 9 * 3 + 2 * 2 + 1 * 1 + 22 * 5 + 7 * 16

theorem rootPrefixOrdinaryCost_eq : rootPrefixOrdinaryCost = 848 := by
  decide

theorem rootPrefixCost_eq : 29 + rootPrefixOrdinaryCost = 877 := by
  decide

def rootRawCosts : List Nat :=
  [4,3,2,2,2,2,2,2,2,2,2,5,5,5,6,2,1,4,4,4,1,1,6,2,2,2,2,1,6,2,1,6,2,1,4,4,4,3,2,2,5,5,5,5,16,1,6,2,2,2,1,6,2,1,6,2,1,6,2,1,4,4,4,3,2,2,5,16,2,2,1,6,2,1,4,4]

theorem rootRawCosts_sum : rootRawCosts.sum = 254 := by
  decide

end RootMacroModel

#print axioms RootMacroModel.root_prefix_260
#print axioms RootMacroModel.root_growth_76_pairs
#print axioms RootMacroModel.rootPrefixCost_eq
#print axioms RootMacroModel.rootRawCosts_sum
