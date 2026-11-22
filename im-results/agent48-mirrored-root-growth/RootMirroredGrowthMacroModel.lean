import Lean
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

/-- Source-transcribed #85 outer successor; token branches are marked none.
    The 76-step mirrored-root path never enters any of those branches. -/
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

/-- Independently counted raw costs of the 76 underlying source-mode branches. -/
def rootRawCosts : List Nat :=
  [4,3,2,2,2,2,2,2,2,2,2,5,5,5,6,2,1,4,4,4,1,1,6,2,2,2,2,1,6,2,1,6,2,1,4,4,4,3,2,2,5,5,5,5,16,1,6,2,2,2,1,6,2,1,6,2,1,6,2,1,4,4,4,3,2,2,5,16,2,2,1,6,2,1,4,4]

theorem rootRawCosts_sum : rootRawCosts.sum = 254 := by
  decide

end RootMacroModel

#print axioms RootMacroModel.root_growth_76
#print axioms RootMacroModel.root_growth_76_pairs
#print axioms RootMacroModel.rootRawCosts_sum
