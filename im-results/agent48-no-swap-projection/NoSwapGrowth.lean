import Lean
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace NoSwapGrowth

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

/-- Source-transcribed #85 projected successor. Token-normalizer branches
    are represented by none; the 76-step insertion orbit never enters them. -/
def step : Cfg → Option Cfg := fun s =>
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

def run : Nat → Cfg → Option Cfg
  | 0, s => some s
  | n+1, s => (step s).bind (run n)

def G : List Nat := [0,0,1,0,1,0,0,0,0,1]
def B : List Nat := [16,0,0,0,2,0,0,0,2,0,0,0]

def start (T : List Nat) : Cfg := ⟨.DR, G, 1 :: B ++ T⟩
def finish (T : List Nat) : Cfg := ⟨.DR, G, 1 :: B ++ B ++ T⟩

/-- The 76-successor right-insertion macro, for every finite suffix T. -/
theorem growth76 (T : List Nat) :
    run 76 (start T) = some (finish T) := by
  rfl

def Gpairs : List (Nat × Nat) :=
  [(0,0),(0,0),(1,0),(0,0),(1,0),(0,0),(0,0),(0,0),(0,0),(1,0)]

def Bpairs : List (Nat × Nat) :=
  [(16,0),(0,0),(0,0),(0,0),(2,0),(0,0),(0,0),(0,0),(2,0),(0,0),(0,0),(0,0)]

/-- Pair-list form used by the hparams=1 stack encoding. -/
theorem growth76_pairs (T : List (Nat × Nat)) :
    run 76
      ⟨.DR, Gpairs.map Prod.fst, ((1,0) :: Bpairs ++ T).map Prod.fst⟩ =
    some ⟨.DR, Gpairs.map Prod.fst, ((1,0) :: Bpairs ++ Bpairs ++ T).map Prod.fst⟩ := by
  rfl

end NoSwapGrowth

#print axioms NoSwapGrowth.growth76
#print axioms NoSwapGrowth.growth76_pairs
