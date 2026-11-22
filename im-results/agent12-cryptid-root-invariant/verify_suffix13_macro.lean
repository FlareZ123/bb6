import Lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
Finite, independent Lean replay of the ordinary #85 CR/EL/DL/DR branches
used by the offset-six suffix-[13] derivation. First-coordinate stacks only.
This checks bounded instances; it is not the quantified theorem or a proof
that the blank-root path reaches these configurations.
Pinned source: google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a.
-/

inductive Mode where
  | CR | EL | DL | DR | Token | Halt
  deriving DecidableEq, Repr, BEq

structure Config where
  mode : Mode
  left : List Nat
  right : List Nat
  deriving DecidableEq, Repr, BEq

def bump (xs : List Nat) : List Nat :=
  match xs with
  | [] => [0]
  | a :: rest => (a + 1) :: rest

def bumpN (xs : List Nat) : Nat → List Nat
  | 0 => xs
  | k + 1 => bumpN (bump xs) k

def step (c : Config) : Option (Config × Nat) :=
  match c.mode with
  | .CR =>
    match c.left with
    | [] => some (⟨.EL, [0], bump c.right⟩, 2)
    | a :: l3 =>
      if a == 0 then
        some (⟨.CR, l3, bumpN c.right 2⟩, 2)
      else if a == 1 then
        match l3 with
        | [] => some (⟨.EL, [0], [0] ++ bumpN c.right 3⟩, 6)
        | b :: l8 =>
          if b == 0 then
            some (⟨.CR, l8, [0] ++ bumpN c.right 3⟩, 5)
          else if b == 1 then
            some (⟨.EL, bump l8, [1, 0, 0] ++ c.right⟩, 16)
          else
            some (⟨.DR, (b - 2) :: l8, [1, 0, 0] ++ c.right⟩, 15)
      else
        some (⟨.Halt, [], []⟩, 2)
  | .EL =>
    match c.right with
    | [] => some (⟨.CR, c.left, [0]⟩, 1)
    | r :: r3 =>
      if r == 0 then
        some (⟨.EL, [0] ++ c.left, r3⟩, 2)
      else
        some (⟨.DL, c.left, (r - 1) :: r3⟩, 1)
  | .DL =>
    match c.right with
    | [] => some (⟨.CR, c.left, [2]⟩, 4)
    | r :: r3 =>
      if r == 0 then
        some (⟨.EL, [0] ++ bump c.left, r3⟩, 6)
      else if r == 1 then
        some (⟨.Token, c.left, r3⟩, 4)
      else
        some (⟨.DR, c.left, [1, r - 2] ++ r3⟩, 4)
  | .DR =>
    match c.left with
    | [] => some (⟨.EL, [0], c.right⟩, 1)
    | a :: l3 =>
      match c.right with
      | [] =>
        if a == 0 then
          some (⟨.EL, bump l3, [0]⟩, 4)
        else
          some (⟨.DR, (a - 1) :: l3, [0]⟩, 3)
      | r :: r3 =>
        if r == 0 then
          if a == 0 then
            some (⟨.Token, l3, r3⟩, 4)
          else
            some (⟨.Token, a :: l3, r3⟩, 3)
        else if a == 0 then
          some (⟨.DR, l3, [1, r - 1] ++ r3⟩, 4)
        else
          some (⟨.CR, (a - 1) :: l3, [0, r - 1] ++ r3⟩, 3)
  | .Token | .Halt => none

def run : Nat → Config → Option (Config × Nat)
  | 0, c => some (c, 0)
  | k + 1, c =>
    match step c with
    | none => none
    | some (c', w) =>
      match run k c' with
      | none => none
      | some (d, rest) => some (d, w + rest)

def E (n x : Nat) (suffix : List Nat := []) : Config :=
  ⟨.CR, [0], List.replicate (4 * n + 6) 0 ++ [x] ++ suffix⟩

def decrementCheck (n x : Nat) : Bool :=
  match run (8 * n + 26) (E n x [13, 0]) with
  | none => false
  | some (c, cost) =>
    c == E (n + 1) (x - 3) [13, 0] && cost == 24 * n + 75

def decrementChecks : Bool :=
  [0, 1, 2, 3, 4].all (fun n =>
    [3, 4, 7, 10, 13, 16].all (fun x => decrementCheck n x))

def fourChainCheck (n : Nat) : Bool :=
  match run (32 * n + 152) (E n 13) with
  | none => false
  | some (c, cost) => c == E (n + 4) 1 && cost == 96 * n + 444

def fourChainChecks : Bool := [0, 1, 2, 3, 4].all fourChainCheck

def oneBridgeCheck (n : Nat) : Bool :=
  let target : Config := ⟨.CR, [0], List.replicate 5 0 ++ [8 * n + 9, 5]⟩
  match run (8 * n + 43) (E n 1) with
  | none => false
  | some (c, cost) => c == target && cost == 16 * n + 115

def oneBridgeChecks : Bool := [0, 1, 2, 3, 4].all oneBridgeCheck

example : decrementChecks = true := by decide
example : fourChainChecks = true := by decide
example : oneBridgeChecks = true := by decide

#eval decrementChecks
#eval fourChainChecks
#eval oneBridgeChecks
