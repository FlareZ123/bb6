/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Executable definitions extracted from google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a, BusyBeaver/Calculi/HaltShared.lean.
Independent executable cost replay, not a machine-semantics proof.
-/
import Std
notation "ℕ" => Nat

inductive StackMode
  | BR
  | C
  | B
  | DR0
  deriving DecidableEq


inductive Item where
  | z (c : ℕ)
  | d (v : ℕ)
  | k (r c : ℕ)

inductive LState where
  | raw (items : List Item)
  | clean (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ)


def pushSeg (r c : ℕ) (segs : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if Nat.beq c 0 then segs
  else match segs with
    | (r2, c2) :: ss => if Nat.beq r r2 then (r, c + c2) :: ss else (r, c) :: segs
    | [] => [(r, c)]


def pushL0 (c : ℕ) (L : List Item) : List Item :=
  if Nat.beq c 0 then L
  else match L with
    | .z c2 :: xs => .z (c + c2) :: xs
    | _ => .z c :: L

def pushLk2 (r c : ℕ) (L : List Item) : List Item :=
  if Nat.beq c 0 then L
  else match L with
    | .k r2 c2 :: xs => if Nat.beq r r2 then .k r (c + c2) :: xs else .k r c :: L
    | _ => .k r c :: L

def pushLd (v : ℕ) (L : List Item) : List Item :=
  if Nat.beq v 0 then pushL0 1 L
  else if Nat.beq v 1 then
    match L with
    | .z c :: .d v2 :: xs =>
      if Nat.beq v2 1 && Nat.ble 2 c then .d 1 :: pushLk2 (c - 2) 1 xs
      else .d 1 :: L
    | _ => .d 1 :: L
  else .d v :: L

def popKTail (r c : ℕ) (xs : List Item) : List Item :=
  if Nat.beq c 1 then xs else .k r (c - 1) :: xs

def popL1 : List Item → Option (ℕ × List Item)
  | [] => none
  | .z c :: xs =>
    if Nat.beq c 0 then popL1 xs
    else if Nat.beq c 1 then some (0, xs)
    else some (0, .z (c - 1) :: xs)
  | .k r c :: xs =>
    if Nat.beq c 0 then popL1 xs
    else some (0, pushL0 (r + 1) (pushLd 1 (popKTail r c xs)))
  | .d v :: xs => some (v, xs)

def bumpL (L : List Item) : List Item :=
  match popL1 L with
  | none => [.z 1]
  | some (a, L1) => pushLd (a + 1) L1

def pushR0 (c : ℕ) (R : List Item) : List Item :=
  if Nat.beq c 0 then R
  else match R with
    | .z c2 :: xs => .z (c + c2) :: xs
    | _ => .z c :: R

def mergeRk2Pre (r c : ℕ) (R : List Item) : ℕ × List Item :=
  if Nat.ble 1 r then
    match R with
    | .z rz :: .d v2 :: .d v1 :: xs =>
      if Nat.beq rz r && Nat.beq v2 2 && Nat.beq v1 1 then (c + 1, xs) else (c, R)
    | _ => (c, R)
  else (c, R)

def pushRk2 (r c : ℕ) (R : List Item) : List Item :=
  if Nat.beq c 0 then R
  else
    let p := mergeRk2Pre r c R
    match p.2 with
    | .k r2 c2 :: xs => if Nat.beq r r2 then .k r (p.1 + c2) :: xs else .k r p.1 :: p.2
    | _ => .k r p.1 :: p.2

def pushRd (v : ℕ) (R : List Item) : List Item :=
  if Nat.beq v 0 then pushR0 1 R
  else if Nat.beq v 2 then
    match R with
    | .d v1 :: xs => if Nat.beq v1 1 then pushRk2 0 1 xs else .d 2 :: R
    | _ => .d 2 :: R
  else .d v :: R

def popR1 : List Item → Option (ℕ × List Item)
  | [] => none
  | .z c :: xs =>
    if Nat.beq c 0 then popR1 xs
    else if Nat.beq c 1 then some (0, xs)
    else some (0, .z (c - 1) :: xs)
  | .k r c :: xs =>
    if Nat.beq c 0 then popR1 xs
    else if Nat.beq r 0 then some (2, .d 1 :: popKTail r c xs)
    else some (0, pushR0 (r - 1) (.d 2 :: .d 1 :: popKTail r c xs))
  | .d v :: xs => some (v, xs)

def bumpR (R : List Item) : List Item :=
  match popR1 R with
  | none => [.z 1]
  | some (d, R1) => pushRd (d + 1) R1

def segsToItems : List (ℕ × ℕ) → List Item → List Item
  | [], acc => acc
  | (r, c) :: ss, acc =>
    if Nat.beq c 0 then segsToItems ss acc
    else .k r c :: segsToItems ss acc

def unpackClean (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) : List Item :=
  let tail := segsToItems segs [.z (bot + 2)]
  if Nat.beq c0 0 then .d 1 :: tail else .z c0 :: .d 1 :: tail

def packTail (cur0 : ℕ) : List Item → Option (List (ℕ × ℕ) × ℕ)
  | [] => if Nat.ble 2 cur0 then some ([], cur0 - 2) else none
  | .z c :: rest => packTail (cur0 + c) rest
  | .d v :: rest =>
    if Nat.beq v 1 && Nat.ble 2 cur0 then
      match packTail 0 rest with
      | some (segs, bot) => some (pushSeg (cur0 - 2) 1 segs, bot)
      | none => none
    else none
  | .k r c :: rest =>
    if Nat.beq c 0 then packTail cur0 rest
    else
      match packTail 0 rest with
      | some (segs, bot) =>
        some (pushSeg (cur0 + r) 1 (pushSeg r (c - 1) segs), bot)
      | none => none

def packHead (cur0 : ℕ) : List Item → Option LState
  | [] => none
  | .z c :: rest => packHead (cur0 + c) rest
  | .d v :: rest =>
    if Nat.beq v 1 then
      match packTail 0 rest with
      | some (segs, bot) => some (.clean cur0 segs bot)
      | none => none
    else none
  | .k r c :: rest =>
    if Nat.beq c 0 then packHead cur0 rest
    else
      match packTail 0 rest with
      | some (segs, bot) =>
        some (.clean (cur0 + r + 2) (pushSeg r (c - 1) segs) bot)
      | none => none


structure RleFullState where
  mode : StackMode
  ls : LState
  R : List Item
  halted : Bool


def isTopD1 : List Item → Bool
  | .d v :: _ => Nat.beq v 1
  | _ => false

def modeCanPack (m : StackMode) (items R : List Item) : Bool :=
  match m with
  | .B => R.isEmpty || isTopD1 items
  | .BR => R.isEmpty
  | .DR0 => true
  | .C => false

def minNat (a b : ℕ) : ℕ := if Nat.ble a b then a else b


def stepRawB (items R : List Item) : RleFullState :=
  match R with
  | [] => ⟨.C, .raw (bumpL items), [], false⟩
  | .z c :: R1 => ⟨.B, .raw (pushL0 c items), R1, false⟩
  | _ =>
    match popR1 R with
    | none => ⟨.C, .raw (bumpL items), [], false⟩
    | some (d, R1) =>
      if Nat.beq d 0 then ⟨.B, .raw (pushL0 1 items), R1, false⟩
      else ⟨.BR, .raw items, pushR0 1 (pushRd (d - 1) R1), false⟩


def stepRawBRPop (items R : List Item) : RleFullState :=
  match popR1 R with
  | none => ⟨.C, .raw (bumpL items), [], false⟩
  | some (d, R1) =>
    if Nat.beq d 0 then ⟨.BR, .raw (pushL0 1 items), R1, false⟩
    else if Nat.beq d 1 then ⟨.DR0, .raw items, bumpR R1, false⟩
    else ⟨.B, .raw (bumpL items), pushRd (d - 2) R1, false⟩


def stepRawBR (items R : List Item) : RleFullState :=
  match R with
  | [] => ⟨.C, .raw (bumpL items), [], false⟩
  | .z c :: R1 => ⟨.BR, .raw (pushL0 c items), R1, false⟩
  | .k r m :: R1 =>
    if Nat.ble 1 m then
      match popL1 items with
      | some (a, L1) =>
        if Nat.beq a 0 then
          ⟨.BR, .raw (pushL0 3 (pushLd 1 (pushLk2 r (m - 1) (pushL0 r L1)))), R1, false⟩
        else stepRawBRPop items (.k r m :: R1)
      | none => stepRawBRPop items (.k r m :: R1)
    else ⟨.BR, .raw items, R1, false⟩
  | .d v :: R1 => stepRawBRPop items (.d v :: R1)


def stepRawDR0Atomic (items R : List Item) : RleFullState :=
  match popL1 items with
  | none => ⟨.C, .raw [.d 1], R, false⟩
  | some (a, L1) =>
    if Nat.beq a 0 then
      match items with
      | .z c :: Lrest => ⟨.DR0, .raw Lrest, pushR0 c R, false⟩
      | _ => ⟨.DR0, .raw L1, pushR0 1 R, false⟩
    else ⟨.C, .raw (pushLd (a - 1) L1), pushR0 1 R, false⟩


def stepRawDR0 (items R : List Item) : RleFullState :=
  match items with
  | [.z c] =>
    match R with
    | .d v1 :: .z q :: R2 =>
      if Nat.beq v1 1 then ⟨.DR0, .raw [.z (c + 3 * q)], .d 1 :: R2, false⟩
      else ⟨.BR, .raw [.z (c + 3)], R, false⟩
    | _ => ⟨.BR, .raw [.z (c + 3)], R, false⟩
  | _ => stepRawDR0Atomic items R


def stepRawCAtomic (items R : List Item) : RleFullState :=
  match popL1 items with
  | none => ⟨.DR0, .raw [], R, false⟩
  | some (a, L1) =>
    if Nat.beq a 0 then
      match popL1 L1 with
      | none => ⟨.C, .raw [], pushRd 1 R, false⟩
      | some (a1, L3) =>
        if Nat.beq a1 0 then ⟨.C, .raw (bumpL L3), pushRd 1 R, false⟩
        else if Nat.beq a1 1 then ⟨.C, .raw (bumpL (bumpL L3)), pushR0 1 (bumpR R), false⟩
        else ⟨.BR, .raw (pushLd (a1 - 2) L3), pushR0 1 (pushRd 1 R), false⟩
    else if Nat.beq a 1 then
      match popL1 L1 with
      | none => ⟨.B, .raw [.z 1], pushRd 1 R, false⟩
      | some (a1, L3) =>
        if Nat.beq a1 0 then ⟨.DR0, .raw L3, pushRd 2 R, false⟩
        else ⟨.C, .raw (pushLd (a1 - 1) L3), pushRd 2 R, false⟩
    else ⟨.C, .raw (pushLd a L1), R, true⟩


def stepRawC (items R : List Item) : RleFullState :=
  match items with
  | .z cz :: .k r m :: L2 =>
    if Nat.beq cz 1 then ⟨.C, .raw (pushL0 1 L2), pushRk2 r m R, false⟩
    else stepRawCAtomic items R
  | .z cz :: .d v1 :: L2 =>
    if Nat.ble 4 cz && Nat.beq v1 1 then
      ⟨.C, .raw (pushL0 1 L2), pushRk2 (cz - 3) 1 R, false⟩
    else stepRawCAtomic items R
  | [.z cz] =>
    if Nat.ble 4 cz then ⟨.DR0, .raw [], pushRk2 (cz - 4) 1 R, false⟩
    else stepRawCAtomic items R
  | _ => stepRawCAtomic items R


def stepCleanBPop (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item) : RleFullState :=
  match popR1 R with
  | none => ⟨.B, .raw (unpackClean c0 segs bot), R, false⟩
  | some (d, R1) =>
    if Nat.beq d 0 then ⟨.B, .clean (c0 + 1) segs bot, R1, false⟩
    else ⟨.BR, .clean c0 segs bot, pushR0 1 (pushRd (d - 1) R1), false⟩


def stepCleanB (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item) : RleFullState :=
  match R with
  | [] =>
    if Nat.ble 1 c0 && Nat.ble 1 bot then
      ⟨.B, .clean 1 (pushSeg 0 (bot - 1) (pushSeg (c0 - 1) 1 segs)) 0, [], false⟩
    else ⟨.B, .raw (unpackClean c0 segs bot), [], false⟩
  | .z cz :: .k r cnt :: Rrem =>
    if Nat.beq c0 0 && Nat.ble 1 bot && Nat.beq cz 1 then
      let q := minNat cnt bot
      if Nat.ble 1 q then
        let Rnew := if Nat.beq cnt q then .z 1 :: Rrem else .z 1 :: .k r (cnt - q) :: Rrem
        ⟨.B, .clean 0 (pushSeg (r + 3) q segs) (bot - q), Rnew, false⟩
      else ⟨.B, .clean (c0 + cz) segs bot, .k r cnt :: Rrem, false⟩
    else ⟨.B, .clean (c0 + cz) segs bot, .k r cnt :: Rrem, false⟩
  | .z cz :: R1 =>
    ⟨.B, .clean (c0 + cz) segs bot, R1, false⟩
  | .d v1 :: .d v2 :: .k r cnt :: Rrem =>
    if Nat.beq c0 0 && Nat.beq v1 1 && Nat.beq v2 1 then
      let q := minNat cnt (bot / (r + 1))
      if Nat.ble 1 q then
        let Rnew := if Nat.beq cnt q then .d 1 :: .d 1 :: Rrem else .d 1 :: .d 1 :: .k r (cnt - q)
            :: Rrem
        ⟨.B, .clean 0 (pushSeg (4 * r + 3) q segs) (bot - q * (r + 1)), Rnew, false⟩
      else ⟨.BR, .clean c0 segs bot, pushR0 1 (pushRd 0 (.d v2 :: .k r cnt :: Rrem)), false⟩
    else stepCleanBPop c0 segs bot (.d v1 :: .d v2 :: .k r cnt :: Rrem)
  | _ => stepCleanBPop c0 segs bot R


def stepCleanBR (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item) : RleFullState :=
  match R with
  | [] =>
    if Nat.ble 1 c0 && Nat.ble 1 bot then
      ⟨.B, .clean 1 (pushSeg 0 (bot - 1) (pushSeg (c0 - 1) 1 segs)) 0, [], false⟩
    else ⟨.BR, .raw (unpackClean c0 segs bot), [], false⟩
  | .z cz :: R1 =>
    ⟨.BR, .clean (c0 + cz) segs bot, R1, false⟩
  | .k r m :: R1 =>
    if Nat.ble 1 m && Nat.ble 1 c0 && Nat.ble 3 (r + c0) then
      ⟨.BR, .clean 3 (pushSeg r (m - 1) (pushSeg (r + c0 - 3) 1 segs)) bot, R1, false⟩
    else ⟨.BR, .raw (unpackClean c0 segs bot), .k r m :: R1, false⟩
  | .d v :: R1 =>
    match popR1 (.d v :: R1) with
    | none => ⟨.BR, .raw (unpackClean c0 segs bot), .d v :: R1, false⟩
    | some (d, R2) =>
      if Nat.beq d 0 then ⟨.BR, .clean (c0 + 1) segs bot, R2, false⟩
      else if Nat.beq d 1 then ⟨.DR0, .clean c0 segs bot, bumpR R2, false⟩
      else if Nat.ble 3 c0 then
        ⟨.B, .clean 0 (pushSeg (c0 - 3) 1 segs) bot, pushRd (d - 2) R2, false⟩
      else ⟨.BR, .raw (unpackClean c0 segs bot), .d v :: R1, false⟩


def stepCleanDR0 (c0 : ℕ) (segs : List (ℕ × ℕ)) (bot : ℕ) (R : List Item) : RleFullState :=
  if Nat.ble 1 bot then
    match R with
    | .d v1 :: .z rz :: R2 =>
      if Nat.beq v1 1 then
        let q := minNat rz bot
        if Nat.ble 1 q then
          let Rnew := if Nat.beq rz q then .d 1 :: R2 else .d 1 :: .z (rz - q) :: R2
          ⟨.DR0, .clean (c0 + 4 * q) segs (bot - q), Rnew, false⟩
        else ⟨.BR, .clean (c0 + 4) segs (bot - 1), R, false⟩
      else ⟨.BR, .clean (c0 + 4) segs (bot - 1), R, false⟩
    | _ => ⟨.BR, .clean (c0 + 4) segs (bot - 1), R, false⟩
  else ⟨.DR0, .raw (unpackClean c0 segs bot), R, false⟩


def tryPack (m : StackMode) (items R : List Item) : Option LState :=
  if modeCanPack m items R then
    match packHead 0 items with
    | some (LState.clean c0 segs bot) =>
      if Nat.ble 1 bot then some (LState.clean c0 segs bot) else none
    | _ => none
  else none


def rleStep (s : RleFullState) : RleFullState :=
  match s.ls with
  | .raw items =>
    match tryPack s.mode items s.R with
    | some ls' => ⟨s.mode, ls', s.R, false⟩
    | none =>
      match s.mode with
      | .B => stepRawB items s.R
      | .BR => stepRawBR items s.R
      | .DR0 => stepRawDR0 items s.R
      | .C => stepRawC items s.R
  | .clean c0 segs bot =>
    match s.mode with
    | .B => stepCleanB c0 segs bot s.R
    | .BR => stepCleanBR c0 segs bot s.R
    | .DR0 => stepCleanDR0 c0 segs bot s.R
    | .C => ⟨.C, .raw (unpackClean c0 segs bot), s.R, false⟩


def strictNat {α : Type} (n : ℕ) (f : ℕ → α) : α :=
  Nat.casesOn (Nat.add n 1) (f 0) (fun m => f m)


def strictItem {α : Type} (it : Item) (f : Item → α) : α :=
  match it with
  | .z c => strictNat c (fun c' => f (.z c'))
  | .d v => strictNat v (fun v' => f (.d v'))
  | .k r c => strictNat r (fun r' => strictNat c (fun c' => f (.k r' c')))


def strictItems {α : Type} : List Item → (List Item → α) → α
  | [], f => f []
  | x :: xs, f => strictItem x (fun x' => strictItems xs (fun xs' => f (x' :: xs')))


def strictSegs {α : Type} : List (ℕ × ℕ) → (List (ℕ × ℕ) → α) → α
  | [], f => f []
  | (r, c) :: xs, f =>
    strictNat r (fun r' => strictNat c (fun c' => strictSegs xs (fun xs' => f ((r', c') :: xs'))))


def strictLState {α : Type} (ls : LState) (f : LState → α) : α :=
  match ls with
  | .raw items => strictItems items (fun items' => f (.raw items'))
  | .clean c0 segs bot =>
    strictNat c0 (fun c0' =>
      strictSegs segs (fun segs' =>
        strictNat bot (fun bot' => f (.clean c0' segs' bot'))))


def strictMode {α : Type} (m : StackMode) (f : StackMode → α) : α :=
  match m with
  | .B => f .B
  | .BR => f .BR
  | .DR0 => f .DR0
  | .C => f .C


def strictState {α : Type} (s : RleFullState) (f : RleFullState → α) : α :=
  match s with
  | ⟨m, ls, R, h⟩ =>
    strictMode m (fun m' =>
      strictLState ls (fun ls' =>
        strictItems R (fun R' =>
          Bool.casesOn h (f ⟨m', ls', R', false⟩) (f ⟨m', ls', R', true⟩))))


def strictItems4 {α : Type} : List Item → (List Item → α) → α
  | [], f => f []
  | [x0], f => strictItem x0 (fun y0 => f [y0])
  | [x0, x1], f => strictItem x0 (fun y0 => strictItem x1 (fun y1 => f [y0, y1]))
  | [x0, x1, x2], f =>
    strictItem x0 (fun y0 => strictItem x1 (fun y1 => strictItem x2 (fun y2 => f [y0, y1, y2])))
  | x0 :: x1 :: x2 :: x3 :: xs, f =>
    strictItem x0 (fun y0 => strictItem x1 (fun y1 => strictItem x2 (fun y2 =>
      strictItem x3 (fun y3 => f (y0 :: y1 :: y2 :: y3 :: xs)))))


def strictSegs3 {α : Type} : List (ℕ × ℕ) → (List (ℕ × ℕ) → α) → α
  | [], f => f []
  | [(r0, c0)], f => strictNat r0 (fun r0' => strictNat c0 (fun c0' => f [(r0', c0')]))
  | [(r0, c0), (r1, c1)], f =>
    strictNat r0 (fun r0' => strictNat c0 (fun c0' =>
      strictNat r1 (fun r1' => strictNat c1 (fun c1' => f [(r0', c0'), (r1', c1')]))))
  | (r0, c0) :: (r1, c1) :: (r2, c2) :: xs, f =>
    strictNat r0 (fun r0' => strictNat c0 (fun c0' =>
      strictNat r1 (fun r1' => strictNat c1 (fun c1' =>
        strictNat r2 (fun r2' => strictNat c2 (fun c2' =>
          f ((r0', c0') :: (r1', c1') :: (r2', c2') :: xs)))))))


def strictStateFast {α : Type} (s : RleFullState) (f : RleFullState → α) : α :=
  match s with
  | ⟨m, .raw items, R, h⟩ =>
    strictMode m (fun m' =>
      strictItems4 items (fun items' =>
        strictItems4 R (fun R' =>
          Bool.casesOn h (f ⟨m', .raw items', R', false⟩) (f ⟨m', .raw items', R', true⟩))))
  | ⟨m, .clean c0 segs bot, R, h⟩ =>
    strictMode m (fun m' =>
      strictNat c0 (fun c0' =>
        strictSegs3 segs (fun segs' =>
          strictNat bot (fun bot' =>
            strictItems4 R (fun R' =>
              Bool.casesOn h (f ⟨m', .clean c0' segs' bot', R', false⟩)
                             (f ⟨m', .clean c0' segs' bot', R', true⟩))))))


def runStepsInner (n : ℕ) (s : RleFullState) : RleFullState :=
  Nat.rec
    (fun s => s)
    (fun _ ih s =>
      match s with
      | ⟨m, ls, R, true⟩ => ⟨m, ls, R, true⟩
      | ⟨m, ls, R, false⟩ => strictStateFast (rleStep ⟨m, ls, R, false⟩) ih)
    n s


def runBatches (b : ℕ) (s : RleFullState) : RleFullState :=
  Nat.rec
    (fun s => s)
    (fun _ ih s => strictState (runStepsInner 25 s) ih)
    b s


def weight (segs : List (Nat × Nat)) : Nat :=
  segs.foldr (fun (r,c) s => c * (6*r+26) + s) 0

def drBot (k : Nat) := 6*k+14
def drBotZeros (q k : Nat) := 6*k*q+9*q*q+9*q
def sweep (bot S : Nat) := 6*bot+41+S
def drOne (c0 bot S : Nat) := 6*c0+6*bot+46+S
def drZeros (q c0 bot S : Nat) := 6*q*(c0+bot)+15*q*q+35*q+q*S
def rnilOne (c0 bot S : Nat) := 6*c0+6*bot+57+S
def rnilPow (q bot S : Nat) := 6*q*bot+16*q*q+41*q+q*S
def p1One (r bot S : Nat) := 10*r+6*bot+75+S
def p1Pow (q r bot S : Nat) := q*(7*r+50+6*bot+S)+(3*r+25)*q*q
def p2One (r bot S : Nat) := 15*r*r+77*r+73+6*bot*(r+1)+(r+1)*S
def p2Pow (q r bot S : Nat) := q*(37*r+48+6*bot*(r+1)+(r+1)*S)+(r+1)*(15*r+25)*q*q


def costRawB (items R : List Item) : Nat :=
  match R with
  | [] => 1
  | .z c :: _ => 4*c
  | _ =>
    match popR1 R with
    | none => 1
    | some (d, _) => if Nat.beq d 0 then 4 else 2

def costRawBRPop (items R : List Item) : Nat :=
  match popR1 R with
  | none => 1
  | some (d, _) => if Nat.beq d 0 then 2 else if Nat.beq d 1 then 4 else 5

def costRawBR (items R : List Item) : Nat :=
  match R with
  | [] => 1
  | .z c :: _ => 2*c
  | .k r m :: R1 =>
    if Nat.ble 1 m then
      match popL1 items with
      | some (a, _) => if Nat.beq a 0 then m*(2*r+15) else costRawBRPop items (.k r m :: R1)
      | none => costRawBRPop items (.k r m :: R1)
    else 0
  | .d v :: R1 => costRawBRPop items (.d v :: R1)

def costRawDR0Atomic (items R : List Item) : Nat :=
  match popL1 items with
  | none => 3
  | some (a, _) =>
    if Nat.beq a 0 then
      match items with
      | .z c :: _ => 4*c
      | _ => 4
    else 3

def costRawDR0 (items R : List Item) : Nat :=
  match items with
  | [.z c] =>
    match R with
    | .d v1 :: .z q :: _ => if Nat.beq v1 1 then drBotZeros q c else drBot c
    | _ => drBot c
  | _ => costRawDR0Atomic items R

def costRawCAtomic (items R : List Item) : Nat :=
  match popL1 items with
  | none => 1
  | some (a, L1) =>
    if Nat.beq a 0 then
      match popL1 L1 with
      | none => 3
      | some (a1, _) => if Nat.beq a1 0 then 5 else if Nat.beq a1 1 then 17 else 4
    else if Nat.beq a 1 then
      match popL1 L1 with
      | none => 5
      | some (a1, _) => if Nat.beq a1 0 then 7 else 6
    else 3

def costRawC (items R : List Item) : Nat :=
  match items with
  | .z cz :: .k r m :: _ =>
    if Nat.beq cz 1 then m*(4*r+11) else costRawCAtomic items R
  | .z cz :: .d v1 :: _ =>
    if Nat.ble 4 cz && Nat.beq v1 1 then 4*(cz-3)+11 else costRawCAtomic items R
  | [.z cz] =>
    if Nat.ble 4 cz then 4*(cz-4)+12 else costRawCAtomic items R
  | _ => costRawCAtomic items R

def costCleanBPop (c0 : Nat) (segs : List (Nat × Nat)) (bot : Nat) (R : List Item) : Nat :=
  match popR1 R with
  | none => 0
  | some (d, _) => if Nat.beq d 0 then 4 else 2

def costRNIL (c0 : Nat) (segs : List (Nat × Nat)) (bot : Nat) : Nat :=
  rnilOne (c0-1) (bot-1) (weight segs) +
    rnilPow (bot-1) 0 (weight (pushSeg (c0-1) 1 segs))

def costCleanB (c0 : Nat) (segs : List (Nat × Nat)) (bot : Nat) (R : List Item) : Nat :=
  match R with
  | [] =>
    if Nat.ble 1 c0 && Nat.ble 1 bot then costRNIL c0 segs bot else 0
  | .z cz :: .k r cnt :: Rrem =>
    if Nat.beq c0 0 && Nat.ble 1 bot && Nat.beq cz 1 then
      let q := minNat cnt bot
      if Nat.ble 1 q then p1Pow q r (bot-q) (weight segs) else 4*cz
    else 4*cz
  | .z cz :: _ => 4*cz
  | .d v1 :: .d v2 :: .k r cnt :: Rrem =>
    if Nat.beq c0 0 && Nat.beq v1 1 && Nat.beq v2 1 then
      let q := minNat cnt (bot / (r+1))
      if Nat.ble 1 q then p2Pow q r (bot-q*(r+1)) (weight segs) else 2
    else costCleanBPop c0 segs bot (.d v1 :: .d v2 :: .k r cnt :: Rrem)
  | _ => costCleanBPop c0 segs bot R

def costCleanBR (c0 : Nat) (segs : List (Nat × Nat)) (bot : Nat) (R : List Item) : Nat :=
  match R with
  | [] => if Nat.ble 1 c0 && Nat.ble 1 bot then costRNIL c0 segs bot else 0
  | .z cz :: _ => 2*cz
  | .k r m :: _ =>
    if Nat.ble 1 m && Nat.ble 1 c0 && Nat.ble 3 (r+c0) then m*(2*r+15) else 0
  | .d v :: R1 =>
    match popR1 (.d v :: R1) with
    | none => 0
    | some (d, _) =>
      if Nat.beq d 0 then 2 else if Nat.beq d 1 then 4 else if Nat.ble 3 c0 then 5 else 0

def costCleanDR0 (c0 : Nat) (segs : List (Nat × Nat)) (bot : Nat) (R : List Item) : Nat :=
  if Nat.ble 1 bot then
    match R with
    | .d v1 :: .z rz :: _ =>
      if Nat.beq v1 1 then
        let q := minNat rz bot
        if Nat.ble 1 q then drZeros q c0 (bot-q) (weight segs)
        else drOne c0 (bot-1) (weight segs)
      else drOne c0 (bot-1) (weight segs)
    | _ => drOne c0 (bot-1) (weight segs)
  else 0

def costRleStep (s : RleFullState) : Nat :=
  match s.ls with
  | .raw items =>
    match tryPack s.mode items s.R with
    | some _ => 0
    | none =>
      match s.mode with
      | .B => costRawB items s.R
      | .BR => costRawBR items s.R
      | .DR0 => costRawDR0 items s.R
      | .C => costRawC items s.R
  | .clean c0 segs bot =>
    match s.mode with
    | .B => costCleanB c0 segs bot s.R
    | .BR => costCleanBR c0 segs bot s.R
    | .DR0 => costCleanDR0 c0 segs bot s.R
    | .C => 0


def costStepsInner (n : Nat) (s : RleFullState) : Nat :=
  Nat.rec (fun _ => 0)
    (fun _ ih s =>
      match s with
      | ⟨_, _, _, true⟩ => 0
      | ⟨m, ls, R, false⟩ =>
        strictNat (costRleStep ⟨m, ls, R, false⟩) (fun c =>
          strictStateFast (rleStep ⟨m, ls, R, false⟩) (fun s' => c + ih s')))
    n s

theorem costStepsInner_succ (n : Nat) (s : RleFullState) :
    costStepsInner (n+1) s =
      match s with
      | ⟨_, _, _, true⟩ => 0
      | ⟨m, ls, R, false⟩ =>
        strictNat (costRleStep ⟨m, ls, R, false⟩) (fun c =>
          strictStateFast (rleStep ⟨m, ls, R, false⟩) (fun s' => c + costStepsInner n s')) := rfl

def costBatches (b : Nat) (s : RleFullState) : Nat :=
  Nat.rec (fun _ => 0)
    (fun _ ih s => strictNat (costStepsInner 25 s) (fun c =>
      strictState (runStepsInner 25 s) (fun s' => c + ih s')))
    b s

theorem costBatches_succ (b : Nat) (s : RleFullState) :
    costBatches (b+1) s =
      strictNat (costStepsInner 25 s) (fun c =>
        strictState (runStepsInner 25 s) (fun s' => c + costBatches b s')) := rfl


def first : RleFullState := ⟨.B, .raw [.z 1], [], false⟩
def second : RleFullState := ⟨.C, .raw [], [.z 1], false⟩
#eval ((runBatches 380 first).halted, costBatches 380 first)
#eval ((runBatches 740 second).halted, costBatches 740 second)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first_cost_chunk0 : costBatches 100 first = 141295254433562419116308496 := rfl
#print axioms first_cost_chunk0
