import RleCountedMacros

open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.RleStackEngine
open BB6.Agent17.RleCost (weight drBot drBotZeros sweep drOne drZeros rnilOne rnilPow p1One p1Pow p2One p2Pow)
namespace BB6.Agent17.RleCounted

-- Exact charge for the same branch of each executable RLE operation.
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

end BB6.Agent17.RleCounted
