import Q0151StackSaturation

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation

/-! Executable, independent-of-Python semantics of the proposed q0-151
finite macro abstract interpreter. The machine-level simulation relation
is a separate open obligation. -/

structure RightSummary where
  first : Nat
  tail : Nat
  deriving DecidableEq, Repr

structure SegmentSummary where
  first : Nat
  imageN : Int
  imageP : Int
  last : Nat
  deriving DecidableEq, Repr

structure Control where
  isB : Bool
  right : RightSummary
  segment : SegmentSummary
  deriving DecidableEq, Repr

def emptyRight : RightSummary := ⟨0, 4⟩
def emptySegment : SegmentSummary := ⟨0, 0, 1, 0⟩
def seed : Control := ⟨true, emptyRight, ⟨0, 0, 1, 1⟩⟩

-- -1 denotes a rejected mode.
def dnext (g : Int) (c : Nat) : Int :=
  if g < 0 then -1
  else if c % 4 = 1 then g
  else if c % 4 = 0 then 1
  else if c % 4 = 2 then (if g = 1 then 0 else -1)
  else -1

def maskAccept (t : Nat) (g : Int) : Bool :=
  if g = 0 then (if t = 4 then true else t % 2 = 1)
  else if g = 1 then (if t = 4 then true else t / 2 % 2 = 1)
  else false

def pre (c t : Nat) : Nat :=
  (if maskAccept t (dnext 0 c) then 1 else 0) +
  (if maskAccept t (dnext 1 c) then 2 else 0)

def rightType (r : RightSummary) : Nat :=
  if r.first = 0 then (if r.tail = 4 then 3 else r.tail)
  else pre r.first r.tail

def plus (a b : Nat) : Nat :=
  if a = 0 then b
  else if b = 0 then a
  else if a + b ≤ 4 then a + b
  else 5 + (a + b - 1) % 4

def segClosed (s : SegmentSummary) : SegmentSummary :=
  if s.last = 0 then s
  else if s.first = 0 then ⟨s.last, 0, 1, 0⟩
  else ⟨s.first, dnext s.imageN s.last, dnext s.imageP s.last, 0⟩

def segBit (s : SegmentSummary) (b : Bool) : SegmentSummary :=
  if b then {s with last := plus s.last 1} else segClosed s

def segAppend (s : SegmentSummary) (w : List Bool) : SegmentSummary :=
  w.foldl segBit s

def altWord (n : Nat) : List Bool :=
  (List.replicate n [true,false]).flatten

def preMany (xs : List Nat) (t : Nat) : Nat :=
  xs.foldr pre t

def segConcat (s : SegmentSummary) (r : RightSummary) : RightSummary :=
  let firstRun := if s.last = 0 then r.first else plus s.last r.first
  if s.first = 0 then
    ⟨firstRun, r.tail⟩
  else
    let t := if firstRun = 0 then r.tail else pre firstRun r.tail
    ⟨s.first,
      (if maskAccept t s.imageN then 1 else 0) +
      (if maskAccept t s.imageP then 2 else 0)⟩

def prepend (w : List Bool) (r : RightSummary) : RightSummary :=
  segConcat (segAppend emptySegment w) r

def firstVariants : List Nat := [1,2,4,5,6,8]
def suffixVariants : List Nat := [2,3,4]

def front (t : Nat) : List (Nat × RightSummary) :=
  firstVariants.flatMap fun c =>
    (suffixVariants.filter fun v => pre c v = t).map
      (fun v => (c, ⟨c,v⟩))

def cut (r : RightSummary) : List (Nat × RightSummary) :=
  if r.first = 0 then
    if r.tail = 4 then [(0,r)] else [(3,r)]
  else if r.tail = 4 then [(r.first,emptyRight)]
  else (front r.tail).map (fun pair => (r.first, pair.2))

def choicesA (c : Nat) : List Nat :=
  if c = 1 || c = 2 then [0]
  else if c = 4 then [1]
  else if c = 5 || c = 6 then [1,2,3]
  else if c = 8 then [2,3]
  else []

def resume (r : RightSummary) (saved : SegmentSummary) : Control :=
  ⟨true, r, segAppend saved [true,true,true,true]⟩

def mkControl (b : Bool) (r : RightSummary) (s : SegmentSummary) : Control :=
  ⟨b,r,s⟩

def actionsFor (st : Control) (c : Nat) (r : RightSummary) :
    List (Action Control SegmentSummary RightSummary) := Id.run do
  let s := st.segment
  if c = 0 then
    if st.isB then
      return [.pop (segConcat s r)]
    else if s.last = 3 then
      return [.pop (segConcat {s with last := 2} r)]
    else
      return [.bad]
  let aa := choicesA c
  if aa.isEmpty then return [.bad]
  if c % 4 = 1 then
    return aa.map fun a =>
      if st.isB then
        if a = 0 then .stay (mkControl true r (segAppend s [false,true]))
        else .push (mkControl true r
          (segAppend emptySegment (altWord (2*a-1) ++ [true,true]))) s
      else .stay (mkControl true r
          (segAppend s (altWord (2*a) ++ [true,true])))
  if c % 4 = 0 then
    return aa.map fun a =>
      if st.isB then
        .push (mkControl false r
          (segAppend emptySegment (altWord (2*a-2) ++ [true,true,true]))) s
      else
        .stay (mkControl false r
          (segAppend s (altWord (2*a-1) ++ [true,true,true])))
  if c % 4 = 2 then
    return aa.flatMap fun a =>
      if a > 0 || !st.isB then
        if st.isB then
          [.stay (mkControl true (prepend (altWord (2*a-1) ++ [true]) r)
            (segAppend s [true,true,true,true]))]
        else
          [.pop (segConcat (segAppend s (altWord (2*a) ++ [true])) r)]
      else
        (cut r).flatMap fun (c2,r2) =>
          if c2 = 0 then
            [.pop (segConcat (segAppend s [true,true,true,true]) r2)]
          else if c2 % 4 = 1 then
            (choicesA c2).map fun j =>
              .pop (segConcat (segAppend s
                (if j = 0 then [true,true,true]
                else [true,true,true,false] ++ altWord (2*j-1) ++ [true])) r2)
          else if c2 % 4 = 0 then
            (choicesA c2).map fun j =>
              .stay (mkControl true r2 (segAppend s
                ([true,true,true,false] ++ altWord (2*j-1) ++ [true,true])))
          else [.bad]
  return [.bad]

def delta (st : Control) : List (Action Control SegmentSummary RightSummary) :=
  (cut st.right).flatMap (fun (c,r) => actionsFor st c r)

theorem seed_right_ok : rightType seed.right = 3 := by decide
theorem seed_segment_ok : seed.segment = segAppend emptySegment [true] := by decide

#print axioms seed_right_ok
#print axioms seed_segment_ok
end BB6.Agent5Q0151FiniteModel
