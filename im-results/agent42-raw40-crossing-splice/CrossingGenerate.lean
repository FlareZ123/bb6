import CrossingSource

namespace BB6Coverage.Agent42Crossing
open BB6Coverage Agent50Zipper

/-- Untrusted executable discovery/serialization. The proof never depends
    on this constructor's correctness, only on `checked` for its result. -/
structure BuildCell where
  first : Bool
  current : Bool
  rev : List Ev
  deriving Repr

def newCell (b : Bool) : BuildCell := ⟨b,b,[]⟩
structure BuildZ where
  q : Fin 6
  h : Int
  l : List BuildCell
  c : BuildCell
  r : List BuildCell
  deriving Repr

def buildStart (z : Z) : BuildZ :=
  ⟨z.q,0,z.l.tail.map newCell,newCell (z.l.headD false),z.r.map newCell⟩

def buildStep (p : PartialMachine) (z : BuildZ) : Option BuildZ := do
  let mv ← (p (z.q,z.c.current)).bind id
  let c' := {z.c with current := mv.write, rev := ⟨false,mv.right,mv.next,mv.write⟩::z.c.rev}
  if mv.right then
    let dest := z.r.headD (newCell false)
    let dest' := {dest with rev := ⟨true,true,mv.next,false⟩::dest.rev}
    return ⟨mv.next,z.h+1,c'::z.l,dest',z.r.tail⟩
  else
    let dest := z.l.headD (newCell false)
    let dest' := {dest with rev := ⟨true,false,mv.next,false⟩::dest.rev}
    return ⟨mv.next,z.h-1,z.l.tail,dest',c'::z.r⟩

def buildRun (p : PartialMachine) : Nat → BuildZ → Option BuildZ
  | 0,z => some z
  | n+1,z => (buildStep p z).bind (buildRun p n)

def BuildCell.finish (c : BuildCell) (m : Bool) : Cell := ⟨c.first,c.current,m,c.rev.reverse⟩

def splitSegment (xs : List Cell) (pump : Bool) : List Segment :=
  match xs.getLast? with
  | none => []
  | some c => [⟨xs,pump,edge c true⟩]

def splitSegments (prev : Nat) (xs : List Cell) : List (Nat × Nat) → List Segment
  | [] => splitSegment xs false
  | (a,b)::cuts =>
    let pre := xs.take (a-prev)
    let rest := xs.drop (a-prev)
    let block := rest.take (b-a)
    splitSegment pre false ++ splitSegment block true ++ splitSegments b (rest.drop (b-a)) cuts

def construct (p : PartialMachine) (entry period : Nat) (cuts : List (Nat × Nat)) : Option Certificate := do
  let z ← zrun p entry ⟨0,0,[],[]⟩
  let t ← buildRun p period (buildStart z)
  let full := t.l.reverse.map (fun c => c.finish false) ++
    t.c.finish true :: t.r.map (fun c => c.finish false)
  let k := ((t.l.length : Int)-t.h).toNat
  let head ← full[k]?
  return ⟨(full.take k).reverse,head,splitSegments 0 (full.drop (k+1)) cuts⟩

def defaultCert : Certificate := ⟨[],⟨false,false,false,[]⟩,[]⟩
def witness (p : PartialMachine) (entry period : Nat) (cuts : List (Nat × Nat)) : Certificate :=
  (construct p entry period cuts).getD defaultCert

end BB6Coverage.Agent42Crossing
