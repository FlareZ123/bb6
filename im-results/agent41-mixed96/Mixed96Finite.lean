import Mixed96Sound
import Rows96Split
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace A41

def s96T (t:Nat × Nat × Nat):Bool := s96 t.1 t.2.1 t.2.2

def edgeOK (a k c : Nat):Bool :=
  match nextC (a,k,c) with
  | none => true
  | some t => s96T (qu t)

def checkC (a k c : Nat):Bool :=
    edgeOK a k c && (if c<2 then true else edgeOK a k (c+48))

def checkState (a k c : Nat):Bool :=
  (!s96 a k c) ||
    (checkC a k c && checkC (a+96) k c &&
      checkC a (k+96) c && checkC (a+96) (k+96) c)

def checkRow (a k:Nat):Bool := (List.range 50).all (checkState a k)

theorem checkRow_5_0 : checkRow 5 0 = true := by decide
#print axioms checkRow_5_0
end A41
