import LaneCertificate
import ReverseAverage
namespace BB6.Agent12LaneGenerator
open BB6.Agent12WordBlock BB6.Agent12BitPlanes BB6.Agent12PlaneOps BB6.Agent12LaneCertificate

/-- Untrusted bit-sliced subtraction. Values are reduced modulo the width;
    the separate checker proves the required integer recurrence exactly. -/
def subPairs : List (Nat×Nat) → Nat → List Nat
  | [],_ => []
  | (x,y)::rs,c => (x^^^y^^^c)::subPairs rs (((y|||c)^^^((y|||c)&&&x)) ||| (y&&&c))

def subP (ps qs : List Nat) : List Nat := subPairs (pairs ps qs) 0

def constP (w x mask : Nat) : List Nat := (List.range w).map (fun j=>if x.testBit j then mask else 0)

def pin (mask : Nat) : List Nat → Nat → List Nat
  | [],_ => []
  | p::ps,x => ((p&&&mask)|||(x%2))::pin mask ps (x/2)

def reversePass (N b0 : Nat) (correction old : List Nat) : List Nat :=
  pin (2^(N+1)-2) ((addP old correction).tail.map (fun p=>p<<<1)) b0

/-- The generic ReverseAverage proof gives logarithmically many inverse
    passes whenever a nonnegative integer trace exists within the chosen
    bound. Generator correctness is not assumed by lane_certificate. -/
def recover (s t : State) (N q : Nat) : Trace :=
  let witness := BB6.Agent12BitEventCertificate.propose s N q
  let cs := witness.counts
  let p := witness.p
  let total := t.m
  let w := (2*total+16).log2+1
  let mask := 2^(N+1)-1
  let rem := BB6.Agent12BitEventCertificate.countPlanes N (2^N-1)
  let ms := addP (addP (constP w s.m mask) (addP rem (mul2 rem))) cs
  let correction := maskP q (subP (addP ms (mul2 [p>>>1])) (addP [0,mask] [p]))
  let b0 := (t.a+2+parity t).toNat
  let init := pin (mask-1) (List.replicate w mask) b0
  let bs := (List.range w).foldl (fun prev _ => reversePass N b0 correction prev) init
  ⟨bs,ms,p,cs⟩

end BB6.Agent12LaneGenerator
