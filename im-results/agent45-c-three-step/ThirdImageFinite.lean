import Std
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace BB6.Agent45Third

def val2Loop : Nat → Nat → Nat
  | 0, _ => 0
  | fuel+1, n => if n=0 || n%2=1 then 0 else val2Loop fuel (n/2)+1

def val2 (n : Nat) : Nat := val2Loop 10 n

def imageOne (a k : Nat) : Bool :=
  k%2=0 || (a+k)%4=0 || (a+k)%4=3

def H2 (sResid yResid : Nat) : Bool :=
  let s := 256+sResid%64
  let y := 64+yResid%64
  let x := s-y
  let q := s+s%2
  let v := val2 q
  v ≥ 5 || (y%2=0 && imageOne (s-2) ((y-2)/2)) ||
    (List.range (v-1)).any (fun n =>
      (if s%2=0 then (n+1)%2 else n%2) = x%2 &&
      let a := q/2^(n+1)-(if s%2=0 then 2 else 3)
      let numerator := s+y-a-7-3*n
      imageOne a (numerator/2))

def highHit (v u parity yr : Nat) : Bool :=
  let q := 2^v*u
  let s := q-parity
  let y := 512+yr
  (List.range 4).any (fun i =>
    let n := 2*i+(if y%2=0 then 1 else 0)
    let a := q/2^(n+1)-(if s%2=0 then 2 else 3)
    let numerator := s+y-a-7-3*n
    let k := numerator/2
    H2 ((a+k)%64) (k%64))

def multiplierCases (v : Nat) : List Nat :=
  if v = 12 then [1,3,5,7] else if v = 13 then [1,3] else [1]

def highAll : Bool :=
  (List.range 4).all fun i =>
    let v := 12+i
    (multiplierCases v).all fun u =>
      (List.range 2).all fun p =>
        (List.range 128).all fun yr => highHit v u p yr

example : val2 256 = 8 := by decide
example : H2 0 0 = true := by decide
theorem highAll_cert : highAll = true := by decide
#print axioms highAll_cert
end BB6.Agent45Third
