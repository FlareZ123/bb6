import Std

namespace S4PrefixDynamics

/-- One standard source-style head increment. -/
def bump (k : Nat) (L : List Nat) : List Nat :=
  if k = 0 then L else
    match L with
    | [] => [k-1]
    | b::rest => (b+k)::rest

def transfer (a : Nat) (L R : List Nat) : Nat × List Nat :=
  R.foldl (fun p d => (d,p.1::p.2)) (a,L)

/-- Local exact recursion equivalent by inspection to the original source's stepEpoch. -/
def epoch (a : Nat) (L R : List Nat) : Option (Nat × List Nat) :=
  let k := a / 2
  let R1 := bump k R
  match L with
  | [] =>
      if a ≤ 1 then none
      else if a % 2 = 0 then some (transfer (k-1) [] (bump 2 R1))
      else epoch k [] (0 :: R1)
  | b :: tail =>
      if a % 2 = 0 then some (transfer (b+k) tail (bump 2 R1))
      else epoch (b+k+1) tail (0 :: R1)
termination_by (L.length,a)
decreasing_by
  all_goals simp_wf
  · omega
  · omega

def reduced (T : List Nat) : Option (List Nat) :=
  (epoch 27 (bump 31 T) [0,6,5,3,1]).map (fun q => bump 17 (q.2.drop 4))

def run : Nat → List Nat → Option (List Nat)
  | 0, T => some T
  | n+1, T => (run n T).bind reduced

end S4PrefixDynamics
