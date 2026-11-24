import FARCheck
namespace BB6Coverage.FAR

/-- Candidate synthesis is intentionally untrusted. Only Data.valid is
    used by the soundness theorem, never any termination heuristic below. -/
def knownPrefix (p : PartialMachine) : Nat → Fin 6 → List Bool → List Bool → Bool
  | 0, _, _, _ => true
  | k+1,q,l,r =>
    match p (q,r.headD false) with
    | some (some mv) =>
      if mv.right then knownPrefix p k mv.next (mv.write::l) r.tail
      else knownPrefix p k mv.next l.tail (l.headD false::mv.write::r.tail)
    | _ => false

private def dfs (d : Nat) : Nat → List (Fin d) → Nat → List (List (Fin d))
  | 0, pre, mx => if mx+1=d then [pre] else []
  | k+1, pre, mx =>
    if pre.length/2 > mx then []
    else ((List.finRange d).filter fun x => x.val ≤ mx+1).flatMap fun x =>
      dfs d k (pre++[x]) (max mx x.val)

def dfaList {d : Nat} (start : Fin d) : List (List (Fin d)) :=
  dfs d (2*d-1) [start] 0

private def unionTargets (rows : Array Nat) (N off mask : Nat) : Nat := Id.run do
  let mut out := 0
  for j in [:N] do
    if mask.testBit j then out := out ||| rows[off+j]!
  return out

private def zeroClosure (rows : Array Nat) (N : Nat) : Nat := Id.run do
  let mut z := 1 <<< (N-1)
  for _ in [:N] do
    let mut z' := z
    for j in [:N] do
      if (rows[j]! &&& z) != 0 then z' := z' ||| (1 <<< j)
    if z' == z then break
    z := z'
  return z

/-- Conventional one-sided finite-automata-reduction saturation.
    The bounded loop merely proposes a certificate. -/
def synthesize {d : Nat} (p : PartialMachine) (start : Fin d) (dfa : List (Fin d)) : Option (Data d) := Id.run do
  let N := 6*d+1
  let H := N-1
  let halt := 1 <<< H
  let mut rows : Array Nat := Array.replicate (2*N) 0
  let mut rules : Array (Nat × Nat × Nat) := #[]
  rows := (rows.set! H halt).set! (N+H) halt
  for l in List.finRange d do
    for q in List.finRange 6 do
      for a in [false,true] do
        let dst := a.toNat*N+6*l.val+q.val
        match p (q,a) with
        | some (some mv) =>
          if mv.right then
            let l' := dfa[2*l.val+mv.write.toNat]?.getD start
            rows := rows.set! dst (1 <<< (6*l'.val+mv.next.val))
          else
            for j in List.finRange d do
              for b in [false,true] do
                if dfa[2*j.val+b.toNat]?.getD start == l then
                  rules := rules.push (dst,b.toNat*N+6*j.val+mv.next.val,mv.write.toNat*N)
        | _ => rows := rows.set! dst halt
  for _ in [:2*N*N+1] do
    let z := zeroClosure rows N
    if z.testBit (6*start.val) then return none
    let mut changed := false
    for (dst,src,off) in rules do
      let x := rows[dst]! ||| unionTargets rows N off rows[src]!
      if x != rows[dst]! then
        rows := rows.set! dst x
        changed := true
    if !changed then
      return some ⟨start,dfa,(rows.toList.take N),(rows.toList.drop N),z⟩
  return none

abbrev Verified (p : PartialMachine) := Sigma fun d => { C : Data d // C.valid p }

private def tryDfa {d : Nat} (p : PartialMachine) (start : Fin d) (dfa : List (Fin d)) : Option (Verified p) :=
  match synthesize p start dfa with
  | none => none
  | some C => if h : C.valid p then some ⟨d,⟨C,h⟩⟩ else none

def searchD {d : Nat} (p : PartialMachine) (start : Fin d) : Option (Verified p) :=
  (dfaList start).findSome? (tryDfa p start)

def search (p : PartialMachine) (limit : Nat) : Option (Verified p) :=
  if !knownPrefix p 24 0 [] [] then none
  else (List.range limit).findSome? fun d => searchD p (⟨0,by omega⟩ : Fin (d+1))

theorem search_sound (p : PartialMachine) (limit : Nat) (h : (search p limit).isSome = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  cases hc : search p limit with
  | none => simp [hc] at h
  | some C => exact C.2.1.sound p C.2.2 m hm

#print axioms search_sound
end BB6Coverage.FAR
