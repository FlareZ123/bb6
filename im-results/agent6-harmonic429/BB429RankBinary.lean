import BB429AffineReplay

open BB429AffinePump

def getVarint (data : ByteArray) (start : Nat) : IO (Nat × Nat) := do
  let mut pos := start
  let mut factor := 1
  let mut result := 0
  for _ in [:10] do
    if pos >= data.size then throw (IO.userError "truncated varint")
    let n := data[pos]!.toNat
    pos := pos+1
    result := result+(n%128)*factor
    if n<128 then return (result,pos)
    factor := 128*factor
  throw (IO.userError "overlong varint")

def main (args : List String) : IO Unit := do
  let path :: rest := args | throw (IO.userError "usage: BB429RankBinary certificate [u w time]")
  let mut s : BB429.State := (0,0)
  let mut time : Nat := 0
  match rest with
  | [] => pure ()
  | [us,ws,ts] =>
    let some u := us.toNat? | throw (IO.userError "invalid u")
    let some w := ws.toNat? | throw (IO.userError "invalid w")
    let some t := ts.toNat? | throw (IO.userError "invalid time")
    s := (u,w)
    time := t
  | _ => throw (IO.userError "expected three optional starting values")
  let data ← IO.FS.readBinFile path
  let mut pos := 0
  let mut index := 0
  while pos < data.size do
    let (len,p) ← getVarint data pos
    let (count,p) ← getVarint data p
    let (q,p) ← getVarint data p
    pos := p
    index := index+1
    let b : Block := ⟨len,count,q⟩
    let some next := blockNext b s |
      throw (IO.userError s!"rejected block {index}: {repr b}, state {s}")
    time := time+blockTime b
    s := next
  IO.println s!"accepted {index} blocks; macro time {time}; state {s}"
