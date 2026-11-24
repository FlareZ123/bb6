import BB429AffineReplay

open BB429AffinePump

/-- Executable replay of untrusted generator output. The replay soundness theorem
    is kernel proved; this IO run is computational evidence, not a kernel proof
    of the entire CSV. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: lean --run BB429AffineCSV.lean blocks.csv")
  let lines ← IO.FS.lines path
  let mut s : BB429.State := (0,0)
  let mut time : Nat := 0
  let mut index : Nat := 0
  for line in lines.toList.drop 1 do
    index := index+1
    let some ns := (line.trimAscii.toString.splitOn ",").mapM String.toNat? |
      throw (IO.userError s!"invalid CSV line {index+1}")
    let [len,count,q,u,w,oldTime,v,z,newTime] := ns |
      throw (IO.userError s!"wrong column count at row {index}")
    if s ≠ (u,w) || time ≠ oldTime then
      throw (IO.userError s!"broken chain at row {index}")
    let b : Block := ⟨len,count,q⟩
    let some endState := blockNext b s |
      throw (IO.userError s!"rejected block at row {index}")
    if endState ≠ (v,z) || time+blockTime b ≠ newTime then
      throw (IO.userError s!"incorrect endpoint/time at row {index}")
    s := endState
    time := newTime
  IO.println s!"accepted {index} blocks; root macro time {time}; state {s}"
