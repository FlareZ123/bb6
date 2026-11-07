import FastFullBoolean

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent5CParameterSearch

/-- Exact finite scan of the fully executable high-parameter filter.
    The box bounds are experimental only; no claim is made outside them. -/
def scanRow (jMax m : Nat) : List Nat :=
  (List.range (jMax + 1)).filter
    (fun j => BB6.Agent27FastBool.fastHighAllowedFullBool j m)

/-- Pairs are ordered by increasing m, then increasing j. -/
def scanPairs (jMax mMax : Nat) : List (Nat × Nat) :=
  (List.range (mMax + 1)).flatMap fun m =>
    (scanRow jMax m).map fun j => (j, m)

def scanCounts (jMax mMax : Nat) : List (Nat × Nat) :=
  (List.range (mMax + 1)).map fun m =>
    (m, (scanRow jMax m).length)

def renderCounts (counts : List (Nat × Nat)) : String :=
  String.intercalate "\n" (counts.map fun (m, n) => s!"m={m}: {n}")

def renderPairs (pairs : List (Nat × Nat)) : String :=
  String.intercalate "\n" (pairs.map fun (j, m) => s!"j={j}, m={m}")

def main : IO Unit := do
  let jMax := 5000
  let mMax := 40
  let counts := scanCounts jMax mMax
  let pairs := scanPairs jMax mMax
  let summary :=
    s!"Exact high-filter scan\nj=0..{jMax}, m=0..{mMax}\n" ++
    s!"Total allowed pairs: {pairs.length}\n\nCounts by m:\n" ++
    renderCounts counts ++
    s!"\n\nFirst 200 pairs:\n" ++
    renderPairs (pairs.take 200) ++ "\n"
  IO.FS.writeFile "im-results/agent5-c-parameter-search/high-allowed-5000x40.txt" summary
  IO.println s!"Wrote {pairs.length} high-filter pairs."

end BB6.Agent5CParameterSearch

/-- Root entry point required by `lean --run`. -/
def main : IO Unit := BB6.Agent5CParameterSearch.main
