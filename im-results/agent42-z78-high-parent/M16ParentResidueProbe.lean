import CSourceBridge16

namespace BB6.Agent42Z78Probe

/-- Abstract M16 coordinate for an actual counter at least eight with
    the indicated residue modulo sixteen. -/
def qBig (r : Nat) : Nat := 8 + ((r + 8) % 16)

/-- Bit j records whether the M16 quotient marks the c=0 state
    (a, k) as blank-reachable, with k congruent to j modulo sixteen. -/
def c0RowMask (a : Nat) : Nat :=
  (List.range 16).foldl
    (fun mask j =>
      if CCert.seen a (qBig j) (CCert.q 0)
      then mask + 2^j else mask) 0

/-- The six possible abstract left coordinates for an odd source
    counter a>=8. -/
#eval ( [9, 11, 13, 15, 21, 23].map
  (fun a => (a, c0RowMask a)) )

end BB6.Agent42Z78Probe
