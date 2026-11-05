import Lean
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace BB6.Agent9Density

def previous256 : List Nat :=
  [14,30,57,61,73,77,106,138,173,217,218,221,233,238,250,254]

def previousCost11 : List Nat :=
  [121,125,137,141,153,154,169,170,285,298,537,553,570,590,606,621,
   698,714,718,734,761,765,777,781,814,830,842,925,942,958,1005]

def newCost10 : List Nat :=
  [34,42,50,185,201,281,289,314,334,350,365,369,442,458,462,478,
   505,509,517,521,525,530,557,558,574,578,586,601,617,641,669,
   677,686,701,702,717,749,794,837,861,889,893,902,905,909,921,922,937,938]

def newCost11 : List Nat :=
  [69,93,114,134,161,181,226,257,290,293,306,337,401,441,453,457,514,
   545,613,625,705,773,785,786,813,834,850,857,873,885,897,933,957,973]

/-- The three low-index residue classes have a single potential small-q
    exception each; all q at least 1024 in these classes are excluded. -/
def lowTail : List Nat := [1,6,26]

def certified (q : Nat) : Bool :=
  q%4==0 || q%4==3 ||
  previous256.contains (q%256) ||
  q%1024==29 || q%1024==297 ||
  previousCost11.contains (q%1024) ||
  newCost10.contains (q%1024) ||
  newCost11.contains (q%1024) ||
  lowTail.contains (q%1024)

def acceptedResidues : List Nat := (List.range 1024).filter certified

/-- Exact finite census of source-certified P1 n=16q+2 critical gateway
    exclusions, understood asymptotically for the three low-index tails. -/
theorem certified_density_695 : acceptedResidues.length = 695 := by decide

#print axioms certified_density_695
end BB6.Agent9Density
