import ClosedCertFast

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CascadeEvenPre887T3T6

open CascadeResetInverse

/-- The signed numerator on the n=887 canonical even spine. -/
def signedZ887 (j : Nat) : Nat :=
  8*2^887 + 2*887 + 3 - 2^(j+1)*(2*887+3)

/-- The spine state y_j, so 2*y_j+5=signedZ887(j). -/
def ray887 (j : Nat) : Nat := (signedZ887 j - 5)/2

/-- First odd parent on the t=3 arm (odd-band scale 884). -/
def t3Root (j : Nat) : Nat :=
  16*(signedZ887 j / 81) - 2^887 - 889

/-- The sixteen actual t=3 depths on the n=887 spine. -/
def t3Depths : List Nat :=
  [42,96,150,204,258,312,366,420,474,528,582,636,690,744,798,852]

/-- Five t=3 roots have a further t'=0 odd parent at scale 883. -/
def t3LeafDepths : List Nat := [96,258,420,582,744]

/-- The five terminal t'=0 children of the t=3 roots. -/
def t3Leaf (j : Nat) : Nat :=
  let q := t3Root j
  let e := (2*q+5)/3
  2*e - 2^886 - 888

def t3Leaves : List Nat := t3LeafDepths.map t3Leaf

/-- The sole t=6 first-tier parent at depth 474 (odd-band scale 882). -/
def t6Root : Nat :=
  128*(signedZ887 474 / 2187) - 2^885 - 887

/-- Its unique even parent at scale 882; this state is terminal. -/
def t6Leaf : Nat := 2*t6Root - 2^885 - 882

/-- All seventeen first-tier t=3/t=6 parents of the canonical spine. -/
def sideRoots : List Nat := t3Depths.map t3Root ++ [t6Root]

/-- The 23-state backward-closed cone: 17 first-tier roots and 6 leaves. -/
def sideCone : List Nat := sideRoots ++ (t3Leaves ++ [t6Leaf])

/-- Each listed side root is an exact ResetParent of its canonical spine state. -/
def sideParentPairs : List (Nat × Nat) :=
  (t3Depths.map (fun j => (t3Root j, ray887 j))) ++
  [(t6Root, ray887 474)]

theorem sideParentPairs_valid :
    sideParentPairs.all (fun p => p.1 ∈ parentsFast p.2) = true := by
  decide

theorem sideParentPairs_source (p : Nat × Nat)
    (hp : p ∈ sideParentPairs) : ResetParent p.1 p.2 := by
  have h := (List.all_eq_true.mp sideParentPairs_valid) p hp
  exact (parentsFast_iff p.1 p.2).mp (List.contains_iff_mem.mp h)

/-- Exact second-parent census for all sixteen t=3 roots. -/
theorem t3_parent_lists_exact :
    t3Depths.all (fun j =>
      parentsFast (t3Root j) =
        if j ∈ t3LeafDepths then [t3Leaf j] else []) = true := by
  decide

/-- Exact second-parent census for the single t=6 root. -/
theorem t6_parent_list_exact : parentsFast t6Root = [t6Leaf] := by
  decide

/-- All six second-tier states are terminal in the exact inverse grammar. -/
theorem sideLeaves_terminal :
    t3Leaves.all (fun u => (parentsFast u).isEmpty) = true ∧
      parentsFast t6Leaf = [] := by
  constructor <;> decide

theorem sideRoots_length : sideRoots.length = 17 := by decide
theorem sideCone_length : sideCone.length = 23 := by decide
theorem sideCone_nodup : sideCone.Nodup := by decide

/-- The 23 states are closed under every exact ResetParent edge. -/
theorem sideCone_closed : closedCertFast sideCone = true := by
  decide

/-- None of the seventeen first-tier t=3/t=6 branch roots, nor any of their
    six side children, is reachable from the genuine blank C(2,0) root. -/
theorem sideCone_no_root (u : Nat) (hu : u ∈ sideCone) :
    ¬ CascadeSweep.ReachC (2,0) (u,0) :=
  closedCertFast_excludes u sideCone sideCone_closed hu (by decide)

#print axioms sideParentPairs_source
#print axioms t3_parent_lists_exact
#print axioms t6_parent_list_exact
#print axioms sideLeaves_terminal
#print axioms sideCone_closed
#print axioms sideCone_no_root

end CascadeEvenPre887T3T6
