import AffineMask
namespace BB6.Agent9AffineResidue

def lookup (r : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | p::ps => if p.1=r then p.2 else lookup r ps

theorem lookup_eq (f : Nat → Nat) (r : Nat) (rows : List (Nat × Nat))
    (hrows : ∀ p∈rows, f p.1=p.2)
    (hmiss : r∉rows.map Prod.fst → f r=0) : lookup r rows=f r := by
  induction rows with
  | nil => exact (hmiss (by simp)).symm
  | cons p ps ih =>
    by_cases he : p.1=r
    · simp [lookup,he,←hrows p (by simp)]
    · simp only [lookup,if_neg he]
      apply ih
      · intro q hq; exact hrows q (by simp [hq])
      · intro h
        apply hmiss
        simp [h,show r≠p.1 by omega]

def checkRows (k d : Nat) (rows : List (Nat × Nat)) : Bool :=
  rows.all fun p => localMask k d p.1 == p.2

theorem checkRows_append (k d : Nat) (a b : List (Nat × Nat)) :
    checkRows k d (a++b) = (checkRows k d a && checkRows k d b) := by
  simp [checkRows]

def checkKeys (k : Nat) (rows : List (Nat × Nat)) : Bool :=
  let keys := rows.map Prod.fst
  (nodes (k-1)).all fun p => keys.contains (p.r%2^k)

theorem descend_nil (k d : Nat) : descend k d []=[] := by
  induction d with
  | zero => rfl
  | succ d ih => simp [descend,ih]

theorem table_eq (k d r : Nat) (rows : List (Nat × Nat))
    (hrows : checkRows k d rows=true) (hkeys : checkKeys k rows=true) :
    localMask k d r=lookup r rows := by
  symm
  apply lookup_eq (localMask k d) r rows
  · intro p hp
    have hh := List.all_eq_true.mp hrows p hp
    exact beq_iff_eq.mp hh
  · intro hmiss
    have hnil : (nodes (k-1)).filter (fun p=>p.r%2^k==r)=[] := by
      apply List.filter_eq_nil_iff.mpr
      intro p hp hpr
      have he : p.r%2^k=r := by simpa using hpr
      have hh := List.all_eq_true.mp hkeys p hp
      have hm : p.r%2^k ∈ rows.map Prod.fst := by simpa using hh
      rw [he] at hm
      exact hmiss hm
    simp [localMask,hnil,descend_nil,pack]

/-- Count exact positive-width classes via their low and high bits.
The row/column pairs enumerate each residue modulo 2^(k+d) once. -/
def maskCount (d m : Nat) : Nat := if m=0 then 0 else (List.range (2^d)).countP m.testBit

def residueCount (k d : Nat) : Nat :=
  ((List.range (2^k)).map fun r => maskCount d (localMask k d r)).sum

def tableCount (k d : Nat) (rows : List (Nat×Nat)) : Nat :=
  ((List.range (2^k)).map fun r => maskCount d (lookup r rows)).sum

theorem residueCount_eq (k d : Nat) (rows : List (Nat×Nat))
    (hrows : checkRows k d rows=true) (hkeys : checkKeys k rows=true) :
    residueCount k d=tableCount k d rows := by
  unfold residueCount tableCount
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [table_eq k d r rows hrows hkeys]

#print axioms table_eq
#print axioms residueCount_eq
end BB6.Agent9AffineResidue
