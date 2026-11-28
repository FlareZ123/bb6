# Raw43 B1=1RE branch: complete source-accepted weighted Cover

## Result

The Raw43 branch obtained by fixing the previously undefined (B1) transition
to (1RE) is completely covered at weighted bound **4,044**.

In source, the branch parent is constructed from the canonical Raw43 prefix by
fixing

```text
D1 = 0RB
B1 = 1RE
```

in `BB6.Agent25Raw43B1RE.p`.  Its finite canonical cut has exactly **16**
residual quotient representatives:

```text
BB6.Agent25Raw43B1RE.remaining_count :
  remaining.length = 16
```

All sixteen residual families are discharged by independently source-checked
child theorems.  The final composition proves

```text
BB6.Agent25Raw43B1RE.all_completions
  (m : Machine) (hm : compatible p m) :
  WeightedBound 4044 m

BB6.Agent25Raw43B1RE.cover
  {B : Nat} (hB : 4044 ≤ B) :
  Cover (WeightedBound B) p
```

Thus every completion of this entire Raw43 B1=1RE branch satisfies the
weighted step bound 4,044.  This is a complete branch theorem; it is **not** a
complete Cover of the seven-hole Raw43 parent, whose other top-level branches
still contain unresolved source obligations.

## Source acceptance

GitHub Actions run **46151063756** completed successfully on source revision

```text
1e16f0f85e81c849edbf4c9a02e217d37e18f196
```

The accepted artifact is:

- artifact ID **15265523620**
- name `raw43-b1re-complete-proof`
- ZIP SHA-256
  `6718468f7e409a2d04d3d0d7453ea097b7e9c8527103470cc80dcaeeb957926e`

The final source closure compiled **1,411 project modules**.  The audited
theorem profiles are:

```text
BB6.Agent25Raw43B1RE.classified_all:
  [propext]

BB6.Agent25Raw43B1RE.all_completions:
  [propext, Classical.choice, Quot.sound]

BB6.Agent25Raw43B1RE.cover:
  [propext, Classical.choice, Quot.sound]
```

No `sorryAx` or `native_decide` appears in the accepted source audit.

## Proof structure

The source module `Raw43B1RECut.lean` builds a canonical partial-machine
audit at bound 4,044 and proves that exactly sixteen quotient residuals remain.
The composition module `Raw43B1RECompose.lean` proves that every one of
those residuals matches one of sixteen source-accepted child families, applies
the corresponding quotient-safe weighted theorem, and closes the full branch.

This result is directly reusable in the eventual Raw43 whole-parent
composition and therefore in the staged global Raw43 successor after the
current Canonical37 lineage is accepted.
