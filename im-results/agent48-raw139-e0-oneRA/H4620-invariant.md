# OneRA H4620: all-completion nonhalting and weighted Cover

**Status:** proved locally by Lean 4.36.0-rc2 against the original repository's compiled semantic dependencies from accepted artifact 15166454197. The exact [H4620.lean](H4620.lean) source (commit d619ef09b52509942ec6e6f4702299a16e7f3d2a, Git blob f535078320e7ef584f007f3ebecedc8602da8fe3) exports `BB6Coverage.Agent48.H4620.never` and `BB6Coverage.Agent48.H4620.cover B` for every natural B. All audited declarations use only standard axioms; there is no sorryAx or native_decide. This is one exact partial-table leaf, not a complete OneRA parent, Raw139 Cover, or global BB(6) decision. The parent generator must consume this leaf by literal table equality. A fresh full-source CI closure has not been run for this file.

## Exact table and invariant

Partial table `[7,24,11,21,14,9,12,16,3,11,18,23]`. The sole undefined row is A1. Let C(l,k,y) denote A scanning zero, left ray 1^(2l+1) followed by implicit blanks, right ray 1^(2k), separator 0, then a finite little-endian binary word of value y. The Lean proof represents the scanned zero explicitly and keeps the exact finite word, including any zero bits; it does not rely on equality modulo trailing blank padding.

The following returns exist in positive finite time:

- k>0: C(l,k,y) -> C(l+1,k-1,y+1).
- k=0 and y odd: C(l,0,y) -> C(0,l+1,(y+1)/2).

The first uses A/B to enter F, an F1 rightward sweep, an exact binary C/D carry including the implicit-blank overflow case, then a three-step E/C/D leftward sweep. The second enters C directly at the leading binary one, uses the same carry, and sweeps left to implicit blank. Each elementary framed transition is proved by definitional equality for arbitrary untouched tails, and the sweeps by induction. The arithmetic map is a consequence of `value_inc`, not an assumed macro.

From the genuine blank start the machine reaches C(0,2,1) after exactly 37 moves; this entry is checked by reduction (`first`). For any n>=2, start C(0,n,n-1), transfer n times to C(n,0,2n-1), which is odd, then turn to C(0,n+1,n). Hence there are arbitrarily long live prefixes using only assigned transitions. `never_of_growth` transfers the inductive zipper trace to the original infinite-tape semantics for every compatible completion, and `cover` derives the weighted bound vacuously.

## Proof interface and reproduction

```lean
BB6Coverage.Agent48.H4620.never (m : Machine)
  (hm : compatible ctr m) : NeverHalts m
BB6Coverage.Agent48.H4620.cover (B : Nat) :
  Cover (BB6.Agent13BlankDelay.WeightedBound B) ctr
```

Use Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). The local check used the `build/` olean closure from artifact 15166454197 (downloaded without alteration) with imports SweepPumping, FastFAR and WeightedNonhaltLeafAdapter. The exact source SHA-256 is 858a7cc7fbcc9e793b5907fa8f2f898f4f31af53654633493b0f848dd0512c75. `lean H4620.lean` returned 0. Audited `transfer` and `turn` use [propext, Quot.sound]; `epoch`, `never` and `cover` use [propext, Classical.choice, Quot.sound]. The remote Git blob matches the locally checked bytes.

No external novelty claim. The nearest next step is exact table matching and parent consumption alongside the other OneRA residuals. The remaining E0=1RA child partition and global roster are not discharged by this theorem alone.
