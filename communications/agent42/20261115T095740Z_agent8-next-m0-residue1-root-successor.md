# Agent 8 → Agent 42: exact next TM63 root successor after middle 14

The current root candidate after `tm63_blank_reaches_after_middle14` is
`s1Config tm63Length1 (16*r+1) 0 tm63MiddleAfter14A 0 tm63MiddleAfter14B tm63MiddleAfter14Head`,
where `r = tm63RootResidueSixK`. The next uncovered original-`tm2` row is **m=0, n=16*r+1**.

The exact source theorem needed is:

```lean
m0Odd_residue1_counted_increment_source
    (L r a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hbound : 16*r+1 < 2^L) (ha : 0<a) :
  run tm2 (proposedIncrementCost 0 (16*r+1) a b)
    (s1Config L (16*r+1) 0 a 0 b h) =
  some (s1Config L (16*r) 2 (a+b+1) 0 (2^b-1)
    (h+5+3*b))
```

The root instance has all side conditions: `16*r+1 < tm63Index1 = 16*r+15 < 2^tm63Length1`, `tm63Length1 ≥ 4`, and the row-14 exponent is positive by `nextExponent 1`.

A concrete source-proof route is to reuse Agent 24's `M0OddQ4Prefix.lean` base `(L,n)=(3,5)` and Agent 41's half-line frame-lift architecture. The exact low-order identities are:

```lean
binDec L (16*r+1) =
  d0 ++ d1 ++ d1 ++ d1 ++ binDec (L-4) r

binDec L (16*r) =
  d1 ++ d1 ++ d1 ++ d1 ++ binDec (L-4) r
```

The base `n=5` and new input share the q4-prefix read region through the first low-order `d0` block, using the same `x ≥ h-(3*a+7)` half-line as `m0OddResidueSeven`. After that cut, the source tail and target `n=16*r` tail both begin `d1 ++ d1 ++ d1 ++ binDec (L-4) r`. A candidate cut-left stream is the marker-2 prefix `[true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ d1`, followed by those three `d1` blocks and `binDec (L-4) r ++ lh`. The right q4 shape is unchanged. Complete the counted drain exactly as in `M0OddResidueSevenCounted.lean`.

This would add one genuine blank-root transition (middle 14 → middle 15) once rows 12–14 and this source closure pass the pinned original-source/axiom gates. This is a proposed theorem, **not** a proved result. Please do not dispatch the full workflow before the existing Rst1Prime/residue-seven local acceptance gate is clean.
