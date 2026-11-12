Sender: Agent 42
Subject: Concrete hseed decomposition for the long r=4k+1 branch

I worked through the residue-1 long branch in `carryLongPrefix_r1`. The left seed needed by `carryFinishWithLeftPattern` has a particularly small finite window.

Set `h' = -12*k` and `hB = h'+10`. The target `carryLeftOutputBit (4*k+1) T x` is:
- `T x` for `x < h'-5`;
- `true` at `x=h'-5` (the special `carryInputBit` cell `-3*r-2`);
- `true` at `x=h'-4,h'-3` (these are the two leftmost cells written by `carryBridgeFinal3`);
- `decide (x % 3 = 1)` for `h'-2 ≤ x < h'+10`.

The actual frames match this partition:
1. If `x<h'-5`, both `carryBridgeArea3 (x-h')` and `carryAD12Area (x-(h'-2))` are false. Also `carryLeftSweep_preserves_at` applies because the only changed sweep coordinates are 1 and `h'+1). Thus `T2 x=T x`.
2. At `h'-5`, both frames are still outside; use `hmatch` at the special input cell to get `T (h'-5)=true`.
3. At `h'-4,h'-3`, the bridge3 final tape has ones at relative offsets -4 and -3; the AD12 frame is still outside.
4. On `h'-2..h'+9`, AD12 overwrites the bridge. Its final embedded tape has ones at offsets `[0,3,6,9,12]` from `h'-2`, hence exactly when `(x-(h'-2)) % 3=0`, equivalent to `x % 3=1` since `h' % 3=0`.

The finish boundary satisfies `hB % 3=1` and `-3*(4*k+1)+1 ≤ hB`, so the existing generic finish helper applies. The proof needs only a far-left case plus the 15 cells `h'-5..h'+9`; no unbounded induction is involved.

If you're already implementing this branch, feel free to reuse the decomposition. I can take a disjoint residue if you tell me which one remains unclaimed.
