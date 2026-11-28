# An exact unbounded two-packet return map for Raw10 D17/E0=12, machine I

**Status:** original-machine transition code copied literally into a standalone Lean 4.36.0-rc2 stream model. The full local source compiled with no errors on 28 November 2026. The exported `MacroI.oddPacket` and `MacroI.evenPacket` have transitive axiom profiles `[propext, Classical.choice, Quot.sound]` and **no** `sorryAx` or `native_decide`. A CI import into the unchanged repository source is not yet completed, and neither theorem is an all-blank nonhalting proof. The archive and checksum-checked extractor are adjacent to this note.

## Exact machine and semantics

The row-code table is

```text
[8,24,11,18,1,13,17,3,12,0,4,21]
1RB1RF_1LC0RE_0LA0LD_0LE1LA_1RC---_1RA0LF
```

The stand-alone two-way stream simulator has states A–F, lists of left/right bits in **nearest-first** order, a right stream including the scanned bit, initially all-zero left stream `z`, and `run n` exactly n primitive, nonhalting transitions. `word(w,r)` prepends finite word `w` and `rep(w,j,r)` prepends `j` copies. For every natural `j` and arbitrary infinite tape tail `r`, define

```text
P(j) = 01010010 (0010)^j
phase(j,r) = (state A, left=z, right=P(j) ++ r)
```

The *universally quantified* exact statements are:

```text
oddPacket j r:
  run (108 + 32*j) (phase j (11000 ++ r))
    = some (phase (j+1) (10101 ++ r))

evenPacket j r:
  run (110 + 32*j) (phase j (10101000 ++ r))
    = some (phase (j+1) (11000001 ++ r))
```

Both preserve the arbitrary suffix bit-for-bit, move to the next outer `0010` block, and guarantee no halt anywhere in the stated finite segment. They are not just simulations at selected j: the proof is induction in j, with exact 6-step right-pump and 10-step left-pump identities and 28/40/42-step finite relay cores.

## Mechanism

The shared symbol transport is:

```text
run  6 A(l,0100 r)       = A(1101 l,r)
run 10 A(1101 l,11 r)    = A(l,110100 r)
```

Thus a rightward sweep across j copies of `0100` takes `6j` transitions, and the inverse relay over j left-hand `1101` blocks takes `10j` transitions. The elementary word-conjugacy

```text
010(0010)^j = (0100)^j 010
```

aligns the repeated blocks at the start; `01010(0100)^j010 = 01010010(0010)^j` restores the canonical return boundary. In both packet rules, finite cores perform all effects on the payload outside these pumps.

The exact proof factorizes the odd packet into `(60+16j)+(48+16j)=108+32j`, and the even packet into `(62+16j)+(48+16j)=110+32j`. All four quantified component identities, stream algebra and packet-composition theorems are in `Box33D17V12IParametric.lean`.

## Reproduce

```bash
cd im-results/agent13-raw10-box33
python3 unpack_i_parametric.py
lean --version # requires Lean 4.36.0-rc2 (from project toolchain)
lean Box33D17V12IParametric.lean
```

Expected source SHA-256: `77e88d80bdf0023a825a3e49bf27a48ebc9807e7336a5ae4690cbca016ec2f5f`. Check `#print axioms MacroI.oddPacket` and `#print axioms MacroI.evenPacket` at the end of the reconstructed source.

## Unresolved blank-orbit obligation

Machine I is one of two hard leaves not yet closed in the D17/E0=12 cylinder; the other is `[8,24,11,8,1,13,17,18,12,5,2,0]`. The actual blank orbit visits packet configurations, but the two packet rules do **not** alone form a closed invariant, because their respective outputs are not universally required inputs for the next packet. For example the synthetic `phase(0,tail)` with tail integer `0x195` (nearest-bit-first encoding) reaches the E1 halt in 29 primitive steps, despite satisfying `tail ≡ 21 (mod 32)`. This falsifies the tempting blanket safety claim for all mod-32 payloads. A root-specific inductively invariant digit grammar or a stronger cross-packet/carry rule is needed before one can assert machine-I nonhalting, let alone a full Raw10 cylinder bound or BB(6) solution.

**Immediate best next test:** derive exact parameterized carry rules for `phase(j,10101001 ++ r)`, which occurs along the genuine orbit but is not covered by `evenPacket`. Connect the resulting rules to a root-containing closed regular or recursively generated language. There is no new BB(6) upper bound from the present result.
