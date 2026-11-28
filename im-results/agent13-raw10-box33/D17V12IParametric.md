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


## Further universally quantified results (28 November, ~11:15 UTC)

The adjacent `Box33D17V12ICarry.lean` proves, for every `j : Nat` and arbitrary `r : Stream`,

```text
run (132 + 32*j) (phase j (1010100101000 ++ r))
  = some (phase (j+1) (1100000000101 ++ r)).
```

The proof uses an exact 64-step finite core plus the same two unbounded sweeps and universal 48+16j reset. This is not inferred from numerical growth and does not require a fixed blank suffix.

More generally `Box33D17V12IRelay.lean` proves the **finite-to-infinite relay lifting lemma**. Let `X,Y` be *arbitrary finite Boolean words*, `c` a natural number, and suppose the finite core is valid for all left and right streams:

```text
run c A(1101 ++ l, 010 ++ X ++ r)
  = some A(l, 11 ++ 010 ++ Y ++ r).
```

Then for every `j,r`, without any assumption about `r`,

```text
run (20+c+16*j) (phase j (X++r))
  = some (phase j (Y++r)).
```

The proof is a literal decomposition into `5+6(j+1)+c+10j+9` primitive transitions. Its other theorem, `universalSecond`, proves

```text
run (48+16*j) (phase j (00010000++r))
  = some (phase (j+1) (110000++r)).
```

The combination `packetLift` maps any appropriate arbitrary-tail finite core in `c` steps to a `68+c+32j` return that adds one outer `0010` block. This turns the hard **unbounded spatial repetition parameter** into a fixed-size Lean proof of the core and a reusable induction theorem. `generate_i_relays.py` emits such source theorem candidates for finite numerical guard prefixes; it never declares successful source acceptance. The adjacent extractor `unpack_i_generator.py` reconstructs the audited generator, SHA256 `e936ff293159f851a51c2e843d1bd779ce5f368e15529e574b7a8bfd0a07c3c0`.

### Source reconstruction and test

```bash
cd im-results/agent13-raw10-box33
python3 unpack_i_parametric.py
python3 unpack_i_carry.py
python3 unpack_i_relay.py
python3 unpack_i_generator.py
lean -o Box33D17V12IParametric.olean Box33D17V12IParametric.lean
LEAN_PATH=. lean -o Box33D17V12IRelay.olean Box33D17V12IRelay.lean
LEAN_PATH=. lean Box33D17V12ICarry.lean
python3 generate_i_relays.py /tmp/IExamples.lean 0x75 0x55 0x215 0x295
LEAN_PATH=. lean /tmp/IExamples.lean
```

The local proof was compiled with Lean 4.36.0-rc2. `#print axioms` reports only the ordinary `propext`, `Classical.choice`, and `Quot.sound` axioms for `relay`, `universalSecond`, `packetLift`, and `carryPacket`. Import into the original repository transition semantics and a globally closed blank-root invariant remain uncompleted.

## Payload return-map evidence and important counterexamples

The fixed `10101` prefix at one boundary produces the exact low-bit payload return map `F` in a second boundary, and `packetLift` can prove each finite guarded cylinder when its core passes `rfl`. For example, with integer payload notation converted to nearest-first words:

```text
F(1w) = 0w
F(000w) = 001w
F(011w) = 000w
F(01000w) = 00001w
F(0010000w) = 0000101w
F(00101000w) = 00000101w
```

These samples are **finite-guard identities**, not a complete total characterization of `F`. In particular, the separate guarded prefix `0011` immediately reaches the E1 halt, as does `010011`. An infinite invariant must distinguish the genuine payload orbit from such unsafe continuations.

An exploratory, untrusted iteration of `F` on blank-extended integer payloads beginning with `11` completed 100,000 section returns without encountering a halt. Every return after the initial two had prefix `000` or `001`, alternately (49,999 observations of each); largest active integer payload length was 66 bits. This **does not prove the infinite trajectory**, and the first long orbit is not a substitute for an inductive invariant. A prefix-tree search through depth 12 found 77 closed return/halt cylinders and 82 unresolved length-12 prefixes; these counts are discovery diagnostics, not a universal prefix partition theorem. For every fixed prefix length 4 through 21 considered, a sampled root-orbit even-boundary prefix had a deliberately changed six-bit continuation that halted within two return attempts. Consequently a simple finite-prefix safety cylinder is inadequate; the genuine orbit likely requires a more structured (possibly recursive or automata-theoretic) language.

The open question is the carry regime `001w` and how to identify a closed language of full payload streams containing the authentic blank-start sequence. Neither the root nor the entire D17V12 cylinder is closed by this partial result.
