# General TM63 S0/S1 encoder

This directory contains a Lean transcription of the physical source encoding
used by the TM63 champion's S0/S1 sections. It is an intermediate proof bridge,
not an academically publishable BB(6) result by itself.

## Source orientation

The pinned BusyCoq definitions in `verify/Helper.v` and the Inc0/S1 section
of `verify/SOBCv5.v` (around lines 10237–10275) determine the orientation:

- `l <* xs` is `Str_app xs l`: it prepends `xs` to the head-facing left
  stream.
- `<[x;y;z]` reverses the displayed physical block.
- The current head cell is the first element of the head-facing left stream;
  physical left-to-right order is its reverse.

Consequently, in head-facing order:

- `d0 = [0,0,1]`, physically `100`;
- `d1 = [1,1,1]`, physically `111`;
- `lh = [1,1,0,1,1,1]`, physically `111011`;
- `S0(l,a,z,b)` has left stream `BinDec(a,z) ++ l`;
- `S0`'s physical right side is `0 ++ 11100 ++ 111^(1+b)`;
- `S1(L,n,m,a,z,b)` has left stream
  `BinDec(a,z) ++ marker(m) ++ d0 ++ BinDec(L,n) ++ lh`.

The encoder is exposed as an actual `BB6Coverage.Config` in original D-state
index 3. The theorems `s0Config_left_cell` and `s1Config_left_cell` give the
exact correspondence between head-facing list positions and cells of the
original bi-infinite tape.

## Formal results

In `S1Encoder.lean`:

- `binDec_even` and `binDec_odd` mirror the source `BinDec_mul2` and
  `BinDec_mul2add1` equations.
- `binDec_mulpow2` is the repeated low-zero-bit expansion.
- `exists_odd_factor` gives (z=(2q+1)2^r) for every positive (z).
- `binDec_carryPrefix` proves
  `BinDec(a,z) = d1^r ++ d0 ++ BinDec(a-r-1,q)` when
  (z=(2q+1)2^r) and the residual (q) fits its declared length.
- `s1LeftFacing_carryPrefix` transports that expansion to the real S1
  D-head boundary.
- `s1PhysicalLeft_carrySuffix` reverses it into the physical
  left-to-right suffix `d0 ++ d1^r` immediately before the head.
- `s1Config_left_carryCells` states the same fact directly on the original
  TM63 tape, so counted local transition theorems can be applied without a
  second zipper or an implicit orientation change.
- `s1PhysicalLeft_m0_zero` gives the source physical word
  `111011 ++ 111^L ++ 100 ++ 10 ++ 111^a`; the right word is
  `0 ++ 11100 ++ 111^(1+b)`.

The length premise (q<2^{len}) is explicit. A caller with (z<2^a)
and a chosen 2-adic factorization must supply the corresponding residual
length inequality; this module does not silently assume it.

## Integration

The intended consumer is Agent 24's counted `Inc0` proof. For a positive
counter value, choose (q,r) with (z=(2q+1)2^r), instantiate
`s1Config_left_carryCells`, and compose the resulting source-level tape
boundary with the counted 12r carry and odd local template. The module does
not claim that the complete `Inc0` macro or BB(6) score has already been
proved.

Compile through the existing selective workflow:
`.github/workflows/agent48-s1-encoder-check.yml`.
