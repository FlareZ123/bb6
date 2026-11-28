# Raw43/B1LE/E0LF residual 559: sweep decomposition toward a Lean proof

Status: **computationally derived / not yet a Lean theorem**.  This note records
an exact symbolic decomposition checked against the residual transition table
for multiple parameters.  It is intended to be translated into
`SweepPumping.lean` lemmas.  Do not cite it as a proved nonhalting result yet.

Machine:
`1RB---_1RC1LE_0RD1RF_1LD0RB_0LF0LE_1RA0RB`.
Only A1 is unassigned.

The previously observed family can be written in zipper form

```
family n =
  <F,
    011 ++ rep(011,4*n+1) ++ rep(01,2*n) ++ 0101101101,
    []>
```

and direct simulation gives

```
run0 table (448*n+612) (family n) = family (n+1)
```

for the checked parameters.  The family is reached from blank at step 170,
so this would prove nonhalting once the parameterized recurrence is kernel
checked.

## Exact constant local transfers found

The following schemas were exhaustively tested over small arbitrary left/right
tails and match the residual table.  They are deliberately stated as intended
Lean `rfl` lemmas; they still need kernel checking.

```
start41:
  run0 table 41 <F, 0::L, []>
    = <E, L, 00110011>

left15:
  run0 table 15 <E, 1101++L, R>
    = <E, 1::L, 011++R>

left14:
  run0 table 14 <E, 101++L, 0::R>
    = <E, 1::L, 011++R>

finish31:
  run0 table 31 <E, 1101101, R>
    = <E, [], 0011011++R>

turn16:
  run0 table 16 <E, [], 00110110++R>
    = <E, [], 0000010110++R>

prelude21_C:
  run0 table 21 <E, [], 00000101101++R>
    = <C, 1101100101101, R>

right6_C:
  run0 table 6 <C, 1::L, 11++R>
    = <C, 110++L, R>

right3_C:
  run0 table 3 <C, 1::L, 101++R>
    = <C, 1101++L, R>

finish11_CE:
  run0 table 11 <C, 1::L, 10011++R>
    = <E, 1101++L, 01++R>

prelude21_F:
  run0 table 21 <E, 1100++L, 011++R>
    = <F, 1110101++L, R>

right6_F:
  run0 table 6 <F, 11++L, 11++R>
    = <F, 1110++L, R>

right3_F:
  run0 table 3 <F, 1::L, 011++R>
    = <F, 1110++L, R>

finish8_FE:
  run0 table 8 <F, 1::L, 01001++R>
    = <E, 110++L, 001++R>
```

## First large phase

From `family n`, `start41` gives

```
<E,
  1 ++ rep(101,4*n+2) ++ rep(01,2*n+1) ++ 101101,
  00110011>
```

Then:

- `left15` swept `4*n+2` times costs `60*n+30`;
- `left14` swept `2*n+1` times costs `28*n+14`;
- `finish31` costs 31.

Total: `88*n+116`, reaching

```
P1 n =
<E, [],
  00110110 ++ 1^(4*n+2) ++ rep(110,4*n+2) ++ 0110011>
```

and `turn16` reaches

```
P2 n =
<E, [],
  0000010110 ++ 1^(4*n+2) ++ rep(110,4*n+2) ++ 0110011>.
```

## Middle large phase

The `P2 n -> P3 n` segment costs exactly `224*n+260`.

First half:
- `prelude21_C`;
- `right6_C`, `2*n+1` times;
- rotate the remaining leading 1 against the periodic word;
- `right3_C`, `4*n+1` times;
- `finish11_CE`;
- `left15`, `4*n+3` times;
- `left14`, `2*n+1` times.

Cost: `112*n+100`.

Second half:
- `prelude21_F`;
- `right6_F`, `2*n+1` times;
- `right3_F`, `4*n+2` times;
- `finish8_FE`;
- `left15`, `4*n+4` times;
- `left14`, `2*n+2` times;
- `finish31`.

Cost: `112*n+160`.

The target is

```
P3 n =
<E, [],
  00110110 ++ 1^(4*n+4) ++ rep(110,4*n+4) ++ 011>
```

and another `turn16` reaches

```
P4 n =
<E, [],
  0000010110 ++ 1^(4*n+4) ++ rep(110,4*n+4) ++ 011>.
```

## Final phase progress

Direct simulation verifies

```
run0 table (136*n+204) (P4 n) = family (n+1).
```

The first `24*n+39` steps are already factored enough to expose the next
sweeps.  At that point the exact configuration is

```
<C,
  rep(110,4*n+3) ++ rep(10,2*n+2) ++ 1100101101,
  10110011>.
```

This comes from `prelude21_C`, a `right6_C` sweep of `2*n+1`
iterations, a six-step turn, and a `right3_C` sweep of `4*n+2`
iterations.  The remaining `112*n+165` steps are a left-moving transfer
over the two periodic blocks followed by a fixed finish.  Simulation shows a
15-step repeated transfer moving one `110` block from the left side to the
right side while retaining a sentinel `110`; this needs a small
sentinel-aware induction lemma rather than the existing unrestricted
`sweepL` theorem.

## Next proof action

Formalize the constant transfers above as `rfl` lemmas, use
`sweepL`/`sweepR` plus `rotate`/list associativity for the first two
large phases, then add one sentinel-preserving sweep lemma for the final
phase.  This should replace residual 559's 9,922-state BiDFA certificate with
a compact structural nonhalting proof.
