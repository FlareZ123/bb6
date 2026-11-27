# M62 complete infinite-run proof by a two-phase regular zipper invariant

**27 November 2026.** This is a new **paper-level mathematical proof** that the Raw43 B1=0LE E0=1LA index 62 one-hole cylinder never queries its missing F1 transition. The literal transition table is

```
1RB0LA_1RC0LE_0RD1RF_1LD0RB_1LA1RA_0RE---
```

**Verification boundary:** The individual literal-machine instruction words, the arbitrary-tail carry identity, and 30,000 sampled admissible sections have been checked by an independent executable simulator. The inductive regular-language argument below is mathematical, **not yet compiled against original-source Lean**. Do not cite this as a source-certified `Cover` until a Lean translation and CI acceptance have been obtained. This is an intermediate result rather than a proof of BB(6).

## Notation and theorem

A configuration `F[L | R]` means the machine is in state F, the scanned cell is zero, `L` is the finite left tape word ordered from far-left to nearest the head, `R` is the finite right word including the scanned cell (or `R=ε` if the right ray is blank), and every other cell is zero. Concatenation is literal left-to-right. The invariant below always gives a left word ending in 1 and a right word starting in 0, so the partial machine never queries F1 at its section boundaries.

**Theorem (all completions).** From the blank tape, the partial machine has a defined run of every finite length, and every total machine compatible with its eleven assigned rows is nonhalting.

Let `1^k` and `0^k` denote unary words. Define three languages of *nonempty frames*; any displayed parameter `a,c>=0`, any inner `b_i>=1`, and `k>=0`:

```
O = {1^(5a) : a>=1}
  ∪ {1^(5a+3) (0 1^(5b_i+1))_(i=1..k) 0 1^(5c+3)}

A = {1^(5a+3) (0 1^(5b_i+1))_(i=1..k)}

B = {1^(5a+2)}
  ∪ {1^(5a+3) (0 1^(5b_i+1))_(i=1..k) 0 1^(5c) : c>=1}
```

In O's second component, `c>=0`; in A, the inner `b_i>=1`; in B's second component, `c>=1`. Let `O^{*}_{00} T` mean zero or more O frames followed by one terminal T frame, with **exactly two zero symbols** between adjacent frames:

```
T,  O 00 T,  O 00 O 00 T, ...
```

Define code words

```
W2(k) = 0^(5k+2) 101
W4(k) = 0^(5k+4) 101              (k>=0)
W = (W2(k) | W4(k))*
RA = {01} ∪ {01 0^(5k+1) 101 W : k>=0, W ∈ W}
RB = W
```

The two invariant states are

```
Phase A : F[L | R] with L ∈ O*_(00) A and R ∈ RA.
Phase B : F[L | R] with L ∈ O*_(00) B and R ∈ RB.
```

All braces describe languages, not any undecidable search; they are regular because all exponents have a fixed residue modulo five, and all interior blocks may be repeated finitely often.

## The four finite forward macros

A direct expansion of the eleven assigned instructions gives the following **literal first-F-return identities**, where the head moves right by exactly the length of the consumed right prefix. The left word `L` and right continuation `U` are arbitrary, provided the new scanned cell in `U` is zero (or `U` is empty, representing blank):

| Raw steps | Starting right prefix | Appended left word | Head advance |
|---:|---|---|---:|
| 18 | `010000` | `110011` | +6 |
| 8 | `010101` | `011111` | +6 |
| 11 | `00101` | `11111` | +5 |
| 11 | `0000101` | `1110011` | +7 |

The exact instruction-word traces (state/read pairs) are respectively:

```
18 : F0 E1 A0 B0 C0 D0 D0 D1 B1 E0 A1 A1 A0 B0 C0 D1 B0 C1
 8 : F0 E1 A0 B1 E1 A0 B0 C1
11a: F0 E0 A0 B1 E1 A0 B1 E1 A0 B0 C1
11b: F0 E0 A0 B1 E1 A0 B0 C0 D1 B0 C1
```

Each path stays within the consumed interval and reaches F scanning its immediate right successor. These identities can be checked by finitely many substitutions in the literal transition table; they do not require a search cutoff.

## The unbounded backward carry

Use the independently derived [arbitrary-tail all-parameter macro](M62CarryMacro.md). Starting in F0 with

```
... 00 1^r1 0 1^r2 ... 0 1^rN | 00000 ...
```

the first F return, after `S+18+9N` steps where `S=Σ_i r_i`, changes the displayed interval to

```
... 111 | 01 0^(r1-2)101 ... 0^(r(N-1)-2)101 0^(rN-1)101 ...
```

for `N>=2`; for `N=1`, the right string is `01 0^(r1-1)101`. The vertical bar here is the **new** head boundary (just before the zero after the new three 1s). The left prefix outside the displayed interval and the right suffix beyond the five zeros are untouched.

The trace factorization is

```
P A1^(rN+2) Q (A1^(r(N-1)+1) Q) ... (A1^(r1+1) Q) A1 R
```

with the fixed 13-, 8- and 3-transition words P, Q, R explicitly expanded in the linked carry-macro dossier. The A1 sweeps require only `rN>=1`, `r1>=2` for `N>=2`, and all internal `ri>=2`; those inequalities hold automatically for every B terminal frame.

This is **a first return** to F, not a long-run numerical coincidence. It avoids F1 at every intermediate step.

## Closure proof — exhaustive phase analysis

**Phase A → Phase B.** Every `RA` right string is one of the following.

* `R=01`, or `R=01 0^(5k+1)101 W` with `k>=1`: The 18-step forward rule consumes `010000` (the extra zeros are blank for `R=01`). In the latter case its right residue becomes `0^(5(k-1)+2)101 W`, an allowed `W2(k-1)` followed by `W`. The left terminal A frame gains two ones, turning it into an O frame: if it had one run, its terminal length becomes divisible by five; if it had multiple runs, its last residue changes from 1 to 3. Appending the rest `00 11` of `110011` creates a B terminal frame `11`. Thus both tapes satisfy Phase B.
* `R=01 0^1 101 W`: The 8-step rule consumes `010101`. Appending `0 1^5` to an A terminal frame makes a B terminal of the multi-run form (first residue 3, intermediate residues 1, final residue 0). The remaining right word is `W`. Again Phase B.

**Phase B → Phase B or A.** Every `RB=W` begins with one of these, or is empty.

* `R=W2(0) W`: The 11-step `00101` rule appends five ones. The B terminal frame stays in B (all run-length residues unchanged), and the right word becomes `W`. Thus Phase B is preserved.
* `R=W4(0) W`: The 11-step `0000101` rule appends `111 00 11`. Adding three ones turns a B terminal frame into an O frame: single terminal residue 2 changes to 0; multi terminal residue 0 changes to 3. The final `00 11` creates a new B terminal. The right word becomes `W`. Thus Phase B is preserved.
* `R=ε`, `R=W2(k) W` with `k>=1`, or `R=W4(k) W` with `k>=1`: In all cases the next five right cells are zeros, so apply the unbounded backward carry to the terminal B frame and the preceding `00`. If B is one run, its length is `5a+2`; the produced first right digit has gap `(5a+2)-1=5a+1`. If B is multi-run, the first run is `5a+3`, every inner run is `5b_i+1` (with `b_i>=1`), and the last run is `5c` (with `c>=1`). Their produced gaps are respectively `5a+1`, `5(b_i-1)+4`, and `5(c-1)+4`. Hence the new right word begins with exactly `01 0^(5a+1)101`, followed by allowed W4 tokens and then the untouched continuation after the first five zeros. The latter continuation is either empty, `W2(k-1)W`, or `W4(k-1)W`; therefore the resulting right word lies in RA.
  
  The left B terminal is consumed together with its preceding pair of zeros, leaving **three fresh ones**. If no outer O frame remains, the result is `111 ∈ A`. Otherwise those three ones extend the last outer O frame: a single O run of residue 0 becomes a single A run of residue 3, and a multi-run O frame whose last run has residue 3 becomes an A frame whose last run has residue 1 (and length at least six). Thus the new left word lies in `O*_(00) A`, so the return is in Phase A.

Every listed return uses a strictly positive number of primitive steps and never visits F1. There is no unlisted right-code constructor. This proves the two-phase invariant is closed under the literal machine's genuine first-return operation.

## Blank entry and nonhalting conclusion

Starting from the blank tape, the first twelve state/read pairs are

```
A0 B0 C0 D0 D0 D1 B1 E0 A1 A0 B0 C1
```

After these **exactly twelve** moves the machine is in state F scanning position +2, with left word `111` and right word `01`. This is Phase A with zero outer frames. Repeatedly apply the exhaustive closure proof: every return to F occurs after a positive finite number of genuine transitions, is again F scanning 0, and satisfies Phase A or B. Consequently there are arbitrarily long defined blank-origin prefixes, no missing-row query, and no halting step.

Because the eleven assigned entries are identical in every compatible total six-state machine, *every completion follows the same infinite execution*. The one-hole M62 cylinder is thus mathematically nonhalting.

## Scope, executable tests, and formalization route

This is a machine-specific mathematical result, not a Raw43 parent or all-six-state upper bound. The full proof is self-contained modulo finite substitution of the explicitly listed primitive words, plus the general carry trace. Independent tests include: 2,293 arbitrary-tail carry sections (committed [falsifier](M62CarryMacro.cjs)); 30,000 generated two-phase regular-language configurations tested under the exact literal simulator with zero failures; and the authentic blank prefix. **None of those finite tests substitute for the induction above**. A focused Lean formalization of the phase languages, four fixed `run0` rules, carry sweep and `NeverHalts` transport remains necessary for repository source acceptance. Prioritize this one leaf rather than rerunning large cutoffs or unrelated search portfolios.
