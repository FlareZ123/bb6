# Marker-1 even-L terminal macro: exact empirical law

**Status: strong computational conjecture, not yet proved.** This is the most promising terminal development for the current m=2,n=1 root path.

## Initial configuration

The simulator starts TM2 in state 3 at head 0 on

```
s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 0 0
```

with right-facing word `s0RightFacing 0`, where A,L≥1. Thus the left-facing word is

```
d1pow A ++ [1,0,1] ++ [0,0,1] ++ d1pow L ++ [1,1,0,1,1,1]
```

and the right-facing word is `[0,1,1,1,0,0,1,1,1]`. The simulator transcribes the original TM2 transition table; marker-0 controls reproduce the proved `59+12(A+L)` count.

## Observed even-L formula

For every tested even L, the run halts by the unique state-0/read-1 query. Let N be the final head coordinate (also the number of state-4/read-0 events in every tested run). The data fit the exact expressions

[
N(A,L)=10cdot 2^{A-1}(2^{L+2}-1)+7,
]

[
T(A,L)=rac{2N(A,L)^2+45N(A,L)+60(A+L)+52}{5}.
]

Here T counts successful transitions before the undefined halt query. The numerator is divisible by 5 because N≡2 (mod 5).

## Exact observed cases

| A | L | Final head N | Simulated halting steps T |
|---:|---:|---:|---:|
| 1 | 2 | 157 | 11,319 |
| 2 | 2 | 307 | 40,521 |
| 3 | 2 | 607 | 152,913 |
| 4 | 2 | 1,207 | 593,685 |
| 5 | 2 | 2,407 | 2,339,217 |
| 7 | 2 | 9,607 | 37,004,361 |
| 1 | 4 | 637 | 168,111 |
| 2 | 4 | 1,267 | 653,601 |
| 3 | 4 | 2,527 | 2,577,129 |
| 4 | 4 | 5,047 | 10,234,413 |
| 5 | 4 | 10,087 | 40,789,929 |
| 1 | 6 | 2,557 | 2,638,407 |
| 2 | 6 | 5,107 | 10,478,649 |
| 3 | 6 | 10,207 | 41,765,121 |
| 1 | 8 | 10,237 | 42,010,719 |

All listed runs were actually simulated to halt. The formula was evaluated independently from the observed output and matches every row. The q4-event count equals N in all cases.

The final tape also appears to have a simple form: the right side begins `11` followed by blanks, and the left side begins `1110` followed by a long periodic `100100100…` region. The exact full-tape normal form has not yet been stated or proved.

## Why this matters to the root

The authentic middle-34 root does not use L=3. It uses

```
tm63Length1 = tm63FirstSection.exponent + 5
tm63FirstSection = sectionResult 7 2 6 63
```

The seven marker stages are 2,1,0,2,1,0,2. Since the right counter remains odd at every stage and the exponent recurrence is `a' = a+b+δ_m` with `δ_0=1`, `δ_1=δ_2=2`, the exponent parity from a=6,b=63 evolves

```
even → odd → even → even → odd → even → even → odd
```

so `tm63FirstSection.exponent` is odd and `tm63Length1` is even. Thus the even-L marker-1 terminal law is the relevant branch for the authentic m=2,n=1 root endpoint.

## Formalization target

The key missing theorem is a parameterized exact run from the marker-1 S0 configuration to the halting query, for all A≥1 and even L≥2. A useful proof decomposition should expose:

1. a macro invariant for the state-4 scans and their 0/1 exit boundary;
2. the exact number `N(A,L)` of state-4/read-0 events and the final head coordinate;
3. the exact sum of the macro's step costs, yielding `T(A,L)`;
4. the final tape normal form, including the periodic left `100` region and the right `11` suffix.

The q4/0/1 halt criterion is exact from the transition table: state 0 is entered only from state 4 reading 0, and state 0 reading 1 is the only undefined transition. The formula and its quantified validity remain conjectural until a proof or independently checked macro certificate is produced.

## Reproduction

Run `marker1_terminal_experiment.cjs` from this directory. Example:

```sh
node marker1_terminal_experiment.cjs 1 3 6 50000000
```

This should halt at the values in the table. The script also records q4-zero/right-neighbor event counts.
