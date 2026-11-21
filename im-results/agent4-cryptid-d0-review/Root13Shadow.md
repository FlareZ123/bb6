# Thirteen-step 3-adic shadow of the authentic root (intermediate result)

**Status:** exact arithmetic computation on the repository's DRegular model and the committed external macro trace. Not yet a Lean theorem about the original TM trajectory. Reproduction script: `root13_shadow_check.py`.

## Finding

Let

`C = 1975700577069254261393123959451562008800234946348086`

be the empty-suffix parameter at the start of the external halting-cylinder macro path.

In the authentic-root arithmetic chain generated from `L(9,0,0)`, the section at index **31,777** has state `L(a,0,0)` and satisfies

[
a-C equiv 3^{13}pmod{3^{14}}.
]

Equivalently, `a = C + 3^13 p` for an integer `p` with

[
pequiv 1pmod 3,qquad pequiv43pmod{81}.
]

The root parameter has 44,970 bits. The congruence is exact to 14 powers of three: the difference is divisible by (3^{13}), but not (3^{14}).

This is a deeper shadow than the previously reported seven-step shadow at index 2,640.

## Why it shadows thirteen external macros

The external trace records each macro's affine parameter update in the form

[
n' = 8leftlfloorrac n3ightfloor+c_i
  = 8rac{n-r_i}{3}+c_i,qquad r_i=nmod3.
]

If the root and external parameters enter a macro with the same residue (r_i), and the same suffix, the same branch and macro argument apply. Their parameter difference is divided by three and multiplied by eight:

[
a_{i+1}-n_{i+1}=rac83(a_i-n_i).
]

Starting with (a_0-C=3^{13}p), the difference after (i) matching macros is

[
a_i-n_i=8^i3^{13-i}p.
]

Since (p
otequiv0pmod3), the input residues match for macros 1 through 13. The suffixes also match exactly, as shown by the external trace. After macro 13 the parameter difference is (8^{13}p), which is not divisible by three. Consequently the root's next input has residue 1, while external macro 14's input has residue 2: the paths diverge at macro 14.

## Exact matching prefix

| Macro | Branch | A_step2 argument | Root/external input residue | (v_3) of output-parameter difference | Output suffix |
|---:|:---:|---:|---:|---:|---|
| 1 | E | 13 | 1 | 12 | `0111111` |
| 2 | E | 21 | 1 | 11 | `01010111` |
| 3 | B | 5 | 2 | 10 | `010111` |
| 4 | B | 5 | 2 | 9 | `0111` |
| 5 | E | 21 | 1 | 8 | `01010` |
| 6 | B | 5 | 2 | 7 | `010` |
| 7 | E | 17 | 1 | 6 | `011111111` |
| 8 | E | 21 | 1 | 5 | `0101011111` |
| 9 | B | 5 | 2 | 4 | `01011111` |
| 10 | E | 27 | 1 | 3 | `010101011` |
| 11 | E | 35 | 1 | 2 | `0111111110111111` |
| 12 | E | 21 | 1 | 1 | `01010111110111111` |
| 13 | B | 5 | 2 | 0 | `010111110111111` |

At macro 14, the external input residue is 2 and the root input residue is 1.

## Scope and limitations

- The root index is the section/return index used by `check_root17.py`, not a primitive-step count.
- The arithmetic chain is replayed using `check_eighth_root.py`'s exact integer DRegular transition and exceptional-reentry functions. The root state at index 31,777 lies ten DRegular transitions before the sixth exceptional endpoint.
- A scan of the DRegular states through the episode-20 arithmetic lookahead found no exact hit of the external cylinder (aequiv Cpmod{3^{108}}). Among states with ((q,b)=(0,0)), the largest observed (v_3(a-C)) was 13, uniquely at index 31,777. This scan covers DRegular states and the explicit reentry endpoints in that chain; it is not a scan of every primitive configuration inside exceptional packets.
- The 13-step arithmetic shadow becomes a theorem about the original TM only after the DRegular source-section path to index 31,777 and the first 13 external `A_step2` source macros are joined by the raw-machine/CryptidBoundary conjugacy. Agent 44's explicit-`K` and transition-conjugacy work is directly relevant.
- This does not establish halting. It identifies a substantially deeper near-alignment and the exact point of divergence.

## Reproduction

Run `python3 root13_shadow_check.py` from this directory in the repository checkout. The script imports the existing `check_eighth_root.py` arithmetic model and reads the committed `macro_trace.json`; it prints the 13 matching residues and checks the macro-14 divergence.
