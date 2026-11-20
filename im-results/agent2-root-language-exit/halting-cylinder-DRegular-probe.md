# DRegular diagnostic against the @-d 108-step halting cylinder

**Status:** exact-integer exploratory calculation plus direct comparison with the external Lean proof's intermediate configurations. This is not a new halting proof.

## Target

The external formal target is
`A(3^108*k+C, [])` with
`C=1975700577069254261393123959451562008800234946348086`.
The wiki's 108-letter E/B suffix-rewriting word begins
`EEBBEBEEBEEEBBEBBEEBBEBEEBBEBBEEEBBEBBEBBEEBBEE...`.

The letters in that word are **not** to be identified naively with every branch label in the DRegular arithmetic table. The external Lean proof uses its own `A_step2` macro and explicit intermediate suffixes.

## First external A-macro checkpoint equals the DRegular first exit

The external proof file
[`BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean`](https://github.com/int-y1/proofs/blob/1929f57df4dd7afcc11c3f458e20526fd1f991e0/BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC0LB_1LE---.lean)
proves the first ten `A_step2` transitions from `A(3^108*k+C,[])` reach

`A(3^98*(8^10*k)+D1, [0,1,0,1,0,1,0,1,1])`

where

`D1=35925965576050291197954676646168812866911688985763244505`.

The suffix is `(01)^4 1`. Independently, exact BigInt evaluation of the repository's DRegular table for ten successful transitions from `(C,0,0)` reaches exactly

`L(D1,4,1)`.

The source-section encoding therefore identifies the first ten-step external A-macro checkpoint with the repository's first DRegular exit configuration. The next required external macro letter is E; the DRegular table has no regular successor at `L(D1,4,1)`, which is exactly where its regular suffix language stops.

## The next external checkpoint leaves the regular suffix language

The external proof's next ten `A_step2` transitions reach

`A(3^88*(8^20*k)+D2, [0,1,0,1,1,1,0,1,0,1,0,1,1,1])`

where

`D2=653274599173389056319717515476765122857837155218448003942322`.

Its suffix is `01011101010111`, which is not of the DRegular form `(01)^q1^b`. This is the precise first point where the regular `L(a,q,b)` model cannot represent the external A-macro orbit. Extending the suffix language to this state (and its successors) is more directly relevant than closing another isolated regular return.

## Existing q=4 source closure is a later return, not the next A-macro step

The DRegular exit `L(D1,4,1)` satisfies `D1=27*u+25`, with

`u=1330591317631492266590913949858104180255988480954194240`.

The existing
`ExceptionalEPacketClosure.exceptional_EE_all_reentry_or_reset`
theorem applies. Its E/E packet has

`c=(192*u+161, 2, 2*4-3)=(255473532985246515185455478372756002609149788343205294241,2,5)`.

Exact evaluation of the `PacketSafeExit.advance` definitions gives:

| Stage | Branch | a | q | p |
|---|---:|---:|---:|---:|
| input | — | 255473532985246515185455478372756002609149788343205294241 | 2 | 5 |
| 1 | B | 681262754627324040494547942327349340291066102248547451314 | 1 | 5 |
| 2 | B | 1816700679006197441318794512872931574109509605996126536842 | 0 | 5 |
| 3 | E | 4844535144016526510183452034327817530958692282656337431577 | 0 | 2 |
| terminal | B with q=0 | — | 0 | 2 |

The p2 B-zero source branch then returns to

`L(12918760384044070693822538758207513415889846087083566484211,1,5)`.

This is a later regular F/0 endpoint obtained by a longer source run. It is **not** the external proof's next A-macro checkpoint `A(D2,01011101010111)`. The fact that the q=4 source closure reaches another regular section does not make it the first A-macro return. The existing suffix-language synthesis explicitly warns that its rows do not establish first-return minimality in every case.

## Research consequence

The useful bridge is now sharply located:

1. The DRegular model and external A-macro agree at the first ten-step checkpoint `L(D1,4,1)`.
2. The next ten external A-macro transitions reach a nonregular suffix `01011101010111`.
3. The existing q=4 E/E + p2 source closure skips to a later regular endpoint, so it is an accelerator, not a substitute for the intermediate A-macro states.
4. The DRegular 3-adic shift theorem is therefore valuable on the first regular segment, but a complete proof of the 108-step route requires a generalized suffix-state model or a verified decomposition of each accelerated source return into the external A-macro checkpoints.

Do not compare the 108-letter E/B word directly with all DRegular branch labels; the first-prefix coincidence is not a proof of macro equivalence. Do not infer nonhalting or challenge the external halting theorem from this diagnostic.
