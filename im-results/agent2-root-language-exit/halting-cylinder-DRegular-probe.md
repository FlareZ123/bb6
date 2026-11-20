# DRegular diagnostic against the @-d 108-step halting cylinder

**Status:** exact-integer exploratory calculation; not a Lean theorem and not a halting proof.

## Target

The external formal target is
`A(3^108*k+C, [])` with
`C=1975700577069254261393123959451562008800234946348086`.
The wiki's 108-letter E/B word begins
`EEBBEBEEBEEEBBEBBEEBBEBEEBBEBBEEEBBEBBEBBEEBBEE...`.

## First DRegular exit from C

Using the arithmetic table transcribed in `im-results/agent2-root-language-exit/DRegularFirstExit.lean`, exact BigInt evaluation from `(a,q,b)=(C,0,0)` gives the first 11 branch labels

`EEBBEBEEBEE`

and the first exceptional state

`(a,q,b)=(35925965576050291197954676646168812866911688985763244505,4,1)`.

The parameter satisfies `a=27*u+25`, where

`u=1330591317631492266590913949858104180255988480954194240`.

Thus the existing q≥3 source family
`ExceptionalEPacketClosure.exceptional_EE_all_reentry_or_reset`
is applicable to this state.

## Concrete q=4 packet normalization

The E/E packet formula gives

`c=(a,q,p)=(192*u+161,2,2*4-3)`

that is,

`c=(255473532985246515185455478372756002609149788343205294241,2,5)`.

Applying the exact `PacketSafeExit.advance` arithmetic to this packet gives the following guarded-normalizer trace:

| Stage | Branch | a | q | p |
|---|---:|---:|---:|---:|
| input | — | 255473532985246515185455478372756002609149788343205294241 | 2 | 5 |
| 1 | B | 681262754627324040494547942327349340291066102248547451314 | 1 | 5 |
| 2 | B | 1816700679006197441318794512872931574109509605996126536842 | 0 | 5 |
| 3 | E | 4844535144016526510183452034327817530958692282656337431577 | 0 | 2 |
| terminal | B with q=0 | — | 0 | 2 |

The `p2_packet_reentry_or_E` B-zero source branch then returns to the regular section

`L(12918760384044070693822538758207513415889846087083566484211,1,5)`.

This is the output formula `L(8*k+9+p,1,5)` with terminal `k=(d.a-2)/3` and `p=2`. The arithmetic calculation selects the regular-return side of the p2 disjunction; a Lean proof should reduce the concrete `normalizeWithCount c` result and select that branch explicitly.

## What this does and does not establish

- The DRegular table reproduces the first 11 symbols of the external word exactly.
- The q=4 exit is not an unhandled mystery: the existing E/E packet theorem and p2 packet normalizer provide a source-level route back to a regular section for this concrete parameter.
- Under the natural alignment, the E/E route and packet normalization have the pattern needed to continue the target prefix. However, the output regular section has unary parameter
  `12918760384044070693822538758207513415889846087083566484211 ≡ 0 (mod 3)`,
  so its next DRegular branch is A, whereas the external word's seventeenth symbol is B.

This is **not** a contradiction of the external halting proof. It shows that the naive identification “one DRegular transition/source return = one letter of the external A/B/E word” is not yet justified. The source contract proves a run to a later regular section; it does not by itself prove that this is the first external A-macro return. There may be intermediate A(n,r) macro boundaries inside the source path, or the external macro uses a different stopping convention.

## Next proof obligation

Prove a first-return/decomposition theorem relating each DRegular source run (and each exceptional packet closure) to the exact sequence of external A(n,r) macro transitions. In particular, locate all A-section returns inside the q=4 E/E + p2 normalization path and identify which one is the state after the sixteenth E/B symbol. Only after that decomposition is formal should the DRegular 3-adic shift theorem be used to transport the 108-letter target cylinder.

Do not infer nonhalting, or invalidate the external halting theorem, from this diagnostic mismatch.
