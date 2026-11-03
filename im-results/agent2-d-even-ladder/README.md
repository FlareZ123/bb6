# An even-depth E-ladder embedded in regular D-family sections

**Status (2026-11-03): intermediate source-derived mathematics and exact finite primitive-machine corroboration.** Agent 2. This is a new **even-depth parameter embedding** relative to the odd-depth bridge already documented by Agent 35. It does not decide the true blank-root machine, establish a BB(6) bound, or claim external novelty. The composed original-source proof has not been checked as one Lean theorem. Existing component universal machine theorems and local source-import checks have the stated provenance below.

> **Stronger result:** [Three-return periodic bridge](three-return-periodic-bridge.md) eliminates the fourth preliminary section. Its bounded, period-64 multiplier construction embeds **every even depth** after only three prior source-macro checkpoints, matching Agent35's odd-depth three-checkpoint construction. This README preserves the earlier, independently derived four-section route for traceability.

## Original machine and precise target

The literal D-start six-state table is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Write `I_n(s)` for state F scanning a zero, the *entire tape left of the head blank*, and right physical tape `1^n s 0^infinity`. Let `P_r=(01)^r`. Consider the synthetic regular-language E inputs
`X(k,q) = I_(3k+4)(P_q 1)`, which are in Agent 37's regular section family.

Agent 31 derived and independently numerically tested an exact **fourth F/0 endpoint** for every `v>=0, q>=3`, with `k=27v+7`:

```text
X(27v+7,q) --[four exact raw-machine source-macro endpoints]-->
I_(4096v+1162)(0 1^(2q-3) 0 1^6).
```

The four source-macro components are the explicit B/A/E branches of
[Agent 31's third/fourth classification](../agent31-d-exceptional/third-return-classification.md), composed from already source-verified original machine macro identities. The aggregate four-return source theorem and universal strict minimality were not separately imported/checked. Finite original raw checks exist in that dossier.

Agent 2's [`ETripleLadderIndex.lean`](../agent2-cryptid-continuity/ETripleLadderIndex.lean) establishes against locally assembled SHA-verified *original D source* that, for every `m,u,q,ys`,

```text
I_(3^(m+1)*(u+1)+1)(0(10)^q 1^(3m+3) 0 ys)
    --[totalCost m u q original primitive steps]-->
I_(3*8^m*(u+1)+1)(0(10)^(q+2m) 111 0 ys).
```

[`ETripleLadderSource.lean`](../agent2-cryptid-continuity/ETripleLadderSource.lean) certifies the exact E endpoints and all intervening first F/0 return times for the prepared packet, while [`ETripleLadderSafe.lean`](../agent2-cryptid-continuity/ETripleLadderSafe.lean) proves no primitive halting state through the endpoint. All locally compiled Lean claims reported only standard axioms, with exact-committed-byte CI still pending for some files. The source modules use `u+1` as multiplier below.

## Even-depth embedding: exact constructive lemma

**Claim.** For *every even natural depth* `m>=2`, there are explicitly computable nonnegative integers `v` and `q=(3m+6)/2>=6`, and an integer `U>=1`, such that the fourth F/0 endpoint of the regular input `X(27v+7,q)` is **exactly** the input for `m` consecutive E-triple-pairs source transitions:

```text
X(27v+7,(3m+6)/2)
  --[four source macro endpoints]-->
I_(3^(m+1)*U+1)(0 1^(3m+3) 0 1^6)
  --[m original-source E macro endpoints]-->
I_(3*8^m*U+1)(P_(2m) 0 111 0 1^6).
```

The additional E stage uses `ETripleLadderIndex.power_ladder_source m (U-1) 0 (1^6)`; its entire suffix is specified, and the first-return/minimality source result applies *within this E stage*. The first four endpoints remain source-composition claims, with no new assertion of universal minimality between them.

**Proof of existence, constructively, for all even m.**
Set `q=(3m+6)/2`. This is integral precisely when `m` is even, and `2q-3=3m+3`. It remains to choose `v>=0` with `3^(m+1) | 4096v+1161`. Here `4096=2^12` and `4096 ≡1 (mod 3)`.

Use base-3 digit lifting. Set `v_0=0`, `a_0=1161`. For each `j=0,...,m`, if `3^j | (4096v_j+1161)`, put `c_j=(4096v_j+1161)/3^j`. Choose the unique digit `d_j in {0,1,2}` with `c_j+d_j ≡0 (mod3)`, and define `v_(j+1)=v_j+d_j*3^j`. Then

```text
4096v_(j+1)+1161
 = 3^j(c_j+4096d_j),
```

which is divisible by `3^(j+1)` because `4096 ≡1 (mod3)`. Thus `v=v_(m+1)` is nonnegative, is less than `3^(m+1)`, and satisfies the required divisibility. Define `U=(4096v+1161)/3^(m+1)`, a positive integer. Consequently `4096v+1162=3^(m+1)U+1`. The packet lengths match because `2q-3=3m+3`. Substitute into the four-return formula, then apply the existing original-source E-ladder theorem. QED (parameter arithmetic and conditional composition of cited source identities).

This fills the **even-depth** parameter gap left by [Agent 35's prior odd-depth bridge](../agent35-d-regular-certificate/README.md). In combination, for every positive depth one can exhibit a *synthetic regular E section* whose exact source-macro itinerary contains arbitrarily many subsequent off-regular-language E-ladder endpoints. This does **not** imply any such section is reached from the genuine blank tape.

## Examples and independent primitive checker

The deterministic Windows-compatible CommonJS [`test-even-ladder.cjs`](./test-even-ladder.cjs) implements the full literal 11-live-rule six-state machine with a frozen halt condition. It records each **genuine physically blank-left F/0 return** and compares complete finite right physical tapes. It also checks the digit-lift divisibility for many even depths.

| m | q | v | k=27v+7 | fourth unary length | U | predicted final unary length |
|---:|---:|---:|---:|---:|---:|---:|
| 0 (vacuous E stage) | 3 | 0 | 7 | 1162 | 387 | 1162 |
| 2 | 6 | 0 | 7 | 1162 | 43 | 8257 |
| 4 | 9 | 54 | 1465 | 222346 | 915 | `3*8^4*915+1` |
| 6 | 12 | 783 | 21148 | 3208330 | 1467 | `3*8^6*1467+1` |
| 8 | 15 | 783 | 21148 | 3208330 | 163 | `3*8^8*163+1` |

An independent direct raw-TM simulation performed before writing the file observed:

- `X(7,3)`: first four physical returns at primitive times **999, 6320, 42665, 298593**, the fourth at `I_1162(0 1^3 0 1^6)`.
- `X(7,6)`: first six at **1011, 6332, 42677, 298605, 2105529, 14911650**. The fourth at `I_1162(0 1^9 0 1^6)`, fifth at `I_3097(P_2 0 1^6 0 1^6)`, sixth at `I_8257(P_4 0 111 0 1^6)`.
- The E subchain lasts `14911650-298605=14613045` raw steps, exactly the closed expression from [Agent 2's verification note](../agent2-cryptid-continuity/verification-note.md) at `m=2,U=43,q=0`. This is a redundant arithmetic check against the genuine primitive simulator.

All these numeric experiments are finite evidence, alongside the universal source-family arithmetic derivation. The larger m rows are **parameter constructions**, not brute-force run confirmations.

## Research use and remaining edge

Any proposed global invariant of the D machine's *regular* F/0 suffix language must address arbitrary-depth exceptional packets even for regular synthetic entries. The current constructive all-even bridge strengthens the previous all-odd one and supplies a Hensel-digit construction with small explicit parameters. It is a **method limitation** for finite-depth regular-language repair on all synthetic sections, not an impossibility proof for more powerful invariant languages, nor an all-time statement about the actual blank origin.

For promotion, the most valuable remaining work is one complete **unmodified-source** Lean import of Agent 31's full four-return composition and this parameter bridge plus Agent 2's exact first-return ladder, followed by independent root-relevance/novelty review. The missing genuine blank-entry reachability condition remains decisive. Preserve the exact distinction between source-derived endpoint identity and formal whole-orbit certification.
