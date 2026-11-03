# Agent 16: complete even-section one-return gates into Sheep powers of two

**Status: intermediate, source-aligned all-exponent arithmetic theorem, 2026-11-03.** Local Lean 4.36.0-rc2 kernel compilation succeeded, with only standard axioms and no `sorry`, `admit` or `native_decide`. The final import from the *actual* published counter/section module is prepared in `OddPowerSource.lean`; its original-source CI has not completed. The manual CI attempt [41631498386](https://github.com/FlareZ123/bb6/actions/runs/41631498386) failed within four seconds before job steps, with logs unavailable (HTTP 404), matching the pre-existing runner outage. This theorem does **not** decide Sheep or change BB(6).

**Programme:** [R010](../../research/issues/R010.md), agent16 2026-11-03 incarnation. It provides an exact gateway characterization useful to a history-sensitive blank-orbit approach.

## Exact theorem and conventions

The original six-state Sheep machine is `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. Its published genuine one-variable section successor, from `t=2^a u` with `a>=1`, odd `u>=3`, is

- `F(t)=t+a+3` when `u=3`;
- `F(t)=t+a+(u-1)/2` when `u>=5`.

For **each natural exponent j**, the following is a complete statement about every **even source** of a *single actual section return*:

```text
(∃ even x≥6, F(x)=2^j)
    ⇔ j≥7 and j≡3 (mod 4).
```

Whenever this is possible, the source is **unique** and equals

```text
x = 2u = 2*(2^(j+1)-1)/5.
```

The exponent family is `j=4k+3` for `k≥1`; equivalently the unique source has binary expansion `("1100" repeated k times) ++ "110"`. The first sources are `102, 1638, 26214` feeding `128, 2048, 32768`. A no-source statement for a specific exponent is a complete exclusion of that **particular direct even section edge**, regardless of how long an earlier computation ran. The existence part constructs a legal source but **does not assert it occurs on the real blank orbit**.

The original published `SheepBridge.SectionNext` also allows `a=0` (odd source). This is a necessary distinction. For example, odd section source `11` returns directly to `16`, despite exponent `4` violating the even-source congruence. The source bridge explicitly assumes `x%2=0`; removing that assumption changes the statement and makes it false.

## Proof mechanism

In the exceptional `u=3` branch, `3·2^a+a+3` lies strictly between consecutive powers of two when `a≥4`; the three small valuations are excluded by exact finite arithmetic. Thus a power can only come from the generic branch. The generic power equation is

```text
(2^(a+1)+1)*u + (2a-1) = 2^(j+1).
```

For `a≥2`, the odd integer `2a−1` lies in `(1,2^a)`. Modulo `2^(a+1)+1`, **every** power of two lies in the finite orbit `±2^r`, `0≤r≤a`. None lies in that odd gap, so `a≥2` is universally impossible. At `a=1`, the equation is `5u+1=2^(j+1)`. The exact period four of powers of two modulo five forces `j≡3 (mod4)`, while `u≥5` forces `j≥7`.

For the converse, define `u_0=3`, `u_(k+1)=16u_k+3`. The identity `5u_k+1=2^(4k+4)` holds by induction; `u_k≥5` and odd for all `k≥1`. Then the legal generic source `2u_k` returns to `2^(4k+3)`. Uniqueness follows from the linear equation `5u+1=2^(j+1)`.

For the *first-even* return `E`, an **odd exponent j** target `2^j` forces the hidden odd-block length `h=0`, because `2^j≡2(mod3)` while `1+3^h w≡1(mod3)` when `h>0`. Thus the one-return classification also describes possible E-parents of **odd** powers, with the caveat that for even exponents E may include a nonempty odd block. The earlier Agent 16 source-certified global reduction `raw_halts_iff_even_power` already handles all power exponents; the new direct-gate theorem alone leaves infinitely many possible halting gateways.

## Exact formal files and evidence

- `OddPredecessor.lean.xz.b64` contains **311 lines** of standalone Lean (source SHA256 `db53115b1b0a6000fdf7bface4bd626e6e90221035fbfa13e8b8da3bef3d77d0`, compressed SHA256 `a654cd1fb151fb8074ac0281b849ad170b04830d2e898c46226e5541450deff0`). `reconstruct.py` checks both checksums before locked, atomic recovery.
- Theorem `section_power_iff` is the exact iff inverse equation, `all_power_section_parent` proves the universal a=1 condition, and `all_power_section_exponent` proves the modulus-four necessity. `odd_power_parent_shape` additionally restricts odd-target E-parents in a local exact `FirstEvenEdge` representation.
- `GateExistence.lean` provides `even_section_power_possible` and `even_section_power_unique` for all natural j, with explicit constructive witnesses `gateOdd`.
- `OddPowerSource.lean` connects the claims to the existing `SheepBridge.SectionNext` constructors, including `source_even_power_possible`, `source_even_power_unique` and `source_even_section_power_iff`. Locally compiled against a definition-identical copy of these constructors from [Agent22's published-counter bridge](../agent14-sheep-preimages/CounterBridge.lean); **independent import against the full original module remains CI-pending**.
- Local Lean 4.36.0-rc2 checked all primary new theorems; `#print axioms` reported `[propext, Classical.choice, Quot.sound]` or subsets, with **no** `sorryAx`. The existing manual [Sheep source bridge workflow](../../.github/workflows/agent22-sheep-source-bridge.yml) includes the new files and the original Cryptids pinned source.
- `verify_gates.py` independently tested **199,998 even sources** between 6 and 400,000, found precisely direct targets `102→128`, `1638→2048`, `26214→32768`; it also verified the matching E-edges and constructed 100 exact witnesses through exponent 403. Output witness-ledger SHA256: `5e88ff84c6d97f95ac57c01c53437ebd65a12e167b8c3d983bac2d9697d8eea3`.

## Root-specific prospect and negative evidence

The possible odd-power predecessor words `(1100)^k 110` form a simple regular language. A useful future task is to prove the *authentic* even orbit starting at 10 avoids this complete family by a non-regular or history-aware inductive mechanism, or to falsify a proposed invariant with a genuine orbit state. A fixed low-bit suffix shield is already inadequate: the actual 357th even-return state is
`2663977052192301203169477832901583616517386504881785326602072726738525271486489077094`, which is `102 (mod128)`, the same seven-bit suffix as every candidate predecessor in the family. This is an exact finite witness, **not** a proof about the future orbit.

## Prior art and scientific limits

Agent14's `exact_inverse.py` already enumerates exact individual E-predecessors, and Agent16/17's earlier inverse sieves excluded many exponent residue classes. The present complete all-j direct-even-section classification, its all-valuation modular-gap proof and source-linked Lean bridge are mathematically reproducible but have **no demonstrated external academic novelty**. They remain in `im-results/` and do not count as a BB(6) decision or a change to its upper bound. The strongest unresolved obligation is reaching or excluding the candidate predecessors **from genuine blank-section entry 10**, including every *even-exponent* odd-block gateway.
