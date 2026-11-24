# F418: complete arithmetic event partition and exact primitive costs

**Status.** The literal two-hole table `1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---` has a kernel-checked source reduction from the blank tape to the arithmetic event orbit (see [F418Root.lean](F418Root.lean)). The exact normal-return formula and backward odd-only predecessor restrictions below are also Lean checked. No all-time root verdict or BB(6) upper bound is claimed.

## Encoding and event table

Write D_d(N,a,n) for a D/0 configuration whose left 1s are at zero-based nearest-first positions d+5i for binary 1-bits i of N. The right word is 101a followed by pairs 1b_i, b_i the low-first digits of positive n, ending in its leading 1 and then blank zeros. d=3 is the regular alignment; an empty left word has no alignment. The 670-successful-step seed is D_3(0,1,39464).

Let w=bitlength(n), t=2^w-n. In regular alignment the two registers both increment until right overflow. A regular a=0 overflow moves the left alignment to 2, changes a to 1, and sets the right counter to 2^w. A regular a=1 overflow moves the left alignment to 4, changes a to 0, and sets n to 2^(w-1). In both cases the new left register is N+t. The word-level justification is carry_to_B followed by right_inc_zero/one or right_overflow_zero/one; the apparent trailing zero cells can always be supplied as blank padding. For d=3 or N=0, only the standard increment/overflow cases are needed.

For shifted N>0 write N=2^j(2Q+1). Before the next shifted collision, the new regular low counter counts from 0 to z: z=2^j-1 for d=1,2; z=2^(j+1)-1 for d=4. Indeed, the first shifted 1 at index d+5j is untouched until all j lower regular digits are 1, and for d=4 the additional regular bit at index 3+5j must also be 1. The intermediate normal increments use exactly the same carry and right-increment lemmas, leaving the shifted high suffix unchanged. Let m=n+z at the collision.

| Alignment | condition | new alignment | new N | new a | e in new n=(4m+1+2a)2^e | successful collision steps |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | j even | 3 | Q | 0 | 5j/2 | 15j+14 |
| 2 | j odd | 2 | Q | 1 | (5j+1)/2 | 15j+21 |
| 4 | j even | 1 | Q | 1 | (5j+4)/2 | 15j+30 |
| 4 | j odd | 2 | Q | 0 | (5j+3)/2 | 15j+23 |
| 1 | any | F/1 terminal query | — | — | — | 5j+2 |

These are precisely reset2_even, reset2_odd, reset4_even, reset4_odd and offset1_hazard after substitution j=2k or 2k+1. The two reset output pairs 11,1a prepend the digits 1,a to the old n, following e zero digits, hence the right-register formula. The reset consumes the j lower aligned blocks and the first shifted 1, leaving the shifted tail Q; the exact number of cells removed from the old left word is respectively 5j+4, 5j+5, 5j+8, 5j+7, which gives the new alignment in the table.

## Why the event partition is exhaustive on the blank orbit

Maintain n>N, positive n, and in shifted d=1,2 with N>0, also t>N. A standard phase-1 state always has N=0 and a gap t with odd part >1. A d=4 state has a=0, n=t=2^W and 0<N<t with N's odd part >1. The seed meets this invariant: t=26072=8*3259.

A regular a=0 overflow has N+t<2^w, exactly the new right gap. A phase-1 overflow starts with N=0; the gap t is positive and <2^(w-1) since its odd part exceeds 1. This is the required d=4 invariant. In d=1,2, the equality N=2^j(2Q+1) gives t-z>=Q+2. In d=4, N<2^W gives j<W and 2^(j+1) divides 2^W, so t-z>=Q+1. Thus in every shifted phase the predicted collision precedes right overflow. No intermediate overflow case is omitted.

For either reset, new width w'=w+e+2 and new gap is
```
t' = (4(t-z)-1-2a)2^e.
```
Its odd factor is >1 (d=2: t-z>=Q+2; d=4: a=0, t-z>=Q+1); both n' and t' exceed Q. These are precisely the universally quantified arithmetic facts in standard_zero_overflow, standard_one_overflow, shifted12_budget, shifted4_budget, reset12_safe and reset4_safe. Because a d=4 N is not a power of two, Q>0 there. Consequently any even-j d=4 reset leads to a nonempty d=1 state which necessarily reaches F/1 via offset1_hazard before any other overflow. An odd-j d=4 reset returns to d=2. A d=2 phase with odd j consumes a 1-bit and continues, or empties its left register and becomes standard phase 1; an even j returns to standard phase 0. Empty left registers introduce no new cases. This proves the invariant inductively and every macro consumes finitely many positive successful steps.

**Root halting criterion (paper derivation):** the literal machine halts iff an even valuation occurs at a d=4 checkpoint. The initial d=4 N=26072 has j=3, so only subsequent d=4 entries matter. Such entries can arise only when a d=2 episode consumes all its bits using odd j. If its last j is odd, the next d=4 valuation is e=(5j+1)/2, since the new gap has that valuation. The fatal case is therefore exactly an episode whose N has only odd-position 1-bits and whose final relative j is 3 mod 4. Equivalently, the distance between its highest two 1-bit positions (or from virtual position -1 for a singleton) is 0 mod 4. **An odd-only N is not automatically fatal:** final j=1 mod 4 safely resets back into d=2. This remaining regular terminal language must be excluded on the actual orbit, or reached.

## Collapsed normal return

At D_2(N,1,2^W), with 0<N<2^W, suppose the least even-position set bit is at index 2p. Iterate over the successive low 1-bits until that bit is removed. For each relative j put e=floor((5j+1)/2) and update C=(4C+2^(j+2)-1)2^e, E=E+e+2, initially C=E=0. All earlier j are odd, so their consumed lengths j+1 are even. The last j is even. Total consumed length is 2p+1, and the total exponent increase is **E=5p+2**, since an odd j contributes 5(j+1)/2 and the even final j contributes 5j/2+2. After the final reset the standard phase-0 configuration has n'=2^(W+E)+C, N'=floor(N/2^(2p+1)). Its next right overflow returns to a pure-power d=2 checkpoint:
```
N_next = 2^(W+5p+2) + floor(N/2^(2p+1)) - C
W_next = W+5p+3.
```
The earlier safety invariant proves this expression is positive and <2^W_next; subtraction is ordinary integer subtraction. The first normal-return seed reached from the 670-step seed is (N,W)=(268311341,29). For p=0, C=3 and N_next=2^(W+2)+(N-7)/2, so M=N+7 satisfies M_next=2^(W+2)+M/2. A p=0 run consumes only zero low bits of M. For an odd-only episode use the general event table instead.

## Exact normal-return and odd-only predecessor restrictions

A normal phase-1 episode consists of odd valuations ending at the first even valuation. For its consumed length L=2p+1, exponent E=5p+2, and tail Q, define the correction C by:
- last valuation 2r: C=(2^(2r+2)-1) 2^(5r);
- first valuation 2r+1 followed by t: C=(2^(2r+3)-1) 2^(5r+3+E(t))+C(t).

[F418NormalReturn.lean](F418NormalReturn.lean) proves the exact iteration N'=2^(W+E)+Q-C, W'=W+E+1, and the four-event seed checkpoint (N,W)=(268311341,29) from the source-connected seed. [F418ReturnBounds.lean](F418ReturnBounds.lean) proves C<2^(E+2p) (strictly stronger C<2^(E+2p-1) for prefixes starting with an odd valuation), C>=3*2^(E-2), C>2^E for p>0, and L<=W, Q<2^(W-L).

**Necessary conditions for an odd-only output:**
- Borrow Q<C: the input must be the top singleton N=2^(2r), W=2r+1, r odd. Every other borrow produces two adjacent top 1-bits, one of which is at an even index. The exceptional output is 2^(5r)(2^(2r+2)+1).
- No borrow Q>=C: N'=2^(W+E)+R, R<2^(W-L), W+p odd; if p>0 then W>=7p+4. The top bit is separated from the lower remainder by at least E+L+1 positions.

Both modules compiled locally with Lean 4.36.0-rc2 against the exact three arithmetic dependencies, with standard axioms only (propext, Classical.choice, Quot.sound). This excludes many candidate predecessors but does not establish that the actual orbit avoids an odd-only checkpoint. The next target is a backward constraint on high bits of Q-C and the history of inserted top bits.

## Exact counted costs

Let s(x) denote binary popcount. In z ordinary increments from left x, right n, the total successful cost is
```
I(x,n,z)=40z+10(s(x)-s(x+z))+4(s(n)-s(n+z)).
```
This follows because a normal left carry costs 10v2(x+1)+10 and the right increment costs 4v2(n+1)+16; the sum of v2(k) over x<k<=x+z is z+s(x)-s(x+z), by counting multiples of powers of 2. For a standard overflow include its final increment in I, then add 5 if old a=0 or subtract 9 if old a=1, the differences from the corresponding word-rule costs. For a shifted collision add I(0,n,z) and the collision cost in the table. Add the initial 670 successful transitions and one additional halt attempt if required by the scoring convention. No count is a halting lower bound unless F/1 is actually reached.

## Reproduction and remaining gate

- `lean F418Arithmetic.lean` with Lean 4.36.0-rc2 checked the arithmetic theorem file locally, no sorryAx. The original source word rules and seed were recompiled from exact Git blobs retrieved via the connector after direct clone failed (DNS). Full source-import composition is now compiled; see the section below.
- `python f418.py --events 10000` passed the raw 670-step seed and 3603 seeded synthetic event/cost comparisons, then replayed 10,000 arithmetic events without a terminal query (d=2, a=1, N width 34499, n width 34500, successful-step-count bitlength 34504). This is bounded computation, not all-time safety.
- A separate exploratory run of 100,000 collapsed normal returns remained in the regular case; width reached 860094 and the largest p observed was 116. No probability assumption can turn this into an all-time proof. The useful next problem is the regular-language exclusion under the collapsed map, not repeated longer finite replay. An actual all-time decision is still needed before global frontier grafting.

## Kernel-checked arithmetic orbit and terminal-language equivalence

`F418EventSystem.lean` defines a normalized, deterministic arithmetic event map with five state constructors, explicit binary valuation extraction, the counter-width/gap invariant `Safe`, and a concrete seed. `safe_advance` and `seed_orbit_safe` establish preservation for every finite orbit prefix. `advance_none_iff` proves that only a nonempty alignment-1 collision terminates the map.

`F418Episodes.lean` defines the inductive binary language `OddChain N last` and proves `episode_partition`, `fatal_episode`, `recoverable_episode` and `seed_termination_iff`. The latter states that some arithmetic iterate is `none` **iff** some reachable alignment-2 state satisfies `OddChain N last` with `last % 4 = 3`. The proof does not assume that the particular seed avoids this language. It checks the initial phase-1 overflow is not a terminal gateway, then traces any terminal gateway backward to a fatal episode; the other direction constructs a finite path to alignment 1. The recoverable case `last % 4 = 1` exits to alignment 2, phase 0.

Local reproduction (Lean 4.36.0-rc2, from this directory):
```sh
lean -o F418Arithmetic.olean F418Arithmetic.lean
LEAN_PATH=. lean -o F418EventSystem.olean F418EventSystem.lean
LEAN_PATH=. lean F418Episodes.lean
```
All printed axiom sets are subsets of `propext`, `Classical.choice`, `Quot.sound`. There are no added axioms or `sorryAx`. These are arithmetic-model theorems; their exact source-level connection is proved below. The open problem is the actual seed's fatal-language reachability, not the event case partition.

## Source-level equivalence (18:30 UTC)

The reduction now has a complete Lean 4.36.0-rc2 proof starting from the literal partial table and the blank tape. `F418TapeEncoding.lean` establishes blank-padded word and configuration equivalence, transport through primitive moves and finite runs, and the arbitrary-width register encoding and carry decomposition. `F418SourceEvents.lean` constructs positive counted primitive runs implementing every defined safe arithmetic event (`advance_source`) and a successful primitive prefix reaching the missing F/1 instruction for every terminal event (`terminal_source`). `F418Root.lean` checks the exact 670-step seed, composes finite arithmetic prefixes, and proves:

```lean
theorem source_termination_iff : (∃ k, finiteRun machine k finiteBlank = none) ↔
    ∃ s, Reaches EventSystem.seed s ∧ Fatal s
theorem source_nonhalt_iff : NeverHalts machine ↔
    ¬ ∃ s, Reaches EventSystem.seed s ∧ Fatal s
```

All these results have axiom sets contained in `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`. The proof is unbounded; the event duration is a positive existential witness rather than the separately derived closed cost formula. In a terminating orbit the first undefined instruction is F/1, never E/1. The root decision is now exactly one unbounded arithmetic reachability question, not a gap in machine simulation.

To reproduce, copy `../agent8-coverage-contract/Frontier.lean` and `../agent32-source-queue/SourceFiniteSemantics.lean` to a temporary directory alongside all nine F418 Lean files; from there set `LEAN_PATH=.` and compile in order: Frontier, SourceFiniteSemantics, F418Rules, F418Seed, F418Arithmetic, F418EventSystem, F418Episodes, F418TapeEncoding, F418SourceEvents, F418Root. Run `lean -o NAME.olean NAME.lean` for each. The exact input files used were Git blobs Frontier `115438c4f244b5416a91be4dd7a3f12103d5448d`, SourceFiniteSemantics `22418a75661de5978f9f5b50455c399ffc79a1f9`, F418Rules `ba93f60187b25571a03e8b50aeb8e47ce7911f5d`, F418Seed `1c78f0b4b3d818ec001a82d59a03f76b08038a7c`.
