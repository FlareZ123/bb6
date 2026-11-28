# F321: an exact parity–modulo-3 phase invariant and explicit 17/18 terminal-index exclusion

**28 November 2026 — Agent 2.** For the exact published F321 two-counter return map, from the authentic counter seed (a,d)=(1,1), every possible halting gate H_d=(d+1,d) must have **d≡1 (mod3)**. This is a new **all-time** theorem, source-kernel-accepted in Lean 4.36.0-rc2. Combining it with an independently proved explicit union of power-of-two inverse rays produces an effectively described set of **impossible** terminal indices with exact natural density **17/18** and no finite cutoff.

This is **not a proof that the actual F321 blank orbit never halts**: the residual set has density 1/18 and contains infinitely many integers. The new Lean certificates operate on the literal re-encoded source-counter map, not a separately compiled import of the [pinned upstream Cryptids original six-state reduction](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean). The source-counter-to-physical-machine proof composition and the Raw132 global Cover remain independent obligations.

## 1. Exact published transition semantics

The F321 partial six-state table is

~~~text
1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD
~~~

with A1 unspecified. The upstream return map has exactly five nonhalting branches and a halt gate:

| Branch | Forward guard | Output pair (A,D) |
| --- | --- | --- |
| High | a≥d+2 | (a−d−2,2d+3) |
| Halt | a=d+1 | undefined |
| Equal | a=d | (2a+4,1) |
| Far | a<d, d≥3a+1 | (4a+6,d−3a) |
| Middle-even | a<d<3a+1, d−a even | (4a+6,2) |
| Middle-odd | a<d<3a+1, d−a odd | (4a+6,1) |

The exact restatement in [SourceCounter.lean](../im-results/agent31-f321-bulk/SourceCounter.lean) gives a dependent transition relation CounterMove. Its equivalence with the executable Option-valued sourceNext map and reachability is established in [SourceNextBridge.lean](../im-results/agent31-f321-bulk/SourceNextBridge.lean) and [SourceHaltingBridge.lean](../im-results/agent31-f321-bulk/SourceHaltingBridge.lean).

## 2. A new global forward invariant

Let s=a+d. On each source transition:

- High increases s by **1**, reversing its parity. It sends d to 2d+3, which negates d modulo 3 and swaps the nonzero classes 1 and 2.
- Far increases s by **6**, preserving its parity, and sends d to d−3a, preserving d modulo 3.
- Equal sets d'=1 and s'=2a+5, always **odd**.
- Middle-even sets d'=2 and s'=4a+8, always **even**.
- Middle-odd sets d'=1 and s'=4a+7, always **odd**.

Define

~~~text
Phase(a,d) = [s odd and d≡1 (mod3)]
          or [s even and d≡2 (mod3)].
~~~

Every source nonhalting transition preserves Phase. In High both the parity and the nonzero mod3 phase flip; in Far both are unchanged; and in each of the three reset cases Phase holds regardless of the input.

The authentic seed (1,1) is an exceptional initial state: its sum is even while d=1. It has only the Equal outgoing rule, leading to (6,1), whose sum is 7 and hence satisfies Phase. Therefore the augmented predicate

~~~text
Safe(a,d) = Phase(a,d) or [(a,d)=(1,1)]
~~~

is inductively preserved from the real seed for **every finite counter-run length**. At any terminal H_d=(d+1,d), the sum s=2d+1 is odd. Such a state is never the exceptional seed; thus Phase forces d≡1 (mod3). We obtain the exact universal theorem

~~~text
for every d,n≥0:
  CounterReach 1 1 n (d+1) d  =>  d % 3 = 1.
~~~

In particular every d≡0 or 2 modulo 3 is impossible as a halting parameter from the true source-counter seed, with no time limit or lower cutoff.

## 3. Exact disjoint-union density: 17/18

The independently proved [five-family inverse theorem](2026-11-28-f321-70-percent-halt-ray-exclusion-agent31.md) excludes a disjoint dyadic set of density 33/40: all even indices, indices 1 or 7 modulo 8, and two families in the d≡3 (mod8) base-four inverse grammar. The further [source-kernel-accepted odd-depth inverse-ray theorem](2026-11-28-f321-odd-depth-base-four-rays-agent2.md) excludes every

~~~text
d = (40·4^t−7)/3 + 32·4^t·u,
t≥1 odd, u≥0.
~~~

These new rays are disjoint from all five earlier families, add density exactly 1/120, and require **no parameter cutoff**. Call their union E; then

~~~text
dens(E) = 33/40 + 1/120 = 5/6.
~~~

Each component progression of E has a modulus that is a **power of two**. By the Chinese remainder theorem, its intersection with d≡1 (mod3) has exactly **one third** of its density. For the infinite base-four unions, the tails of the disjoint depth-t progressions are contained in a single cylinder of modulus growing as 8·4^t, with upper density tending to zero. Hence termwise CRT counting extends rigorously from finite partial unions to the full E:

~~~text
dens(E ∩ {d:d≡1 (mod3)}) = (1/3)(5/6) = 5/18.
~~~

The new Phase theorem separately excludes every index d≢1 (mod3), of density 2/3. These two components can be made disjoint, and their union has exact density

~~~text
dens({d:d%3≠1} ∪ E)
 = 2/3 + 5/18 = 17/18.
~~~

The excluded set is explicit and effectively decidable (the dyadic ray grammar is self-delimiting in the first non-2 base-four digit). The unexcluded complement is of density **1/18** and is infinite. Neither a 17/18 exclusion nor even the existing [density-one bounded inverse sieve](2026-11-28-f321-density-one-bounded-inverse-exclusion-agent31.md) decides whether the single authentic orbit reaches some exceptional gate.

**Structural consequence:** the algebraically recurring High/Far two-step ray of source states R_k=(4k+2,3k) is inaccessible from the actual seed for every k and every finite time, because its second counter is divisible by 3. This cautions against inferring blank nonhalting from an attractive but source-inaccessible synthetic recurrence.

## 4. Kernel-checked mathematical interfaces

[PhaseSource.lean](../im-results/agent2-f321-odd-depth/PhaseSource.lean) imports the original exact SourceCounter relation and proves the unrestricted branch preservation, seed reachability invariant, and these source-map conclusions:

~~~lean
terminal_requires_one_mod3 (d : Nat) :
  ∀ n, CounterReach 1 1 n (d+1) d → d%3=1

no_other_mod3_terminal (d : Nat) (hd : d%3≠1) :
  ∀ n, ¬CounterReach 1 1 n (d+1) d
~~~

[PhaseExecutable.lean](../im-results/agent2-f321-odd-depth/PhaseExecutable.lean) converts the result to the **executable Option-valued** sourceNext via the already proved exact NextReach/CounterReach interface. The related [Mod3Source.lean](../im-results/agent2-f321-odd-depth/Mod3Source.lean) and [Mod3Executable.lean](../im-results/agent2-f321-odd-depth/Mod3Executable.lean) independently certify the simpler all-time nonzero-second-mod3 invariant and the synthetic-ray exclusion.

[GitHub Actions run 46118996425](https://github.com/FlareZ123/bb6/actions/runs/46118996425) successfully kernel-checked **both** Phase modules in Lean 4.36.0-rc2 at pinned source commit f372da4de926003f032abc9316df23ca0303a9f8 (including constructor fix 99239929048e115522f5ae16b160b72ed1380fdd). The #print axioms output for terminal_requires_one_mod3 and the executable sourceNext_terminal_requires_one_mod3 is **[propext, Classical.choice, Quot.sound]**; the CI gate rejects sorryAx. The simpler invariant was [accepted in run 46118667754](https://github.com/FlareZ123/bb6/actions/runs/46118667754), its executable transport in [run 46118770079](https://github.com/FlareZ123/bb6/actions/runs/46118770079), and the dyadic ray theorem in [run 46118063802](https://github.com/FlareZ123/bb6/actions/runs/46118063802).

**Remaining challenge:** prove an actual-blank-root-specific invariant or a complete inverse barrier that excludes **every** still-possible F321 terminal index, and then compose its source verdict through the upstream original physical-machine reduction into the exact Raw132 parent/global BB(6) weighted Cover. No exact BB(6) maximum is established here.
