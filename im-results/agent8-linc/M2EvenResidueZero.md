# Marker-2 even residue-zero reset-prefix candidate

<badge label="Computational evidence only — not proved" color="warning" />

## Candidate theorem

The next root row after the existing marker-0 odd residue-one source is marker 2 with even index divisible by 8. The candidate general reset-prefix theorem is:

```lean
m2Even_residue0_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hk : 0 < k)
    (hbound : 8*k < 2^L) (ha : 0 < a) :
  run tm2 (resetPrefixCost 2 (8*k) a b)
    (s1Config L (8*k) 2 a 0 b h) =
  some (s1Config L (8*k-1) 1 (a+b+2) (2^b-1) 0
    (h+5+3*b))
```

The parameter order matters: the reset-prefix endpoint has `z=2^b-1` and right counter `b=0`. The already-existing counted-drain theorem then converts that endpoint to the final counted-increment target with `z=0) and right counter `2^b-1`.

For marker 2,
`resetPrefixCost 2 n a b = 71 + 12*(a+v2(n)) + 3*b`.
Since `v2(8*k)=3+v2(k)`, the candidate cost is
`107 + 12*a + 12*v2(k) + 3*b`.

## Reproducible simulation

The standard-library-only simulator is `m2_even_residue0_sim.py`. It implements the TM63 transition table and S1 tape encoding, then checks exact state, head, and complete finite-support tape equality against the proposed reset-prefix endpoint.

The deterministic JavaScript simulation run that motivated this file passed **240 cases**:
- 144 cases: `k=1..12`, `a=1..3`, `b=0..3`, minimal valid `L`;
- 96 cases: `k=1..8`, `a=1..2`, `b=0..2`, and `L) one or two larger than minimal.

Every case ended in state D at `h+5+3*b` with tape exactly equal to
`s1Config L (8*k-1) 1 (a+b+2) (2^b-1) 0 (h+5+3*b)`.
The Python script has been committed for independent reproduction; it has not been run in this environment.

This is finite computational evidence, not a universal proof. In particular, it does not establish the arbitrary-`k` theorem or transitive axiom-freedom.

## Why the existing residue-four bridge does not directly solve it

The existing `M2EvenQ4Prefix.lean` base case is `n=4`, with low blocks `d1,d1,d0`. For `n=8*k), the low blocks are `d1,d1,d1`. The old bridge's certified local input window includes two cells of the third block, so its exact input-match theorem cannot simply be reused unchanged.

The raw `n=8`, `a=1`, `b=0`, `L=4` run nevertheless reaches the proposed reset-prefix endpoint in 119 steps. This calls for a new base-`n=8` bridge or a more general counted carry proof; it is not evidence that the old 50-step bridge still applies.

## Connection to the universal LBinDec H-run

The candidate cost splits as
`(68 + 12*a + 12*v2(k)) + (39 + 3*b)`.
The second term has the same shape as the existing q4 suffix. The first term suggests a fixed base-`n=8` prefix with a variable `12*v2(k)` carry contribution. The H-run derivation in `CountedLBinDecHRun.md` supplies the relevant universal carry mechanism: a `4+12*i` run for a carry length `i=v2(k)`, with the fixed 4-step bridge absorbed into the base prefix.

This decomposition is a research hypothesis until the base bridge, arbitrary-context carry lemma, and exact tape equality are formalized.

## Root relevance

The existing root continuation after middle 15 has marker 2 and index `16*r = 8*(2*r)`. Thus this candidate, if proved, is exactly the next missing source row with `k=2*r`. The root's stronger index bound `16*r+15 < 2^L` implies `16*r < 2^L`; the root length bound also gives `L≥4`.

**Status:** useful new candidate and reproducible finite evidence only. Keep it in `im-results/`; do not promote it to `results/` or report it as a proved lower-bound step.


## Observed four-phase structure

The raw runs factor at exact intermediate configurations, not merely at the final endpoint. For the tested cases, the phases are:

1. **Initial left sweep:** `9*a+6` steps, ending in D at `h-(3*a+2)`.
2. **Carry bridge:** `62+12*v2(k)` steps, ending in E at `h-(3*a+2)+2`.
3. **E scan:** `3*a` steps, ending in E at the original head `h`.
4. **Q4 suffix:** `39+3*b` steps, ending in D at `h+5+3*b` with the exact reset-prefix target tape.

The total is
`(9*a+6)+(62+12*v2(k))+3*a+(39+3*b) = 107+12*a+12*v2(k)+3*b`.

For `a=1,b=0`, additional traces for `k=1..16` show that the carry bridge reaches its endpoint in exactly `62+12*v2(k)` steps. Its head path has maximum `hN+2` and minimum `hN-15-3*v2(k)`, where `hN=h-5`. Thus each extra factor of 2 in k extends the leftward excursion by three cells and the bridge by twelve steps. This is consistent with the generic H-run's `4+12*v2(k)` cost, with its fixed four-step bridge absorbed into the base 62-step bridge. That internal identification remains a proof hypothesis.

The simulator is being upgraded to check all four intermediate endpoints, so the phase decomposition is reproducible rather than inferred from total length alone.
