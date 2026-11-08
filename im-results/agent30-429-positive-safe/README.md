# Cryptids #429: the entire positive-Junc return block contains zero C/0 instructions

## Exact claim and proof status

For the original #429 zipper transition table, let
`J(u,v,w) = junc u v w`, `T(N,v) = juncPosFullTime N v`, and
`runSafe` be the source interpreter guarded against executing an instruction
from state C while scanning 0. The file [PositiveSafe.lean](PositiveSafe.lean)
proves the unbounded statements

```lean
theorem junc_positive_safe (u v w : Nat) (hw : 2 ≤ w) :
    runSafe (4*v+10) (junc (u+1) v w) =
      some (junc u (v+2) (w-2))

theorem junc_positive_iter_safe (N U v w : Nat)
    (hU : N ≤ U) (hw : 2*N ≤ w) :
    runSafe (juncPosFullTime N v) (junc U v w) =
      some (junc (U-N) (v+2*N) (w-2*N))
```

It also proves the direct all-prefix conclusion `junc_positive_iter_no_czero`:
for each `t < T(N,v)`, the original, unguarded zipper `run` succeeds
at time `t`, and the reached source configuration has
`(state == 2 && !current) = false`.
This removes every possible C/0 halting gateway *within* all consecutive
full positive-`u` transitions, for arbitrary natural parameters satisfying
the full-return inequalities.

**Proof status:** successful unmodified-repository Lean 4.36.0-rc2
[source audit, CI 42528345611](https://github.com/FlareZ123/bb6/actions/runs/42528345611),
commit `a0ac4fb0a7a9766acebf4076a57a9641c5c0e786`. The workflow
compiled the original dependencies and this module, printing normal Lean
logical axioms without `sorryAx`. No exact decision from an initially blank
tape follows from these prepared-configuration transitions.

## Mechanism and relation to the shared proof programme

The proof factors the primitive positive-`u` return into (i) four
preparation steps, (ii) `2(v+1)` A/0, B/1 right-sweep steps, and
(iii) `2(v+2)` A/1, F/1 left-sweep steps. Each factor has a source-level
`runSafe` certificate, with symbolic tails and arithmetic parameters.
The all-parameter induction composes them; a second induction covers
`N` consecutive positive-`u` returns. The use of Agent 1's
[guarded interpreter](../agent1-429-w4-boundary/W4CZeroSafe.lean)
gives a semantically precise all-prefix exclusion.

The earlier [source Junc return](../agent6-429-one-sided-excursion/BB429JuncHeadExcursion.lean)
already proved the endpoint and cost by the unrestricted transition
interpreter. This note's additional claim is the *absence of C/0 at every
internal primitive instruction*, including all repeated positive-`u`
returns. It complements Agent 1's [exact C/0 census in the right-one
zero-`u` branch](../agent1-429-w4-boundary/W4CZeroCount.lean).

The quantified result applies to prepared `junc U v w` configurations.
Its missing implication is **authentic root coverage**: one must prove
that every C/0 on the genuine all-zero-tape #429 trajectory is covered
by a sufficient chart entry/exception grammar, and account for the
other branches (including `w=0,1` and the zero-`u` cases).
For the physical halting criterion see [Agent 32](../agent32-429-raw-parent/README.md):
the machine halts iff a genuinely reachable C/0 scans a marked immediate
right neighbor. No global bound or BB(6) exact value has been established.

The result is retained in `im-results/` because external novelty and
blank-root impact are not established.
