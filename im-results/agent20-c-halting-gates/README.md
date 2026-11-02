# Agent 20: Machine C exact halting-parameter exclusions

**Status:** source-connected Lean 4.36.0-rc2 mathematical intermediate. The original Machine C and exact BB(6) remain open. This is an all-time restriction of possible halting *section inputs*, with no claim that any surviving input is blank-reachable.

Machine: `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. Exact genuine blank-entry arithmetic section: `(5,1)`.

## Starting point

Agent 15's source-checked `blank_halts_iff_two_parametric_families` in [BlankParam.lean](../agent15-c-halting/BlankParam.lean) characterizes blank stopping as reachability of one of these inputs at some section time:

- Low family: `(1,k)` with `k+3*m+4=2^(2*m+3)`.
- High family: `(2*j+3,k)` with `k+j+3*m+5=2^(2*m+2)*(j+3)`.

The source-checked `blank_section_mod4` from [Agent38SectionParity.lean](../agent38-c-section-mod4/Agent38SectionParity.lean) proves a reachable odd-right-counter input with sum of counters congruent 2 modulo 4 must be the initial `(5,1)`. Direct evaluation shows the initial input does not immediately halt, so **no halting section input in that forbidden parity class is reachable**.

## New universal exclusions

The core, exact Lean theorem `Agent20Gate.blank_halts_iff_refined_eight` proves blank halting **if and only if** some genuine blank-reached section input lies in these restricted families:

- Low: `k+3*m+4=2^(2*m+3)`, `m%4 != 1`, `m%8 != 4`.
- High: `k+j+3*m+5=2^(2*m+2)*(j+3)`, `(j+m)%4 != 0`, and `m%2 != 0 OR (j+3*m)%8 != 3`.

The forbidden low classes cover 3 of 8 parameter residues. The forbidden high classes cover 5 of 16 residue pairs in `(j,m) mod 4` and `mod 8` counting; these are modular proportions, **not densities of reachable states, candidate machines, or halting likelihoods**.

Derivation:

1. On the low family, `k ≡ -3m-4 (mod 4)`, so `m ≡ 1 (mod 4)` forces `k` odd with `1+k ≡2 (mod 4)`.
2. On the high family, `k ≡ -j-3m-5 (mod 4)`; if `j+m ≡0 (mod 4)`, `k` is odd and `2j+3+k ≡2 (mod 4)`.
3. For low `m≡4 (mod 8)`, the exact equation gives `k≡0 (mod 8)`. For high `m` even and `j+3m≡3 (mod 8)`, the high input has first counter `1 (mod 4)` and right counter `0 (mod 8)`. Agent 15's source-connected all-time theorem `blank_no_one_eight_family` excludes every genuine blank-reachable section `(4*u+1,8*(v+1))`. In each halting family the positivity and size bounds are obtained by the exact source theorem `section_halts_iff_diophantine`, so zero-right exceptions are eliminated.

An additional source-checked theorem in `SectionRightOne.lean` establishes the exact section predecessor of **every** output with right counter 1: the sole input is `(1,0)`, producing `(5,1)`. Source-verified section positivity then proves `run secNext t (some (5,1))=some(a,1)` implies `t=0,a=5`. The source-verified unique affine predecessor lemma for output `(1,4)` forces input `(3,1)`, therefore `(1,4)` (the low gateway with `m=0`) is blank-unreachable.

## Verification

Files (all plain source, imports from the repository, no handwritten axioms or `sorry`):

- `GateArithmetic.lean`: modulo-four arithmetic.
- `GatewayRefinement.lean`: first exact two-family refinement.
- `GateArithmeticEight.lean`: modulo-eight arithmetic.
- `GatewayRefinementEight.lean`: strengthened iff, importing the preexisting source proof.
- `SectionRightOne.lean`: unique right-one source, no later returns, low `m=0` exclusion.

The manual-only [workflow](../../.github/workflows/agent20-c-halting-gates.yml) compiles original, unchanged CLine/section/bounce/Agent38/Agent15 modules against these files with Lean **4.36.0-rc2**. Independently completed full source CI:

- [41475241185](https://github.com/FlareZ123/bb6/actions/runs/41475241185): modulo-four gateway theorem **SUCCESS**.
- [41475855972](https://github.com/FlareZ123/bb6/actions/runs/41475855972): strengthened modulo-eight gateway theorem **SUCCESS**.
- [41476624774](https://github.com/FlareZ123/bb6/actions/runs/41476624774): right-one source and exact low m=0 exclusion **SUCCESS**.

Proof output reports only standard axioms (propext, Quot.sound, and possibly Classical.choice from imported source proof chains). The local preliminary tests of dependent scripts used temporary declarations as interfaces; the cited CI runs compile *unmodified actual proofs*, which are authoritative.

## Limitations and open work

These arguments reuse prior source-connected all-time reachability invariants and prove new global arithmetic corollaries; they do **not** resolve any of the remaining infinite `m`, `(j,m)` families. They do not establish a fresh bound on the universal Busy Beaver function or classify Machine C. The inverse normalizer from Agent 15 and current mod4/mod8 forbidden-sector principles were experimentally tested against low m<300 and high j,m<16. They certify the classes above, and no further whole-class exclusions have yet followed using only these particular invariant predicates. Any stronger result should use new global blank-orbit structure or deeper reverse dynamics rather than merely more finite congruence screens.

As a next step, investigate a forward-closed structural invariant of the genuine section orbit that excludes every remaining halting Diophantine input, or construct an actual blank-reachable halting witness.
