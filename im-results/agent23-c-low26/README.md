# Machine C: a five-link inverse obstruction and a stronger exact blank-halting sieve

**Agent 23, 6 November 2026.** These are unconditional theorems about the original six-state Machine C's blank-entry section map. They do **not** decide whether Machine C halts, determine BB(6), or supply a BB(6) upper bound. This directory belongs in `im-results/`, pending wider mathematical synthesis and external prior-art assessment.

## Main result: two oblique forbidden families

Let `CReach x y` mean reachability of the genuine original-section state `(x,y)` at any number of section steps, starting from the authenticated blank-entry `(5,1)`. The original map is `BB6.Agent46.secNext` from `FastSectionDef.lean`.

[`C26Oblique.lean`](C26Oblique.lean) proves the following all-time source theorem for any natural counters `x,y` with `y≥34`:

```text
if (y%32=26 and (4*x+y)%256=30)
or (y%32=18 and (4*x+y)%256=222),
then ¬ CReach x y.
```

The two sets are oblique infinite congruence cylinders. Neither requires a bound on the first counter or on elapsed machine time.

The core proof uses integers `q,z≥0` satisfying `x+2*z=16*q+7`, `z≥4`, and either `(z%4,q%4)=(3,0)` or `(2,3)`. It forces five consecutive original-source inverse transitions:

```text
(x,              8z+2)
   <- (x+8z,          4z)           E
   <- (x+12z-2,       2z-1)         E
   <- (8q+6z,         4q+4z-2)      O
   <- (12q+10z-4,     2q+2z-2)      E
   <- (14q+12z-8,     q+z-2)        E
```

Here **E** is Agent24's exact original-source `six_even_right_blank_reach_iff`; **O** is Agent3's exact `oddodd_lowval_blank_reach_iff`. All their guard conditions are discharged for the two infinite parameter sectors, without a simulator shortcut. The last state has odd right counter at least five and sum `15q+13z-10 ≡ 1 (mod 4)`. The original blank-orbit image invariant `BB6.Agent3.blank_section_odd_image` allows only sums 0 or 3 modulo 4 at such a post-initial state; the true initial state is also excluded. Thus every such putative blank-root ancestor is impossible.

The rectangular theorem [`blank_no_rectangle`](C26Rectangle.lean),

```text
∀u v≥0, 1≤v → ¬ CReach (64*u+1) (256*v+26),
```

is an independently Lean-checked subfamily of the first oblique congruence, with its explicit affine reverse chain in `C26Rectangle.lean`. `LowC26.lean` additionally retains a standalone five-link proof for the one-dimensional root `(1,256v+26)`.

## Original stopping-source consequences

The complete original-source low stopping equation is

```text
k + 3*m + 4 = 2^(2*m+3),  first counter = 1.
```

[`LowC26.lean`](LowC26.lean) proves that **every** candidate with `m%256=246` is unreachable from the blank source. Such candidates necessarily satisfy `k%256=26` and `k≥282`, so they lie in the first oblique region at first counter 1.

The high stopping equation is

```text
k + j + 3*m + 5 = 2^(2*m+2)*(j+3),  first counter = 2*j+3.
```

[`C26ObliqueHigh.lean`](C26ObliqueHigh.lean) proves that, for every `m≥3`, the stopping candidate is unreachable whenever either of the following coupled modular conditions holds:

```text
A: (j+3*m+5)%32=6  and (7*j+233)%256=(3*m)%256
B: (j+3*m+5)%32=14 and (7*j+41)%256=(3*m)%256.
```

These are exactly **128 ordered residue pairs** of `(j mod256,m mod256)` in total: 64 in A and 64 in B. Equivalently, A requires `j%4=3` and its displayed mod256 equality, while B requires `j%4=0` and its displayed mod256 equality. The two families are disjoint. The original-source proof derives the actual stopping right counter's appropriate oblique modular condition using divisibility of `2^(2*m+2)` by 256, and proves `k≥34` uniformly. [`C26High.lean`](C26High.lean) retains the earlier eight-pair subcase `j%32=31 ∧ (j+3*m+5)%256=230`, now formally shown to be contained in A by [`old_high_sieve_in_new`](JointC26.lean).

## Updated exact time-free Machine C stopping criterion

[`JointC26.lean`](JointC26.lean) composes the new proofs with Agent19's source-verified `JointFiveSieve.blank_halts_iff_five_root` (including Agent3, Agent11, Agent19 and Agent24's earlier restrictions). It establishes `blank_halts_iff_c26_five_root`, an exact **if and only if** for genuine blank halting in terms of the existing `mixedFiveFastRootDecision` on only:

- low parameters admitted by `BB6.Agent11Joint.lowAllowed m` **and** `m%256≠246`;
- high parameters admitted by `BB6.Agent19Five.highAllowed j m` **and** outside the A/B obstruction for `m≥3`.

Both permitted domains are still infinite. The Boolean root predicate is source-equivalent to fixed-target reachability, and the equivalence has no existential runtime variable. The remaining parameter existence problem is **undecided**.

## Verification, scope, and reproduction

The original CLine, Machine C transition definition, section construction, exact inverse identities, and true blank-root invariant are compiled unchanged with **Lean 4.36.0-rc2**. All proofs print only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`:

- [CI run 42212769191](https://github.com/FlareZ123/bb6/actions/runs/42212769191) successfully recompiles the original sources and proves `blank_no_oblique_mod256` and `blank_no_high_oblique`, together with the narrower prior certificates. Workflow: [`agent23-c-low26.yml`](../../.github/workflows/agent23-c-low26.yml).
- [CI run 42212940315](https://github.com/FlareZ123/bb6/actions/runs/42212940315) successfully rebuilds the entire existing Machine C five-sector joint source sieve, then proves `blank_halts_iff_c26_five_root` and `old_high_sieve_in_new`. Workflow: [`agent23-c26-joint.yml`](../../.github/workflows/agent23-c26-joint.yml).

These are full general theorems, as distinct from bounded numerical search. Newness is assessed relative to the repository's source files inspected in this invocation; independent literature and other unexamined paths might contain overlapping results. The unresolved mathematical bottleneck remains the **infinite root-existence problem** in the combined criterion, alongside the other Busy Beaver six-state candidates.
