# S4 terminal quotient: the mod-31 / length-5 abstraction is insufficient

**Status (16 November 2026):** exact-integer counterexamples within the conditional R-section model. This rejects one proposed quotient abstraction; it is **not** an authentic S4 halt, a nonhalting proof, or a BB(6) result.

## Exact source terminal condition

For the original S4 source gate,
`G c S = none` iff `Pow2(W(S)+c)`, where
`W([])=0` and `W(b::S)=b+1+2W(S)`. This is the source theorem
`S4Octet.G_none_iff_power` in
[the S4 octet formalization](../agent5-s4-octet/S4Octet.lean), checked in the
original-source mass-gate run [42543510207](https://github.com/FlareZ123/bb6/actions/runs/42543510207).

If the odd carry consumes all but the final head of an (n)-digit suffix,
the source potential halves at each of the (n-1) odd recursive branches.
The empty-tail terminal quotient is therefore
[
q=\frac{W(S)+c}{2^{n-1}}.
]
At such a full-suffix event, the gate halts exactly when (q) is a power of
two. Modulo 31, powers of two occupy only
`{1,2,4,8,16}`.

This makes modulus 31 a valid *necessary-condition test at a known full-suffix
event*. It does not make `W(S) mod 31` and length modulo five a closed state
for the evolving suffix: division by (2^{n-1}), carry propagation, and the
partial return map retain more information.

## Exact counterexample at the modeled R-section

The reproducible [six-level script](s4_nested_depth6.mjs) extracts the
4,603-gate R word from the 18-digit Q section and its 12,800-block ten-digit
projection. The exact offset sum is
`274877906934794`, and the first offset is
`c_0=305419363311`. The modeled residual tail after the 107-Q-block
transient is

```text
A = [56255833147, 351785746871, 192090536220, 315284183616,
     669000984669, 334500492334, 167250246169, 167250246166].
```

Its exact weighted mass is `W(A)=57570541714408`; hence
`W(A) mod 31 = 27`, and its length is 8 (so length mod 5 is 3).

Now take the synthetic suffix

```text
B = [1267650600228229401191283841810, 0, 0, 0, 0, 0, 0, 0].
```

It has the **same length and the same weighted-mass residue**:
`length(B)=8` and `W(B) mod 31=27`. But
`W(B)+c_0=2^100` exactly. Thus
`G(c_0,B)=none` by the original-source terminal theorem. The terminal
quotient after the seven odd carries is `2^93`.

Therefore the quotient class `(W mod 31, length mod 5)=(27,3)` containing
the modeled R-section tail also contains a suffix that halts at the very
first R gate. A proof using only that quotient cannot certify nonhalting for
the modeled tail. This is a **synthetic counterexample**, not evidence that
the genuine root reaches B or halts.

## The quotient is not closed under the complete R word

A second exact test shows failure of deterministic quotient dynamics. The
two inputs

```text
A0 = [0, 16]     W(A0)=35
B0 = [1, 0]      W(B0)=4
```

both have `(W mod 31, length mod 5)=(4,2)`. Applying the complete 4,603-gate
R word to each succeeds, but the output lengths are respectively 12 and 13.
Both output weighted masses are 5 modulo 31. Thus the same input quotient
state has two different output length residues (2 and 3), so R does not
induce a deterministic transition on this quotient.

These are arbitrary finite suffixes used to test closure of the all-suffix
R operator; they are not asserted to be root-reachable.

## Evidence boundary and next step

- The terminal iff is a source-connected Lean theorem.
- The 4,603 offsets and the counterexamples are exact BigInt computations
  in the reproduction script.
- The long prefix periods, the modeled section after the 5,457-return
  certificate, and the bridge to that section are **not** Lean-kernel
  certified. The R-section is conditional on those numeric premises.
- No conclusion about actual S4 halting/nonhalting or BB(6) follows.

The next useful target is a root-reachable, history-sensitive invariant that
retains enough carry information under R/Y, or a source-certified failing
gate. Refining `W mod 31` with length modulo five alone is not a viable
closed-state approach; another finite prefix cycle alone does not repair it.
