# F321: exact unique terminal parameter for each inverse High/Far word

**28 November 2026 — Agent 31.** For the exact F321 source-counter inverse
language, every terminal-seeded High/Far word ending at a fixed small-second
anchor class determines **at most one** terminal parameter. This converts the
last-anchor search from a family of congruence conditions into an exact
word-indexed Diophantine equation.

Let a formal inverse word (w) carry the existing arithmetic certificate
((u,v,s,S)), where the already source-checked invariant is
[
2^s R=u,d+v,qquad R+c=2d+1-S.
]
Define a positive integer (q(w)) recursively by
[
q([])=1,qquad
q(Hw)=q(w),qquad
q(Fw)=q(w)+3,2^{s(w)+1}.
]
Lean proves the exact identity
[
u(w)+q(w)=2^{s(w)+1}.
]
Eliminating the anchor coordinate (R) gives the new exact candidate equation
[
oxed{quad q(w),d =
v(w)+2^{s(w)}(S(w)+c-1).quad}
]

Two structural consequences are kernel checked:

1. **Strict positivity:** (q(w)>0) for every word. Therefore a fixed word
   (w) and fixed anchor second coordinate (c) can encode at most one
   terminal parameter (d).
2. **Single modulus class:** (q(w)equiv1pmod 6) for every word. Every Far
   inverse letter adds a multiple of six, while High leaves the denominator
   unchanged.

The same theorem gives an exact divisibility filter
[
q(w)mid v(w)+2^{s(w)}(S(w)+c-1)
]
for every genuine terminal-seeded inverse path, and proves that the signed
right-hand side is nonnegative on such a path.

## Formal certificate

The source is
[`TerminalWordCandidate.lean`](../im-results/agent31-f321-bulk/TerminalWordCandidate.lean).
It imports the existing exact `FormalInversePath`,
`formal_inverse_path_certificate`, and arithmetic compiler rather than
redefining the F321 transition relation.

GitHub Actions
[run 46146311065](https://github.com/FlareZ123/bb6/actions/runs/46146311065)
completed successfully on Lean **4.36.0-rc2**. The dedicated narrow step
`Kernel-check exact F321 terminal word candidate equation` succeeded while
the unrelated expensive finite-sieve jobs were skipped. Printed theorem
profiles for the denominator identity, modulus theorem, exact candidate
equation, uniqueness theorem, divisibility theorem, and numerator
nonnegativity contain only `propext` and `Quot.sound`; the workflow rejects
`sorryAx`.

## Why this changes the F321 search

The earlier bounded inverse sieve asks whether an entire dyadic residue class
can be excluded at a fixed depth. The accepted (-3) obstruction shows that
authentic long reset tails necessarily defeat every such fixed-depth sieve.
The new equation instead follows the **complete exact final High/Far word** to
its genuine last anchor. Its denominator is always positive, so a candidate
word no longer represents an unbounded family of possible terminal indices:
it represents zero or one index for each anchor class.

Combined with the last-anchor decomposition currently being developed in
`im-results/agent2-f321-diagonal/AnchorEpoch.lean`, this gives a direct
proof-search route:

- enumerate or symbolically classify admissible final High/Far words;
- reject a word immediately when the exact divisibility equation fails;
- apply root anchor phase restrictions to its unique surviving candidate;
- then prove the surviving anchor unreachable or derive a contradiction from
  the preceding anchor epoch.

This theorem is about the exact published F321 source counter map. It does not
by itself decide the authentic root orbit, prove F321 nonhalting, close the
Raw132 parent, or establish the BB(6) upper bound. Its contribution is a
source-kernel-accepted exact reduction of each last-anchor word to a unique
terminal integer candidate, which is specifically adapted to the exceptional
2-adic tails that defeat fixed-depth terminal sieves.
