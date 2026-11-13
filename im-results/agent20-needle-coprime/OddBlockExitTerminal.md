# Odd-block exit followed by one terminal-feeder transition

**Status:** A new source-linked exact identity has been added in
[NeedleOddBlockExit.lean](NeedleOddBlockExit.lean). Its targeted pinned-upstream
CI is being added. This is an intermediate result, not a nonhalting proof.

## Statement

Let (t>0), (m>0), and (m) be odd. The original-source odd-block theorem
gives the exact run
[
  2^t m-1 \longrightarrow^{\,t} 5^t m-1,
]
and the exit counter (5^t m-1) is even. Suppose one further high-level
transition from this exit reaches a terminal tower:
[
  \operatorname{highLevelNext}(5^t m-1)=\operatorname{haltTower}(k).
]
The complete source classification of successful high-level transitions
then gives a feeder decomposition
[
  5^t m-1=\operatorname{oddTower}(q,v),\qquad
  5^t m+1=2^v(2q+3).
]

Combining this exact exit equation with the original-source terminal-feeder
identity gives
[
\boxed{
  2^{k+v+2}+5\cdot2^v
  =
  5^t m(2^{v+1}+3)+2^v(2v+4)+3.
}
]
In particular,
[
  2^{k+v+2}+5\cdot2^v
  \equiv 2^v(2v+4)+3 \pmod{5^t}.
]

The Lean theorem odd_block_exit_terminal_identity proves the exact equality
and includes the actual runHigh block witness and even-exit fact. Its
corollary odd_block_exit_terminal_nonzero_mod_five proves
[
  5\nmid \bigl(2^v(2v+4)+3\bigr).
]
This follows because the left side of the boxed identity is congruent to
(2^{k+v+2}), a unit modulo five.

## Explicit valuation classes excluded

The residue
[
  F(v)=2^v(2v+4)+3 \pmod 5
]
depends only on (v\bmod20): the exponential factor has period four modulo
five, while the linear factor has period five. Direct evaluation over one
period gives
[
  F(v)\equiv0\pmod5
  \quad\Longleftrightarrow\quad
  v\bmod20\in\{1,2,4,15\}.
]
Therefore a terminal feeder that is the exit of a positive odd block must
satisfy
[
  \boxed{v\bmod20\notin\{1,2,4,15\}.}
]
This is a history-sensitive exclusion: it applies when the immediate
predecessor state of the terminal transition was itself reached as the exit
of a nonempty odd block. It is not a universal exclusion of these valuation
classes for arbitrary terminal feeders.

## Connection to the cancellation family

For the cancellation feeder family already studied in this dossier, the
shifted feeder counter has the form
[
  b_r=2^{v_r}P_r(A_r),\qquad P_r(A_r)\equiv0\pmod5.
]
Thus (b_r\equiv0\pmod5). By contrast, every positive odd-block exit has
shifted counter (5^t m+1\equiv1\pmod5). Hence no cancellation feeder can
be reached immediately after a positive odd block. Any genuine root path
into such a feeder must have at least one even-to-even transition in its
final suffix.

This is a useful branch reduction for the unresolved cancellation feeders:
it directs root-sensitive work toward the all-even suffix rather than
rechecking odd-block exits. It does **not** show that the all-even suffix is
impossible, nor that any synthetic feeder or parent is blank-root reachable.

## Scope and next mathematical step

The theorem handles an arbitrary positive odd-block length followed by
exactly one further transition to a terminal. It does not yet compose through
two or more intervening even transitions. The decisive open problem is to
control that all-even suffix for the remaining terminal-feeder families, or
to build a source-certified finite-state/p-adic inverse invariant that
handles arbitrary suffix length.

This result belongs in im-results/: it is a source-linked necessary
condition, but it does not decide the unbounded terminal existential and
does not establish a BB(6) upper bound.
