# Agent 5: section collapse for a BB(6) holdout

Status: intermediate reduction, not a machine decision.

Target: `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`.

Google DeepMind's Cryptids module for this machine proves that its Turing-machine behavior is equivalent to the accelerated state map copied in `Section.lean`. Agent 8 separately proved strict growth of `a+b+c` for this same map.

## Exact collapse

The published drain rule decreases `b` by two and adds three to `c`. The Lean file proves

`
(a,2q,c)   ->* (a,0,c+3q)
(a,2q+1,c) ->* (a,1,c+3q).
`

After restricting `b` to its parity bit `p`, one decrement of positive `a` followed by a complete drain gives

`
F(p,d) = (d mod 2, 3*floor(d/2) + 2 + 4p).
`

The four cases are proved universally in `Section.lean`. At `a=0`, parity zero is the halting case, while parity one resets to `(2d+9,0,0)`.

Therefore a global cycle starts from `(A,0,0)`, iterates `F` exactly `A` times, and either halts when the resulting parity bit is zero or resets with `A'=2d+9` when it is one.

With the one-variable encoding `x=2d+p`, the map is

`
x=4q   -> 6q+4
x=4q+1 -> 6q+12
x=4q+2 -> 6q+5
x=4q+3 -> 6q+13.
`

This turns the three-counter problem into a fixed parity transducer sampled at recursively generated iteration counts.

## Finite blank-orbit evidence

Starting from the certified reset `A_0=3`:

`
F^3(0,0)  = (1,8),       A_1=25
F^25(0,0) = (1,113544),  A_2=227097.
`

The third cycle also survives: `F^227097(0,0)` has parity bit one. Its second coordinate has 39,991 decimal digits and 132,846 bits. The next reset also has 39,991 digits.

This is finite evidence only. A general implication from arbitrary surviving iteration counts to their induced reset counts is false on small counterexamples, so a proof must exploit the special recursively sampled sequence.

## Verification and next target

`Section.lean` compiled under Lean 4.36.0-rc2 with no `sorryAx`. The connection from the copied acceleration to the original Turing machine is supplied by the upstream Cryptids proof.

The remaining target is to prove that for the recursive sequence

`
A_0=3,
(p_n,d_n)=F^(A_n)(0,0),
A_(n+1)=2d_n+9,
`

every `p_n` equals one. That would prove this holdout nonhalting when combined with the upstream certified acceleration.
