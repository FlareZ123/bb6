# D100 F1-hole countdown/doubling nonhalting certificate

**Status:** universal macro recurrence, exact blank entry and positive-cost induction all compiled in local Lean 4.36.0-rc2 against a verbatim reconstructed SweepPumping zipper core. The source bridge `never_of_growth` and original-repository import closure require source acceptance. Do not count this as an accepted leaf until that gate succeeds.

Literal `1RB0LE_1RC1LD_0RD0RB_0LD0LA_1LA0RF_1RE---`, formerly persistent after 300 million primitive steps. This is not a finite search result: the recurrence proves a total positive-time successor for every member of the invariant family.

Write V=10, W=01, U(n)=1^n. Use the original zipper convention, head in the left list or zero if empty. Let
- D(m,q) = (A, [], V^(m+1) 1 V^q 1), m,q natural.
- P(n) = (A, [], V^n 1).

Blank tape reaches D(0,5) after 153 steps. Exact transition laws:
1. D(m+1,q) -> D(m,2q+3) in 8(m+2)+4q²+22q+36 steps.
2. D(0,q) -> P(4+2q) in 4q²+22q+43 steps.
3. P(n+2) -> D(n,5) in 16(n+2)+88 steps, for every n.

Consequently the D family has a total positive-cost successor (m,q)->(m-1,2q+3) for m>0 and (0,q)->(2+2q,5) otherwise. Iterating gives arbitrarily long defined prefixes of the partial machine. Hence **every completion of F1 is nonhalting**, pending source bridge acceptance. No assumption about divergence of arithmetic parameters is needed.

## Proof mechanism

First sweep C across alternating pairs, then a four-move turn and an A/B/C/D sweep gather the right alternating word into a left unary block of length 2q+4. A fixed 20-step segment removes four ones and initializes the right word V^3 1. For any left tail L, a 4b+10-step EF/A sweep takes A with left 11L and right V^b 1 to A with left L and right V^(b+2) 1. Repeat q times at exact total cost 4*3*q+4q²+6q. The remaining left alternating word W^m1 is removed by finite boundary turns and two pair sweeps, giving the countdown or pure phase. The pure phase scans alternating pairs and turns at the implicit blank, initializes a finite right word V²0, and uses the corresponding terminal-zero gathering variant followed by one pump. This restarts at D(n,5).

Every primitive boundary identity is an `rfl` proof with arbitrary untouched tails. General sweeps and iteration use inductive theorems, not extrapolation from long finite traces. The exact source module [D100Countdown.lean](D100Countdown.lean) compiled locally; its blob is d8e489893d28ffdff00a2971e95b116f08ab9662. Local axiom profiles: entry [propext]; count, finish, restart, growth and positive [propext, Quot.sound]. [D100CountdownNever.lean](D100CountdownNever.lean) is the source wrapper to be compiled with the existing repository semantics. It uses the same standard bridge as the previously source-accepted long-epoch B1 pump.

Together with the unary-doubling E0 argument and the 53-quadrillion-step delayed E0 exposure, this mathematically resolves all three previously persistent D100 hard literals at the reconstructed-model level. Parent assembly and other source acceptance obligations remain.
