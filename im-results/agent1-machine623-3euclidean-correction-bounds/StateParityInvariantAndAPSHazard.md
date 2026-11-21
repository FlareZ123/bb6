# Certified-state parity shield and the remaining A_pos 3-adic hazard for #623

**Status:** a paper-level inductive invariant derived by case analysis from the exact State.next transition table in the independent Cryptids formalization. The source machine's acceleration is Lean-certified there; this parity invariant and the A_pos hazard reduction have not yet been added as Lean theorems. The invariant is an all-reachable-states statement if the displayed case proof is formalized as written. It does **not** prove nonhalting: one A_pos halting family remains.

## External exact acceleration

The target is the same six-state machine used by this dossier:

1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA

Google DeepMind's public formalization is:

- [Machine-specific Lean file](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean)
- [Cryptids BB(6) hardness dossier](https://google-deepmind.github.io/cryptids/BusyBeaver/BB6/Hardness/)

The Lean file defines a second exact accelerated state system with constructors D0, D1, H, B, A_pos, and A_zero; its next transition is covered by is_valid_acceleration. The start is D0 0 0 4, and the file proves the required connection to its high-level D(0,7) section. The hardness page classifies #623 as a 4-counter base-3 cascade and reports the empirical observation that all 756 measured entries into H_mid had odd a_H. The invariant below explains that parity observation structurally, subject to formalizing the short induction.

## Inductive parity invariant

For a state of the exact State.next system, define P by the following constructor-specific clauses:

| Constructor | Required invariant |
|---|---|
| D0 a b d | a and b are even, and d>0 |
| D1 a b d | a+b is odd |
| H a b m | a and b are odd |
| B a k b d | a+k+b is even |
| A_pos a k q m | a+k+q is odd |
| A_zero a q m | a+q is odd |

The accelerated start D0 0 0 4 satisfies P.

### Preservation proof by constructor

The following checks cover every branch of next.

**D0.** The invariant gives even a,b and positive d, so only d=1, d=2, and d>=3 occur.

- If d=1,b=0,a=0, the successor is D0 0 0 4.
- If d=1,b=0,a>0, the successor is B a 0 0 0; its B-parity sum is the even number a.
- If d=1,b>0, then even b>0, and the successor D1 (a+2) (b-1) 3 has odd first-plus-second sum.
- If d=2,a=0, D1 1 b 2 has odd sum because b is even.
- If d=2,a>0, B (a-1) 0 (b+1) 0 has B-parity sum a+b, which is even.
- If d>=3, D0 (a+2) b (d-2) preserves both even coordinates and has d-2>0.

**D1.** Since a+b is odd, the branch a=b=0 is impossible. If a=0, then b is odd and positive, and D1 1 (b-1) (d+2) has odd coordinate sum. If a>0, B (a-1) 0 b d has B-parity sum a+b-1, which is even.

**H.** Both a,b are odd, so in particular a is nonzero.

- For m=0, D1 a (b+1) 5 has odd coordinate sum.
- For m=1, D1 (a+2) (b+1) 2 has odd coordinate sum.
- For m>=2,a>=2, oddness gives a>=3, and H (a-2) (b+2) (m-2) again has both first coordinates odd.
- For a=1,m=2, the successor D1 2 (b+2) 3 has odd coordinate sum.
- For a=1,m=3, D1 1 (b+3) 2 has odd coordinate sum.
- For a=1,m>=4, D0 2 (b+3) (m-3) has even first coordinates and positive final coordinate.

Thus every reachable H state has odd a; neither halting H branch with a=0 is reachable.

**B.** If b>0, the successor B a (k+1) (b-1) (d+2) preserves a+k+b. If b=0,k>0, the successor A_pos a (k-1) 0 (d+3) has A_pos parity sum a+k-1, which is odd. If b=k=0, B parity forces a even:
- a=0 gives D0 0 0 (d+4);
- a=1, the only B halting case, is impossible;
- a=2,d=0 gives D1 1 2 2, and a=2,d>0 gives D0 2 2 d;
- a>=4 gives H (a-3) 1 (d+1), whose first two coordinates are odd.

Thus the B halting branch B 1 0 0 d is excluded.

**A_pos.** Split on k:
- k=0,a>0 gives D1 a q (m+2), whose D1 sum is odd by the A_pos invariant.
- k=1,a=0 gives D1 1 q m; the A_pos invariant forces q even, so the D1 sum is odd.
- k=1,a>0 gives A_pos (a-1) q 0 (m+2q+3); its new parity sum is a+q-1, odd by the old invariant.
- k=2 gives A_zero a q m; its A_zero parity sum is odd.
- k>=3 gives A_pos a (k-3) (q+1) m; the parity sum changes by -2.

The remaining case k=0,a=0 is a halting branch and is **not** excluded by this parity invariant.

**A_zero.** Its successor D1 (a+2) q m has odd coordinate sum by the A_zero invariant.

This proves preservation of P by exhaustive case analysis. It also proves the full H odd-a shield and excludes the B halting branch for every state reachable from D0 0 0 4.

## Exact reduction of the remaining A_pos halting condition

For A_pos a k q m, set

\[
N=k+3q,\qquad \tau_a=1+3+\cdots+3^{a-1}=\frac{3^a-1}{2}
\]

with tau_0=0.

The A_pos transitions have a simple interpretation:

- If k>=3, A_pos a k q m goes to A_pos a (k-3) (q+1) m; N is unchanged.
- If k=2, the transition goes to A_zero, which is safe.
- If k=1,a=0, the transition goes to D1, which is safe.
- If k=1,a>0, the transition goes to A_pos (a-1) q 0 (m+2q+3); the new N is q=(N-1)/3. This consumes one low-order ternary digit equal to 1 and decrements the budget a.
- If k=0,a>0, the transition goes to D1, which is safe.
- If k=0,a=0, the machine halts.

Consequently, an A_pos a k q m state halts under repeated A_pos transitions if and only if

\[
N\equiv\tau_a\pmod{3^{a+1}}.
\]

Equivalently, the low-to-high ternary digits of N=k+3q begin with exactly a copies of 1 followed by a 0. Any earlier 0 or 2 exits safely; after a ones, a 1 or 2 also exits safely. Only the prefix 1^a0 halts.

The global parity invariant supplies one further necessary condition. Since a+k+q is odd and N=k+3q, N is congruent to 1-a modulo 2. Also tau_a is congruent to a modulo 2. Therefore, if the halting congruence holds, then

\[
\frac{N-\tau_a}{3^{a+1}}
\]

must be odd. This is a necessary condition, not an exclusion.

## What is now proved and what remains

**Established by the case argument:** every reachable H state has odd a; no reachable H halting branch exists; no reachable B halting branch exists; the remaining halting question is exactly the A_pos congruence k+3q congruent to tau_a modulo 3^(a+1).

**Still open:** prove that no A_pos state reachable from the certified start satisfies this congruence. This is the genuine 4-counter 3^n-cascade problem. The reported 756/756 odd-a_H observations are finite evidence; the parity invariant upgrades that particular shield, but it does not resolve the A_pos hazard or prove BB(6).

## Formalization target

Add a theorem over the external State and next definitions:

\[
P(s)\Longrightarrow P(\operatorname{next}(s))
\]

for every non-halting successor, followed by induction from D0 0 0 4. The proof should use omega for parity arithmetic and explicit constructor/counter case splits. Separately prove the A_pos halting-congruence equivalence by induction on the A_pos transition sequence. Do not label the machine nonhalting until the reachable A_pos congruence is excluded.
