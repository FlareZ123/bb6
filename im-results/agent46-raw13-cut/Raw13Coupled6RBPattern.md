# Raw13 E1=0RB: exact two-pass periodic return

**Mathematical claim (arbitrary-tail derivation; source check not yet accepted).** For the literal residual
`1RB1LD1RC1RB1LA1RE1LF0LA0RC0RB---1LA`, every completion is nonhalting. The sole unassigned transition is F0. At the authentic blank-start time 223, the source zipper (current bit first on the left, both words nearest-first) has state A and words

```
L = 011110111
R = 01010 (11110)^2 101011
```

For every n≥0, put A_n = A(0 1^(3n+4) 0 111, 01010 (11110)^(n+2) 101011). The exact return A_n → A_(n+1) has cost 20n+111 primitive assigned transitions. This produces unbounded prefixes independently of the completion of F0. It is a single literal leaf, not closure of the 0RB sibling or Raw13 parent. No global roster change is claimed.

## Proof with an arbitrary untouched left suffix

Write X=10, Y=01, U=11, P=11110, Q=01111, Z=11111110, S=01010, T=0101011, V=111, H0=010111, H1=1010111, H2=11111110111, J=1110, G=0111, and T0=101011. Concatenation is implicit. Each identity below is a finite computation of the literal partial table; L,R are arbitrary untouched words. The empty right end means actual blank padding.

| Input | Cost | Output |
| --- | ---: | --- |
| A(0L, S P R) | 8 | B(10 H1 L, X R) |
| A(H0 L, J P R) | 7 | B(10 H2 L, X R) |
| B(1L, X P R) | 5 | B(1 Q L, X R) |
| B(1L, X T0) | 21 | A(Z 1111 L, 1) |
| A(U L,R) | 2 | A(L,Y R) |
| A(X P L,R) | 5 | A(X L,Q R) |
| A(101 L,R) | 3 | A(L,V R) |

The B pump can be iterated k times with the same X lookahead and arbitrary tails. Using the word identity 1111 Q^k 0=P^(k+1), the first four local rules give the two right sweeps:
- A(0L,S P^(k+1) T0) → A(Z P^(k+1) H1 L,1), cost 5k+29.
- A(H0 L,J P^(k+1) T0) → A(Z P^(k+1) H2 L,1), cost 5k+28.

As Z=U^3 X, three U-pairs followed by j X-framed P pumps give A(Z P^j L,1) → A(X L,Q^j T), cost 5j+6. Apply the 3-step turn and the identity V Q^j T = J P^j T0. Since H1=1H0, this gives A(Z P^j H1 L,1) → A(H0 L,J P^j T0), cost 5j+9. Since H2=1 U^3 G, the same turn plus three additional U-pairs gives A(Z P^j H2 L,1) → A(G L,S P^(j+1) T0), cost 5j+15 (use Y^3 J = S P).

With j=k+1, composition gives the general return
```
A(0L,S P^(k+1) T0) -> A(0111L,S P^(k+2) T0)
```
in exactly 20k+91 steps for every k≥0 and every L. Take k=n+1, L=1^(3n+4)0111 to obtain the stated root return. The positive cost yields nonhalting from the authentic seed, not just growth for prepared tapes.

## Evidence and integration

[Raw13Coupled6RBPattern.lean](Raw13Coupled6RBPattern.lean) expresses all seven finite identities as reductions of the actual `run0` and uses the existing generic source sweep and `never_of_growth` lemmas. The literal 223-step seed and the fixed local identities were replayed using exact source-style zipper semantics in the tool runtime. Shell and Python tool calls returned ClientError before execution, so local Lean could not run; the existing manual source workflow target `coupled6RBPattern` is the focused acceptance route. Until that succeeds, this is a written mathematical derivation with uncompiled Lean source, not a source-accepted leaf. The generator has a literal-table entry for the proof but deliberately rejects a sibling with any missing leaves. The 0RB bank still has other unresolved tables; do not repeat this proof discovery or count the sibling as closed.
