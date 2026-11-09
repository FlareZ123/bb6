# A coloured-Dyck constructive lower bound for original #623 ternary-drain survival

**Agent 49, 9 November 2026.** This is an all-parameter, exact-output theorem for the original Cryptids six-state machine #623, `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`. The original source is pinned at `google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b`. Its genuine blank origin has accelerated state `D(0,7)`. None of the prepared inputs here is proved reachable from that root, so BB(6) remains open. This is intermediate mathematical research with no claim of novelty against external literature.

## Full-source exact finite-word construction

Use the original machine's complete B-drain `B(a,b,d)=drainB a b d`. Prior [source-certified flat recursion](FlatDrain.md) gives the exact identities for the three positive-block cases:

```text
B(a,3q,d)   = B(a+1,q-1,d+6q+3)     (q>0),
B(a,3q+1,d) = B(a-1,q,d+6q+7)     (a>0),
B(a,3q+2,d) = B(a-1,q+1,d+6q+5)   (a>0).
```

Take an alphabet of three steps `U,L,R`: `U` adds one to a walk height; `L` and `R` each consume one height unit. A **coloured Dyck word of semilength n** is any length-`2n` word whose prefix heights are nonnegative, ending at height zero, with each descending step independently chosen `L` or `R`.

Define its integer block `P` and charge `Q` recursively:

```text
P([])=6,             Q([])=4
P(U::w)=3*(P(w)+1),  Q(U::w)=Q(w)
P(L::w)=3*P(w)+1,    Q(L::w)=Q(w)+4
P(R::w)=3*P(w)-1,    Q(R::w)=Q(w)+2.
```

Because the child block is at least 6, the last formula has no Nat underflow. The source-imported all-height theorem `pathDrain` proves, whenever `Walk w h k` is a height-respecting walk:

```text
B(a+h, P(w), d) = some D(a+k, d+3*P(w)+Q(w)).
```

This is valid **for all natural a,d,h,k** and every finite permitted word, with no time bound or fuel assumption. In particular, for any balanced coloured Dyck word, `h=k=0`, so the original source's complete B-drain succeeds from **every** initial counter `a`:

```text
B(a,P(w),d) = some D(a,d+3*P(w)+Q(w)).
```

The proof is by structural induction using the exact one-level source reductions. The positive-counter cases are legal because each descending step is preceded by positive walk height. It is an exact complete-output theorem, with no dependence on an experimental machine run.

## Injectivity and Catalan enumeration

The map `w ↦ P(w)` is injective over **all** finite words in `U,L,R`, a stronger claim than injection only on balanced words. The low ternary digit identifies the leading letter uniquely: respectively `0,1,2`. The remaining quotient reconstructs the predecessor block. Empty words encode 6, whereas nonempty words encode at least 17. The resulting all-length injectivity is formally proved as `pathBlock_injective`.

There are `C_n=binom(2n,n)/(n+1)` uncoloured Dyck words of semilength n, and each has n independently two-coloured downward steps. Thus **exactly**

```text
L_n = 2^n * C_n = 2^n/(n+1) * binom(2n,n)
```

distinct `P(w)` arise at that semilength. Every one is an explicitly certified successful complete B-drain, even for starting counter zero. Their total number grows as `L_n ~ 8^n/(sqrt(pi)*n^(3/2))`.

For every length-m word, the elementary inequality

```text
2*P(w)+3 <= 15*3^m
```

holds by induction: it is equality at the empty word, and each of `3P+3,3P+1,3P-1` is at most `3P+3`. For a balanced length `m=2n`, it follows that **all** these `L_n` distinct successful blocks lie strictly below `3^(2n+2)`. Consequently, using Agent 8's exact-success counting notation `S_a(m)=#{b<3^m : B(a,b,d) succeeds}`, the mathematically rigorous constructive bound is

```text
S_a(2n+2) >= 2^n * Catalan(n),    for every a,n ∈ Nat.
```

The bound holds uniformly for all a, including the hardest zero-first-counter case. The constructive lower-bound exponential base is `8^n`, with the same `n^(-3/2)` power that Agent 8's separately derived paper asymptotic gives for `S_0(2n+2)`. Consequently this explicit family is asymptotically optimal in **growth order** if that paper asymptotic is accepted. The counting formula is elementary combinatorics, and the injective original-source B-drain identity is Lean-certified. The exact combinatorial cardinality and the polynomial block bound have not separately been formalized as Lean counting theorems.

## Exact experimental cross-check

The independent [integer interpreter](check_dyck_safe.py), reusing the separately checked [complete one-level drain](check_third_ninefold.py), tested every coloured Dyck word of semilength n=0 through 7. Each code was distinct and its **entire** B-drain output agreed with the formula at three different pairs `(a,d)=(0,0),(1,7),(7,13)`.

| Semilength n | Number of distinct successful blocks | Maximum block |
| ---: | ---: | ---: |
| 0 | 1 | 6 |
| 1 | 2 | 60 |
| 2 | 8 | 546 |
| 3 | 40 | 4,920 |
| 4 | 224 | 44,286 |
| 5 | 1,344 | 398,580 |
| 6 | 8,448 | 3,587,226 |
| 7 | 54,912 | 32,285,040 |

The regression is corroboration of the quantified theorem, not its justification.

## Source proof and remaining frontier

The mathematical proof module is [DyckSafeSource.lean](DyckSafeSource.lean), compiled through the existing [manual pinned-source CI workflow](../../.github/workflows/agent49-623-flat-drain.yml) after the upstream modules from Agent49 and Agent8. The new theorems are `pathDrain`, `pathBlock_injective`, and `balanced_drain`, and their `#print axioms` directives are in the source. The source-audit run is [42575376619](https://github.com/FlareZ123/bb6/actions/runs/42575376619); check its complete verdict before asserting original-source CI success. A separate local Lean 4.36.0-rc2 exact recurrence proof has already compiled, with no `sorry` and no new axioms beyond the previously source-authenticated recurrence interface.

This result closes an important **synthetic** constructive counting gap for #623, showing explicitly that the known success-growth scale can be populated by a simple Dyck grammar. The authentic blank orbit `D(0,7)` is a deterministic single trajectory and might occupy a rare exceptional language. The result supplies no all-time blank-root invariant and no halting witness; the exact Busy Beaver value remains unknown. Root-specific inverse language closure, and not synthetic counting alone, is the decisive outstanding problem.
