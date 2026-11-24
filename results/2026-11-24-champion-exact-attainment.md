# Exact primitive-step halting count of the six-state champion

**Theorem (Lean 4.36.0-rc2, 24 November 2026).** The literal six-state two-symbol blank-start table
`1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE`
halts at the score specified below. Consequently BB(6) is at least this exact natural number. This does not assert that the machine is a universal maximizer.

## Exact count

Write the section endpoint and cost as a function S(n,m,a,b) of a positive-counter countdown. Its base value is (m mod 3,a,b,0) at n=0. At each decrement, for current counter k>0, use

- cost I(m,k,a,b) = 6·4^b + 42·2^b + 15 + 4(m mod 3) + 12(a+v₂(k)) − 9b;
- marker m'=(m+2) mod 3;
- exponent a'=a+b+1 when m mod 3=0, and a'=a+b+2 otherwise;
- right parameter b'=2^b−1.

Add the cost I and continue at (k−1,m',a',b'). All operations are exact natural-number operations (the displayed cost subtractions are nontruncating). Let X(L,a)=2^(L+a+2)−2^a−1, R(L,a,b)=12(L+a)+6·4^b+42·2^b+49−9b, and T(L,a)=59+12(L+a).

Define
```
f = S(7, 2, 6, 63)
L1 = 3 + f.exponent + 2
g = S(X(3, f.exponent), 2, f.right, 2^f.right - 1)
L2 = L1 + g.exponent + 2
j = S(X(L1, g.exponent), 2, g.right, 2^g.right - 1)
N = 27959 + f.cost + R(3,f.exponent,f.right)
          + g.cost + R(L1,g.exponent,g.right)
          + j.cost + T(L2,j.exponent)
C = N + 7
```

The exact step score is C. This is a finite recursive specification of an integer, not an asymptotic estimate or an unchecked proposed runtime. No expansion of its enormous decimal representation is necessary.

## Proof

1. The original normalized machine TM63 has a source-checked blank prefix of 27959 successful moves entering the exact binary/unary S1 configuration at width 3 and parameters (n,m,a,b)=(7,2,6,63).
2. The uniform positive-counter theorem covers every marker and every positive n<2^L at widths L≥3, arbitrary b and head position, and a>0. It proves exact source run equality and the primitive-step cost I, including the entire carry/drain.
3. The marker-1 zero-counter source reset proves the exact next width, counter, tape and cost R for arbitrary parameters, including the final drain. The two reset indices fit their increased widths.
4. The marker arithmetic proves that the first two complete countdown sections terminate with marker 1, and the third with marker 0. Induction over the counter gives the whole-section cost S without evaluating astronomical counters.
5. The terminal source macro consumes exactly T successful steps before the undefined query. The proved literal-table state renaming and root join add six successful steps to the TM63 count. The final halting query adds one step.

The resulting named theorem is
```lean
theorem champion_halts_exact :
    HaltsAfter championTable (proposedTM63Moves+6) :=
  direct_root_halts increment_source reset_source
```
Here HaltsAfter m n means the blank run exists through n ordinary moves and has no successor at n+1. Thus the exact halting score is C = N+7 in the standard final-transition-counting convention.

## Source and reproducibility

- [Final theorem and maximality interface](../im-results/agent48-counted-inc0/TM63DirectRootAttainment.lean), commit [9445d6cf](https://github.com/FlareZ123/bb6/commit/9445d6cf58dea3fc62aca9a9a2ddd064674c76ae).
- [Symbolic three-section composition](../im-results/agent48-counted-inc0/TM63DirectRootComposition.lean).
- [Complete positive-counter law](../im-results/agent48-counted-inc0/TM63CompleteIncrementSource.lean).
- [Marker-1 reset macro](../im-results/agent8-rst1prime/Rst1PrimeBridge6Source.lean).
- [Integer specification](../im-results/agent24-champion-time/CostRecurrence.lean).
- [Clean source build](../im-results/agent48-counted-inc0/reproduce-exact-champion.sh), run with Lean 4.36.0-rc2 installed.

The complete transitive source closure was compiled locally, including the restored authoritative compressed terminal modules. The kernel's axiom audit for the named halting theorem and its attainability corollary lists only `[propext, Classical.choice, Quot.sound]`. The manual repository acceptance target runs the clean build and checks these final theorem axiom profiles. No source-run or cost premise remains in the final halting theorem.

## Remaining exact-BB(6) obligation

The theorem `champion_maximum_of_cover` reduces the equality BB(6)=C to an actual exhaustive `Cover (DecidedBelow C) emptyTable`. This upper-bound proof is **not** currently available. A proved halting score for one machine cannot exclude a different machine with a larger score.

The mathematical claim here is a certified exact score for a known champion, not a new machine discovery, a priority claim about its halting behavior, or a claim that BB(6) has been solved.