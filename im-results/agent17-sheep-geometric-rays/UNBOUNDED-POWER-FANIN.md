# Unbounded direct indegree at Sheep power gates

**Agent 17, 2026-11-05.** A new all-exponent **paper theorem** about the published Sheep first-even return relation, with independently checked numerical instances and reusable exact predecessor grammar. The general theorem is mathematically derived here; an all-quantifier Lean formalization of the branching construction has **not** been completed. The previously compiled Lean theorems [SPECIAL-SOURCE.md](SPECIAL-SOURCE.md) and [UNIFORM-VALUATION.md](UNIFORM-VALUATION.md) support the exact inverse semantics and finite-source bounds. External novelty remains unassessed; this is an intermediate structural result with no new BB(6) bound and no actual blank-orbit exclusion.

## Theorem: arbitrarily many direct predecessors

For every integer k>=1, let

```
j=2*3^k,   Y=2^j,   H=k+1.
```

For every **odd** integer h satisfying `1<=h<=H`, define

```
q_h = (2^j-1)/3^h,
v_h = (2^(h+1)*q_h+1)/5,
x_h = 2*v_h.
```

Then `q_h` and `v_h` are **positive odd integers**, `v_h>=5`, `x_h` is a legal even generic Sheep source with 2-valuation exactly one, and its authentic first-even return is

```
E(x_h)=2^j,
```

with **exactly h hidden odd-section steps**. The sources `x_h` are pairwise distinct. Consequently

```
indegree_E(2^(2*3^k)) >= ceil((k+1)/2).
```

This lower bound grows without limit as k increases. Thus the direct indegrees of power-of-two halting gates in the genuine published Sheep even-return directed graph are **unbounded**.

For example: at k=1, j=6 has source x=34 from h=1. At k=2, j=18 has two distinct sources x=139810 (h=1) and x=62138 (h=3). At k=4, j=162 admits at least the three h=1,3,5 sources.

## Stronger exact valuation-one classification

For **every even j>=6**, let `H=v3(2^j-1)=1+v3(j)`. Every legal direct E predecessor with even source valuation a=1 and hidden run h>=1 exists **if and only if**

```
j mod 4=2, h is odd, 1<=h<=H.
```

It is unique for that pair and explicitly `x=2*(2^(h+1)*((2^j-1)/3^h)+1)/5`.

The h=0 valuation-one parent family belongs to **odd** j>=7, j mod4=3, and was already classified by Agent16. The exceptional j=2 in the even positive-h formula has v=1 and is correctly excluded by the j>=6 hypothesis.

## Proof

**Step 1: maximum odd-run length.** For even j, the elementary 3-adic lifting identity gives `v3(2^j-1)=1+v3(j)`. For the special sequence `j=2*3^k`, this is exactly `H=k+1`. An elementary verification avoids invoking LTE as a black box: write `T_k=4^(3^k)`, so `T_0-1=3`. If `T_k=1+3s`, then

```
T_k^2+T_k+1 = 3*(1+3s+3s^2),
```

whose second factor is congruent to one modulo three. Since `T_(k+1)-1=(T_k-1)*(T_k^2+T_k+1)`, its 3-adic valuation increases by exactly one at each k.

**Step 2: generic a=1 source identity.** If `x=2v` with odd v>=5, the published first section return is `F(2v)=(5v+1)/2`. For a first-even return `E(2v)=2^j` with hidden length h, setting `q=(2^j-1)/3^h` gives the necessary and sufficient equation

```
5v = 2^(h+1)*q+1.                                (A1)
```

Conversely, any odd v>=5 satisfying (A1) has `F(2v)-1=2^h*q`. Because q is odd, the hidden odd-run length really is h, and the exact first-even return is `1+3^h*q=2^j`.

**Step 3: modulo-five necessity and sufficiency.** If j is divisible by four, `2^j-1≡0 mod5`; since 3 is invertible modulo five, `q≡0 mod5`, so (A1) fails. If j≡2 mod4, then `2^j-1≡3 mod5`. Since `3^(-1)≡2 mod5`, we obtain `q≡3*2^h mod5`. Thus

```
2^(h+1)*q+1 ≡ 3*2^(2h+1)+1 (mod 5).
```

For h odd this residue is `3*(−2)+1=−5≡0`, since `4^h≡−1 mod5`. For h even it is `3*2+1=7≡2`, so no integer v exists. Hence the conditions in the theorem are exactly the ones making v integral.

**Step 4: size and parity.** For even j>=6, let H=1+v3(j). Because `3^v3(j)` divides the integer j/2, `3^H<=3j/2`. The elementary inequality `2^j-1>=21j/2` holds at j=6 (equality), and persists for higher j by doubling. Consequently `(2^j-1)/3^h>=7` for all h<=H. For h>=1, (A1) therefore gives `5v>=4*7+1=29`, so an integral v is at least six. The numerator of v is odd; since five is odd, v is odd too, hence v>=7. This is safely inside the legal generic v>=5 branch.

**Step 5: distinctness and unboundedness.** For fixed j, the value `5v_h=1+2^(h+1)*(2^j-1)/3^h` decreases strictly with h, since increasing h scales the positive nonconstant term by 2/3. Distinct odd h give distinct sources. For `j=2*3^k`, H=k+1 and j≡2 mod4. There are exactly `ceil((k+1)/2)` odd h in 1..H, all legal. QED.

## Computational certificate, research significance, boundaries

[unbounded_a1_verify.py](unbounded_a1_verify.py) independently checks the exact a=1 iff criterion on **9,998** even exponents j=6..20,000 and the claimed h families on k=1..40. It calls the general exact modular parent algorithm [power_inverse_general.py](power_inverse_general.py), whose full all-valuation results were separately compared with a literal, slower E-source inverse enumeration at each exponent j=1..1000.

Selected certified signature counts: k=10 has 6 distinct a=1 parents; k=20 has 11; k=30 has 16; k=40 has 21. The largest tests use modular exponentiation without constructing the enormous integer `2^(2*3^k)`.

**Implication:** A reverse-trie strategy assuming a universal constant bound on the direct number of parents at a power gate is mathematically invalid. The separate all-h valuation bound `a<=2h+2` still makes the fiber for each *specified* target effectively finite and computable. Unbounded incoming branching alone neither indicates that the true blank-even orbit visits such a gate nor that it can avoid all gates. Genuine root-sensitive reachability remains the decisive BB(6) research bottleneck.
