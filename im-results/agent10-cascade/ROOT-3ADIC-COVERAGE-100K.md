# Root level-entry 3-adic coverage: 100,000 exact reset transitions

**Status:** intermediate computational observation; not a proof of nonhalting and not an academic result.

## Reproduction

Run:

```bash
python im-results/agent10-cascade/root_forward_3adic.py --steps 100000
```

The script uses arbitrary-precision integer arithmetic and the first-reset equations represented by `ResetParent` in `FirstInverseComplete.lean`.  The optimized first-failure search starts at (\max(0,\lfloor\log_2 h\rfloor-2)): if (k\le m-3), then (8\cdot2^k\le2^m\le h\le h+k+5), so such a (k) cannot be the first failure.

For source height (h), let (k) be the least index with (h+k+5<8\cdot2^k).  The transition is:

- halt if (h+k+4=4\cdot2^k);
- even branch: (2u=8\cdot2^k+h+k);
- odd branch: (q=4\cdot2^k+\lfloor(h+k)/2\rfloor+3=2^t d), (d) odd, and (2u+5=3^{t+1}d).

The script also checks that the level index never decreases and that odd transitions strictly increase it.

## Exact finite-run observations

For 100,000 successful reset transitions from (h_0=2):

- no halting state was encountered;
- 49,716 level exits occurred, giving 49,717 level entries including the root;
- the final first-failure level was (K=77,220), and the final height had 77,223 bits ((\lfloor\log_2 h\rfloor=77,222));
- the largest odd-branch exponent (t) was 16;
- the three initial level exits were even; the remaining 49,713 were odd;
- from (K\ge4), every observed terminal residual (D_K=8\cdot2^K+K-h) was odd and strictly greater than (4K+10).  The smallest margin (D_K-(4K+10)) was 13, at (K=5).

These are finite-run statements only.  In particular, the all-odd tail is an observed property of this root prefix, not an established invariant.

## 3-adic coverage of level-entry heights

A level entry is the initial height at a new value of (K(h)), including (h=2).  The table records the distinct residues (h\bmod 3^a) seen in the 49,717-entry prefix.  Every possible class congruent to (2\pmod3) is covered through (3^7).

| Modulus | Possible classes (r\equiv2\pmod3) | Seen | First prefix length giving full coverage | Same-level fatal congruence matches |
|---:|---:|---:|---:|---:|
| 9 | 3 | 3 | 4 | 5,551 |
| 27 | 9 | 9 | 39 | 1,884 |
| 81 | 27 | 27 | 259 | 633 |
| 243 | 81 | 81 | 1,212 | 218 |
| 729 | 243 | 243 | 3,735 | 75 |
| 2,187 | 729 | 729 | 16,448 | 21 |
| 6,561 | 2,187 | 2,186 | not reached | 6 |

At modulus 6,561, the only missing class is 530.\n\n“Same-level fatal congruence match” counts entries ((K,h)) with
(h\equiv F_K\pmod{3^a}), where (F_K=4\cdot2^K-K-4).  Such matches automatically occur only in the eligible (K\bmod6\in\{4,5\}) sectors because all observed entries are (2\pmod3).

## Research implications and cautions

1. A fixed-modulus test of the form (h_K\not\equiv F_K\pmod{3^a}) cannot exclude this finite root prefix for any (a\le7): the prefix contains actual same-index matches at every such precision.  There are also six matches modulo (3^8).  This does **not** rule out arguments using additional state variables, depth, inequalities, or moduli growing with (K).
2. The level-entry heights cover every (2\pmod3) residue modulo (3^7).  This is evidence against a simple fixed 3-adic residue invariant, not a proof that the infinite root orbit is 3-adically dense or equidistributed.
3. The observed odd-exit tail suggests a root-specific invariant worth investigating.  The tempting generalization “(D_K) odd and (D_K>4K+10) implies the next level also exits oddly” is false without further hypotheses.  A valid counterexample is (K=8,h=1965,D_8=91>42): the odd reset has (q=2013,t=0), and reaches (3017) at (K=9).  Its level-entry deficit is (1088), whose same-level even reductions are (1088,544,272,136,68,34); since (34<4\cdot9+12), the next exit is even.  The root path avoids this example, so any induction must encode more than the lower bound on (D_K).

The next mathematically meaningful target is therefore not another fixed-modulus sieve.  It is a root-specific description of the terminal deficit / odd-exit map strong enough to explain why the actual orbit remains in the observed odd-exit region, or else to find a fatal entry.
