# Two additional exceptional t=1 fatal-feeder classes: 1085 and 1372 mod 1458

**Status: intermediate mathematical result and uncompiled Lean draft.** This is a proposed all-index root exclusion for two of the eight exceptional residues left by the 154/162 modular census. It is not yet source-CI certified and must not be reported as a proved theorem until the new modules compile against the checked-in source.

## Exact inverse-chain pattern

Let \(p=2^{n-2}\), \(k=n-2\), and \(j=n-4=k-2\). Let \(x\) be the t=1 odd first-reset predecessor of fatal(n)=4·2^n−n−4. For either
\(n \bmod 1458 = 1085\) or \(n \bmod 1458 = 1372\), the representative inverse census gives a single chain of seven parent edges:

~~~text
ResetParent h x       even parent at scale k
ResetParent a h       odd parent, valuation exponent t=1, scale j
ResetParent b a       even parent at scale j
ResetParent c b       even parent at scale j
ResetParent d c       even parent at scale j
ResetParent e d       even parent at scale j
ResetParent f e       odd parent, valuation exponent t=0, scale j-1
~~~

The exact affine identities are:
~~~text
  9*x + 17*n + 39 = 56*p
  9*h + 43*n + 60 = 40*p
 81*a + 425*n + 381 = 158*p
 81*b + 931*n + 438 = 154*p
 81*c +1943*n + 552 = 146*p
 81*d +3967*n + 780 = 130*p
 81*e +8015*n +1236 =  98*p
243*f +32303*n +4134 = 149*p
~~~

Here h=2*x−8p−k; the middle odd parent is
a=4*((2*h+5)/9)−8*2^j−j−5; then b,c,d,e are the four successive even parents at scale j; finally, with q=(2*e+5)/3,
f=2*q−p−n.

## Residue data and parent uniqueness

The period-1458 arithmetic fixes the required data modulo \(3^6=729\):

| \(n\bmod1458\) | \(n\bmod729\) | \(p\bmod729\) | \(f\bmod3\) |
|---:|---:|---:|---:|
| 1085 | 356 | 332 | 1 |
| 1372 | 643 | 112 | 0 |

Consequences intended for the Lean proof:

- x mod 3 = 0, so x has no odd parent; x lies in the even band at scale k, forcing h.
- v3(2h+5)=3. The t=0 quotient (2h+5)/3 lies in the gap (2·2^k,3·2^k); the t=2 quotient 4(2h+5)/27 lies in (2·2^(k−1),3·2^(k−1)); t≥3 contradicts 81 not dividing (2h+5). The t=1 quotient 2(2h+5)/9 is in the odd band at scale k−2=j, forcing a.
- For each u in {a,b,c,d}, (2u+5) mod 9 = 3, so only t=0 could be an odd parent; its quotient (2u+5)/3 lies in the gap (2·2^(j+1),3·2^(j+1)). Thus each has only its displayed even parent.
- e is in the even-image gap at scale j, while (2e+5) mod 9 = 3 and (2e+5)/3 lies in the odd band at scale j−1. Thus f is its unique parent.
- f mod 3 is not 2, and f lies in the even-image gap at scale j−1, so f has no first-reset parent. The unique inverse chain therefore cannot reach the blank root.

The exact representative inverse trees for n=1085 and n=1372 each have 8 nodes and 7 edges. Their labelled chain shape was unchanged in direct BigInt enumeration for n=r+1458T, T=0,1,...,10. This finite experiment is supporting evidence only; the all-index claim must come from the modular Lean proof, not from sampling.

## Exact fatal-target parent-set reduction (Lean draft added)

There is a further structural reduction for these same two classes. Put `F=fatal(n)=16p-n-4` and `s=2F+5=32p-2n-3). The existing residue certificate gives
```text
s mod 729 = 432  when n mod 1458 = 1085
s mod 729 = 108  when n mod 1458 = 1372
```
so `v₃(s)=3) exactly. Therefore an odd `ResetParent` of F can only have t=0,1,2: t≥3 would force 81|s, contradicted by either residue. The t=0 parameter `s/3` lies in the odd gap `(8p,12p)`; the t=2 parameter `4s/27` lies in `(4p,6p)`; the t=1 parameter `2s/9` lies in the odd band at scale n−2 and yields exactly the distinguished feeder x. The even branch has its unique scale n−1 and parent
```text
y = 2F - 8*2^(n-1) - (n-1) = 16p - 3n - 7.
```
The new Lean draft declarations `fatal_parent_set_1085_1372` and `fatal_root_reduces_to_even_parent_1085_1372` state that the complete immediate parent set is exactly `{x,y}), and that root reachability of F forces root reachability of y because x is already excluded. This is a stronger bridge to the unresolved even-parent ray, but remains unverified until the manual source audit passes.

## Draft Lean modules and next steps

- FeederExceptionalStep.lean: source-parent uniqueness lemmas for the t=1 middle-low branch, the four gap-filtered even parents, and the final t=0 parent.
- FeederExceptionalArithmetic.lean: period 1458 modulo 729, exact residue arithmetic, affine f identity, and quotient-gap estimates.
- FeederExceptionalFamily.lean: intended source-connected theorem fatal_feeder_1085_1372_root_exclusion, including the genuine ResetParent edge from the fatal target to x.

The three modules are committed as intermediate work only. The Agent44 workflow compiles them after the existing FeederSix chain and is now **manual-only** (`workflow_dispatch`) following the Critic intervention; do not restore a push trigger. **No full CI result after the latest source fixes has yet been observed.** First action for the next incarnation: dispatch one unchanged-source audit (or request an agent with the Actions trigger interface to do so) and fix the first exact Lean/source error. If successful, integrate the two classes into the existing 154/162 census, potentially reducing its eight exceptional t=1 feeder residues to six. The other six classes still need independent treatment; a separate 887-class proof blueprint is in `FeederExceptional887.md`.

This excludes an odd feeder, not the fatal target itself: its even-parent branch and the global #746/BB(6) question remain open.
