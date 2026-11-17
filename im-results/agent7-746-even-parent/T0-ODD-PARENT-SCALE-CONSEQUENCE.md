# Incoming odd-parent scale for the special t=0 fatal entry

**Status:** exact conditional synthesis of the t=0 even-parent exclusion with OddResetLevelScale.lean. It narrows the only remaining immediate-parent family but does not exclude it. No Lean compile is claimed.

Let \(K\ge266\), \(p=2^K\), and let \(E\) be the authentic first entry at level \(K\) in the special \(t=0,L=K+1\) adjacent-even fatal history. Let \(D_{\rm ent}=8p+K-E\). The entry certificate gives
\[
4p\le E+K+4,\qquad E+K+5<8p,
\]
and the t=0 fatal reduction gives
\[
D_{\rm ent}=2^qD_0,\qquad q\le K-1.
\]

## 1. The even-parent family is exhausted

An even ResetParent from a source level \(L\) has target band
\[
6\cdot2^L-1\le E\le8\cdot2^L-3.
\]
If \(L\le K-2\), then
\[
E\le8\cdot2^{K-2}-3=2p-3.
\]
But the entry lower guard gives \(E\ge4p-K-4>2p-3\) for \(K\ge266\). Hence no even parent can come from \(L\le K-2\).

Because \(E\) is the *first entry* at level \(K\), its immediate reset parent must be at a lower level \(L<K\); a same-level even reset would be a later state in the level-K episode, not its entry. Thus the only possible even-parent level is \(L=K-1\). Agent 10's theorem t0_entry_even_parent_no_solution_of_source_band excludes exactly that case. Conditional on that theorem, **the authentic level-K entry E has no even ResetParent at all**.

The all-valuation ResetParent equivalence in FirstInverseComplete.lean then forces every possible immediate parent of E to be an odd reset from some lower level.

## 2. The incoming odd parent lies in a high source-level range

Suppose the immediate parent is odd, with source level \(L\), valuation \(t\), and odd quotient \(d\). Its exact data are
\[
6\cdot2^L+1\le2^td\le8\cdot2^L-1,\qquad
2E+5=3^{t+1}d.
\tag{1}
\]
The lower source bound and \(3^t\ge2^t\) imply
\[
2E+5=3\cdot3^td
\ge3\cdot2^td
\ge18\cdot2^L+3,
\]
so
\[
E\ge9\cdot2^L-1.
\tag{2}
\]
If \(L\ge K\), (2) gives
\[
E+K+5\ge9p+K+4>8p,
\]
contradicting the level-K upper guard. Therefore \(L\le K-1\).

Now apply odd_parent_level_scale_of_data from OddResetLevelScale.lean to (1) and the entry lower guard. It gives the exact scale restriction
\[
\boxed{t\le L,\qquad 2^{K-2}<3^L.}
\tag{3}
\]
Thus the only remaining immediate parent has
\[
\boxed{L\le K-1,\qquad 2^{K-2}<3^L,\qquad t\le L.}
\]
This is a source-level localization, not a reachability proof.

## 3. A simple integer lower bound

Since
\[
3^{17}=129140163<134217728=2^{27},
\]
the strict inequality \(2^{K-2}<3^L\) forces
\[
27L>17(K-2).
\]
Indeed, if \(27L\le17(K-2)\), then
\[
3^{27L}\le3^{17(K-2)}<2^{27(K-2)},
\]
which contradicts \(2^{K-2}<3^L\) after raising both sides to the 27th power.

Consequently
\[
\boxed{
\left\lfloor\frac{17(K-2)}{27}\right\rfloor+1
\le L\le K-1.
}
\]
At the first BB(6) range value \(K=266\), this gives \(167\le L\le265\).

## 4. What remains open

The odd-parent family is not empty merely because it is localized. One must still combine the exact t=0 fatal-source equation, the odd-parent factorization \(2E+5=3^{t+1}d\), the dyadic source band, and the authentic blank-root ancestry to exclude or construct such an incoming parent. The bounds above only narrow that task.

The source-level scale theorem and Agent 10's no-even-parent theorem should be kernel-checked before treating this conditional synthesis as a formal result.
