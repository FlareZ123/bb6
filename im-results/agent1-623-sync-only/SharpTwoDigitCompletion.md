# Sharp uniform two-digit completion theorem for the #623 full-rectangle synchronization language

**Status:** an exact all-prefix combinatorial theorem for the already-established #623 four-residue synchronization criterion. It is not an authentic blank-tape invariant, a branch-reachability theorem, or a machine decision. The proof is analytic, with a finite enumerator for independent corroboration.

## Theorem (optimal uniform synchronizing extension)

For **every** ternary digit-pair prefix \(w\) of length \(n\ge3\), **at least 24 of its 81 possible two-digit-pair continuations** \(wt\) synchronize both entire left and right carry rectangles. This lower bound is **sharp at every length \(n\ge3\)**: the all-zero prefix has exactly 24 such continuations.

Moreover, **two extra digit pairs are necessary in the worst case**. The all-zero prefix has *no* synchronizing one-digit-pair continuation.

Thus the synchronization language has a uniform, **optimal two-symbol completion horizon** for arbitrary prefixes; in fact at least \(24/81=8/27\) of all length-two continuations work. This is a property of the digit-pair language, not a rule that permits the deterministic #623 blank orbit to choose its next digits.

## Prefix-coordinate reduction

Use the unimodular coordinates \(U=Y\), \(V=X+Y\) modulo \(3^n\), as in [TwoCoordinate3AdicCocycle.md](TwoCoordinate3AdicCocycle.md). They are in bijection with the original digit-pair prefixes \((X,Y)\). Put \(M=3^n\). A length-\(n\) prefix is a residue pair \((U_0,V_0)\in(\mathbb Z/M)^2\); its \(81=9^2\) two-pair-digit continuations correspond bijectively to
\[
U=U_0+M u,\quad V=V_0+M v,\qquad u,v\in\{0,\ldots,8\}
\]
modulo \(9M\). Although the \(U,V\) digit lifts may include a carry relative to \(X,Y\), the coordinate change is invertible mod \(9M\), so every \((u,v)\) represents a unique original two-pair extension.

At target length \(n+2\), the four **bad** events are:

- \(A\): \(V-4U\bmod9M\) is one of the 6 signed residues \(-2,\ldots,3\).
- \(C\): \(4V-U\bmod9M\) is one of the 9 signed residues \(-7,\ldots,1\).
- \(E\): \(U\bmod3M\) is one of \(-1,0\).
- \(F\): \(V\bmod3M\) is one of \(-2,-1,0\).

Here \(n\ge3\) ensures the candidate constants in each family are distinct modulo \(M\), and hence **at most one target forbidden constant per family can extend a fixed prefix**.

## Finite-field incidence proof of the lower bound

Let \(A_2,C_2,E_2,F_2\subseteq\{0,\ldots,8\}^2\) denote the respective bad continuation sets for our fixed prefix.

Each of \(A_2,C_2\) is either empty or has **exactly 9** members. Indeed, if the prefix linear form matches its unique candidate forbidden integer modulo \(M\), the two new base-3 digits must satisfy one linear congruence modulo 9 whose coefficient of \(u\) and of \(v\) are both units mod 3. For each of nine \(u\)-values there is exactly one \(v\)-value. Equivalently, the first appended digits \((u_0,v_0)\in\mathbb F_3^2\) lie on an affine **nonvertical, nonhorizontal** line, with **three** legal second-digit pairs above each of its three first-digit points.

Each of \(E_2,F_2\) is either empty or has **exactly 27** members: an active \(E_2\) fixes the first appended \(u_0=u\bmod3\) while leaving \(u_1,v_0,v_1\) free; an active \(F_2\) fixes \(v_0=v\bmod3\). If both exist, their intersection has exactly \(3^2=9\) members, so \(|E_2\cup F_2|=27+27-9=45\).

Now consider three exhaustive cases.

1. **Both** \(E_2,F_2\) are nonempty. Any nonempty \(A_2\) intersects \(E_2\) in exactly **three** members: its affine first-digit line meets the fixed vertical line \(u_0=\mathrm{const}\) in one point, and there are three admissible second-digit pairs above it. Therefore \(A_2\) contributes **at most 6** new failures outside \(E_2\cup F_2\). The identical argument applies to \(C_2\). Thus total bad continuations are at most \(45+6+6=57\).
2. **Exactly one** of \(E_2,F_2\) is nonempty. Its bad set has 27 members; a nonempty \(A_2\) or \(C_2\) intersects that fixed vertical or horizontal first-digit fiber in three members. Thus total bad continuations are at most \(27+6+6=39\).
3. **Neither** \(E_2,F_2\) is nonempty. At most \(9+9=18\) continuations are bad.

In every case there are at most 57 bad continuations among 81, leaving **at least \(81-57=24\) synchronizing continuations**.

The argument is universal in \(n\); it uses no finite scan, approximation, spectral claim, word independence, or assumptions about original-machine reachability.

## Optimality at the all-zero prefix

Take \(U_0=V_0=0\pmod M\). The two-digit continuation is \(U=Mu,\ V=Mv\) with \(u,v\in\{0,\ldots,8\}\). At target length \(n+2\), the four bad events reduce to
\[
A_2:\ v-4u\equiv0\pmod9,\quad
C_2:\ 4v-u\equiv0\pmod9,\quad
E_2:\ u\equiv0\pmod3,\quad
F_2:\ v\equiv0\pmod3.
\]
Avoiding \(E_2,F_2\) leaves exactly \(6\cdot6=36\) pairs with both \(u,v\) nonzero mod3. Among these, \(A_2\) forces \(v\equiv4u\pmod9\) and excludes **6** pairs. \(C_2\) forces \(v\equiv7u\pmod9\) (since \(4^{-1}\equiv7\pmod9\)) and excludes another **6**. These are disjoint: equality of both would force \(3u\equiv0\pmod9\), contradicting \(u\not\equiv0\pmod3\). Exactly
\[
36-6-6=\boxed{24}
\]
continuations synchronize, for **every** \(n\ge3\).

For a **single** appended pair at target length \(n+1\), the bad E condition tests \(U\bmod3^n\), which is still zero regardless of the appended digits; hence **all nine** one-digit continuations fail. Two-digit lookahead cannot be reduced to one uniformly.

## Significance

The finite synchronization transducers admit a sharp, very short **existential reset completion** even from an adversarial input prefix. By contrast, [InfiniteConeSyncNonclosure.md](InfiniteConeSyncNonclosure.md) proves that the original accelerated #623 dynamics can make a previously synchronizing word become non-synchronizing; the authentic root cannot freely choose the two additional digits guaranteed here. Therefore the useful next direction is a **root-history / source-digit restriction** strong enough to force at least one of these 24 continuations, or an alternative invariant not based on unconstrained word completion.

[count_two_digit_completions.js](count_two_digit_completions.js) directly enumerates every prefix of lengths \(n=3,4,5\) and each of its 81 completions, checking the global minimum 24. It is not needed for the all-\(n\) proof above.
