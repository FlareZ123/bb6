# No regular binary inductive invariant for the Sheep raw return

**Agent 16, 24 November 2026. Mathematical proof (not a complete Lean formalization).** This closes the intermediate-exponential-growth loophole in [GROWTH.md](GROWTH.md). There is no nonempty regular language of canonical binary integers >=5 which is forward closed under the genuine Sheep section relation and excludes all terminal powers. No conjecture about unbounded valuations on the authentic orbit is required. The proof uses the previous zero-prefix-transient theorem (including its prepared-halting density dependency), a bounded-valuation cylinder count already supported by Lean, and a new finite phase-fibre argument.

## 1. General lemma: finite automata have finitely many high-phase fibres

Let L be a regular language of canonical LSB-first binary positive integers. Let Q be the finite state set of a complete deterministic automaton recognizing it, q0 its start, and delta its word action. Write v(w) for a word's binary value in reading order. Use the circle T = R/Z with phase phi(n)=log2(n) modulo 1.

For each state q define H_q to be the set of limits of phi(v(w_j)), where w_j are canonical words accepted starting at q and v(w_j) tends to infinity. This is a closed subset of T, possibly empty: equivalently it is the intersection over B>=1 of the closures of the phases of canonical accepted words of value >=B.

Define K to be the set of joint limits (z,theta) of (n,phi(n)) with n in L tending to infinity, the first component converging in the 2-adic integers Z_2, the second in T. Formally K is the intersection over B>=1 of the closures of these pairs with n>=B in the compact product Z_2 x T. It is compact and nonempty if L is infinite. For any z in Z_2 define its phase fibre H(z)={theta:(z,theta) belongs to K}.

Let w_k be the first k binary digits of z, in LSB reading order, and q_k=delta(q0,w_k). The set of phase limits of arbitrarily large L members sharing the low k digits w_k is **exactly H_qk**. Indeed their words are w_k u with u accepted starting at q_k, and for arbitrarily large such words the tail u is itself canonical. The integer is v(w_k)+2^k v(u); the phase difference from phi(v(u)) tends to zero on T. Conversely every canonical accepted u from q_k yields a canonical accepted w_k u. Consequently H_q(k+1) is a subset of H_qk: the low-prefix condition gets stronger.

We have H(z) = intersection of H_qk over all k. One direction follows by taking low prefixes of any joint-limit sequence. For the reverse direction, for each k choose a member of L of value >=k agreeing with z on its first k digits and with circle phase within 1/k of theta, possible by the phase-limit characterization. This gives the joint-limit sequence. As there are only |Q| possible H_q, the descending sequence of sets H_qk eventually stabilizes, and H(z) equals one of these finitely many sets.

**Full fibre implies full growth.** Suppose some H(z)=T. Then for every m>=1 and every canonical m-bit leading pattern p, there exists an accepted word of length at least m whose highest m bits equal p. To see this, choose a phase strictly interior to the interval corresponding to the leading mantissa p. A sequence of accepted integers approaching that phase and tending to infinity eventually has this high prefix. In LSB reading order p reversed is the fixed final block w of length m. Some reachable automaton state q' accepts w as a continuation. Replace the preceding prefix by a shortest path from q0 to q'; this has length <=|Q|-1. The resulting word is still canonical (its last bit is 1), still accepted, and has high pattern p. Distinct patterns give distinct words, even if the lengths differ. Hence
```
sum_{j=m}^{m+|Q|-1} #L_j >= 2^(m-1),
```
where L_j is the set of accepted canonical words of length j. In particular limsup #L_j^(1/j)=2.

## 2. A rotation principle for piecewise affine integer dynamics

Suppose an infinite regular set L of positive integers is eventually forward closed under a map F: every sufficiently large member has F(n) in L. Assume all such members belong to finitely many disjoint clopen 2-adic branch domains; on branch a the map is F_a(n)=r_a*n+b_a, where r_a>0 and b_a are rational constants. The affine formula is understood on that 2-adic domain and maps its relevant limit points to Z_2. Suppose every nonempty finite product of the r_a is multiplicatively independent of 2 (its base-2 logarithm is irrational).

For any (z,theta) in K, choose an actual joint-limit sequence n_j. It is eventually in the unique clopen branch domain of z. The affine formula and r_a>0 imply F(n_j) tends to infinity, converges 2-adically to F_a(z), and its phase converges to theta+log2(r_a) modulo 1. Eventual closure therefore gives
```
H(z) + log2(r_a) subset H(F_a(z)).
```
This applies to every theta in H(z); the branch a depends only on z, not on theta. The projection P of K is nonempty and forward invariant, so start at any z_0 in P and iterate z_(i+1)=F_a_i(z_i). Every H(z_i) is nonempty. Finitely many possible fibres imply that for some i<j, H(z_i)=H(z_j). Composing the inclusions gives
```
H(z_i) + log2(product_{i<=k<j} r_a_k) subset H(z_i).
```
The angle is irrational modulo 1 by assumption. Any nonempty closed set of the circle containing its rotation by an irrational angle contains the dense forward rotation orbit of each of its points. Thus H(z_i)=T. By section 1 the language has full exponential growth rate 2.

This argument needs no invariant probability, independence of digits, rationality of the initial 2-adic point, periodicity of the valuation itinerary, or rational-point orbit conjecture. The only recurrence is repetition of a member of a finite collection of closed phase sets.

## 3. Application to Sheep

Assume a nonempty regular language I of canonical binary integers >=5, forward closed under the exact nonterminal Sheep raw-return edges and disjoint from the powers of two. The exact section relation is
```
x=2^a*u, u odd >=3;
F(x)=x+a+3                  if u=3,
F(x)=x+a+(u-1)/2            if u>=5.
```
Every member has a genuine successor, strictly larger, so I is infinite. By [ZERO-TRANSIENT.md](ZERO-TRANSIENT.md), if t is the transient of the initial state's zero-action orbit, every member has valuation a<t. This earlier result uses the paper-level [prepared-halting residue/phase density theorem](../agent17-sheep-terminal-extension/README.md); its discrete pumping lemma was Lean checked. In particular t>=1 and all valuations are bounded by A=t-1.

Above 3*2^A every return uses the generic affine branch
```
r_a=(2^(a+1)+1)/2^(a+1), b_a=a-1/2.
```
The branch domains v2(z)=a, 0<=a<=A, are disjoint clopen sets in Z_2. Their finite union contains the 2-adic projection of K, because every large accepted integer has one of those valuations. The affine expression extends continuously on the corresponding domain and has integer 2-adic output: write z=2^a*u, u odd in Z_2, then F_a(z)=z+a+(u-1)/2. Every nonempty finite product of expansion factors equals N/2^c with N an odd integer >=3 and c a positive integer. Its logarithm is irrational: if log2(N/2^c)=p/q with q>0, then N^q=2^(p+c*q), impossible by oddness and N>1. Thus section 2 implies I has growth rate exactly 2.

But [GROWTH.md, section 5](GROWTH.md) gives the strict bound
```
#I_n <= (A+1)*lambda_A^(n+A), for sufficiently large n,
sum_{k=1}^{A+1} lambda_A^(-k)=1, 1<=lambda_A<2.
```
Recall the elementary reason: same generic valuation word of total cost c=sum(a_i+1) determines at most one start modulo 2^c. A first prefix reaching c>=n has cost at most n+A, and the number of words at cost c obeys the finite-composition recurrence. This is a counting bound on the language, not a probability assumption about the actual orbit. The supporting congruence and injectivity are kernel checked in [RawCylinder.lean](RawCylinder.lean). Contradiction.

**Theorem.** No nonempty regular language of canonical binary integers >=5 can exclude all powers of two and be forward closed under the genuine Sheep raw-return relation. In particular no such inductive invariant contains the authentic blank-entry section x=5.

**Stronger conditional formulation independent of prepared-halting density.** No infinite regular subset of positive integers with bounded 2-adic valuation can be eventually forward closed under generic Sheep raw returns. The same proof of the growth bound works with eventual closure by choosing a large enough initial x; all subsequent returns are larger. More generally no infinite regular subset of the set of bounded-valuation all-time survivors can itself be eventually forward closed. This conditional formulation needs no use of the prepared-halting theorem.

## 4. Exact scope

The original-machine source bridge is [Agent22's certified theorem](../agent22-sheep-semantic-bridge/README.md), accepted in CI 41390686337. The proof above is a complete written mathematical deduction from the stated existing prepared-density and exact section results; the compact 2-adic/log-circle and automata arguments have not been formalized in Lean. It is stronger than the earlier permutation, sparse, and bounded-growth obstructions, but it is not a Sheep nonhalting proof, nor does it show that the actual orbit is nonregular, has unbounded valuations, or reaches a power. A nonregular inductive invariant, a different accelerated domain, or a root-specific arithmetic proof remains possible. No BB(6) bound changes. External novelty and independent review are pending.
