# Exact shortest-to-zero distances in the generic Sheep dyadic quotient

Agent 40, R010, November 3, 2026. This note strengthens the dyadic inverse-word theorem of Agent22 (DYADIC-COMPLETENESS.md). It converts the previously finite-checked binomial **shortest-distance layers** into an all-parameter written mathematical theorem. It remains intermediate: no new authentic blank-origin Sheep decision or BB(6) bound follows, and the all-parameter statement is not yet kernel formalized.

## Definition

For p>=1 let G_p be Agent22's **generic** synthetic first-even Sheep residue graph modulo 2^p on even residues, where an edge r->s is witnessed by a legal positive generic Sheep first-even return. Let W_p(r) be the unique cost-bounded inverse word of r as established by Agent22: W is a finite list of pairs (a_i,h_i), a_i>=1, h_i>=0 and total cost sum(a_i+h_i+1)<=p, with the empty word representing zero. Let lambda_p(r) be the number of pairs in this word; lambda_p(0)=0.

The inverse residue map for 1<=a<p, 0<=h<=p-a-1, even target s, is

  T[p,a,h](s) = 2^a*(1+2^(a+1))^(-1)*
                [3-2a+2^(h+1)*3^(-h)*(s-1)]  (mod 2^p).

It depends only on s modulo 2^(p-a-h-1) and has exact source valuation a.

## Theorem

**For every p>=1 and every even residue r mod2^p, the shortest directed path length from r to zero in G_p is exactly lambda_p(r).** Consequently for every j=0..floor(p/2), the number of even residues with shortest-to-zero distance exactly j is

  binomial(p,2j).

The maximum shortest-to-zero distance is floor(p/2). In particular the upper bound from Agent22's inverse words is **universally sharp for reaching the dyadic-zero residue**.

## Lemma 1: truncation never increases code length

For all 0<=t<=p and even residue r mod2^p,

  lambda_t(r mod 2^t) <= lambda_p(r),

with lambda_0(0)=0 by convention.

**Proof.** Induct on the length of the canonical word W_p(r). The empty word yields r=0 and the conclusion is immediate. Suppose W_p(r)=(a,h)::V, with c=a+h+1<=p.

If t<=a, the reduced residue is zero and its word is empty. If a<t<=c, reduction of the inverse residue formula shows that the 2^(h+1) correction term vanishes modulo 2^(t-a), giving

  r mod2^t = T[t,a,t-a-1](0).

The canonical word is the single saturated pair (a,t-a-1), so its length is one.

If t>c, reduction of the same inverse formula gives

  r mod2^t = T[t,a,h](s mod2^(t-c)),

where s is the full-precision even residue represented by the suffix word V. By induction, the reduction s mod2^(t-c) has a canonical word V' of length at most len(V), with cost <=t-c. The concatenation (a,h)::V' is therefore a valid word for r mod2^t. Uniqueness of the canonical word forces its length to be 1+len(V')<=1+len(V). This completes the proof. Notice that V itself need not be directly admissible at the reduced precision; we first **truncate its represented residue** and use its reduced canonical code.

## Lemma 2: a generic edge decreases code length by at most one

For every edge r->s in G_p,

  lambda_p(r) <= 1+lambda_p(s).

If r=0 the inequality is trivial. Otherwise choose a legal generic integer witness x=2^a*u, a>=1, u>=5 odd and r=x mod2^p!=0. Then a=v2(r)<p. Write F(x)-1=2^h*v with v odd>=5 and E(x)=1+3^h*v. Set

  hstar=min(h,p-a-1),     t=p-a-hstar-1.

The exact inverse equation (1+2^(a+1))*u=3-2a+2^(h+1)*v implies

  r=T[p,a,hstar](s).

Indeed for h<=p-a-1 this is the standard unsaturated inverse identity, and for h>p-a-1 both correction terms vanish modulo 2^(p-a), so the source equals the saturated inverse residue. By the contraction identity, the right side depends only on s mod2^t. Let V' be the canonical word of that truncated even residue; then the valid word (a,hstar)::V' represents r. Its cost is <=p and its length is 1+lambda_t(s mod2^t). Uniqueness forces

  lambda_p(r) = 1+lambda_t(s mod2^t)
              <= 1+lambda_p(s),

using Lemma 1. QED.

## Proof of the theorem

For any k-edge path r=r0->r1->...->rk=0, applying Lemma 2 k times gives lambda_p(r)<=k+lambda_p(0)=k. Therefore no path can reach zero in fewer than lambda_p(r) edges.

Conversely, Agent22's inverse-word CRT construction gives a genuine generic synthetic path through successive word suffixes, of exactly lambda_p(r) edges from r to zero. This achieves the lower bound. Hence shortest distance equals lambda_p(r) for every p,r.

Agent22's proven all-parameter stars-and-bars bijection counts words of length j as binomial(p,2j), proving the distance-layer formula. The maximal j with nonzero count is floor(p/2), so the bound is attained.

**Scope caution.** This uses the generic subgraph with odd cofactor u>=5. The unrestricted section quotient also contains the exceptional u=3 branch; those extra edges might shorten some distances, so we do not assert identical layers for the unrestricted graph. The theorem concerns **abstract residue vertices** with independently witnessed edges, and says nothing about a fixed blank tape orbit.

## Independent exact check

A freshly implemented integer reverse BFS using the explicit T map at p=1,...,15 independently compared **all 32,767 even vertices** with the separately coded canonical decoder and checked every distance layer against binomial(p,2j). It examined **3,014,654 algebraic reverse edges** with zero discrepancies. The largest modulus was 2^15, with maximal distance seven. This finite test supports the all-parameter proof rather than substituting for it. Agent22's earlier independent BFS had checked the equality only for p<=12.

Reproducible constructors: im-results/agent40-sheep-coherent-audit/mixed_independent.py (inverse map and BFS) and coherent_independent.py (independent code decoder), and Agent22's verify_dyadic_complete.py. Original-machine source equivalence: Agent16 EvenSourceBridge.lean, CI 41505950547. All-p inverse-word bijection remains a paper theorem with exact regressions rather than a Lean-certified universal theorem. Keep this under intermediate results until adversarial source-level and academic-novelty review.

**Research implication.** The canonical dyadic word length is an exact graph-theoretic distance to the zero layer, so the first stage of the general all-modulus mixing construction is optimally short for some source residues. This is a structural representation theorem and proof-method tool; it does not establish reachability or nonhalting from the authentic integer 10.