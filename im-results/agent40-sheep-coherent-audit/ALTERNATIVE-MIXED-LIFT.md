# Independent all-even-modulus Sheep quotient proof by ascending prime factors

Agent 40, R010, November 3, 2026. Independent derivation of the same **generic synthetic quotient graph** theorem separately discovered by Agent22 in MIXED-COMPLETENESS.md. This is a mathematically written, independently tested alternative. It does **not** certify a true blank-origin Sheep orbit or a BB(6) result.

**Statement.** For each p>=1 and each positive odd q, let m=2^p*q. Vertices are even residues modm; an edge is witnessed by some legal positive generic first-even Sheep section input x=2^a u, with u>=5 odd, a>=1 and E(x)=1+3^h v where F(x)=x+a+(u-1)/2=1+2^h v, v>=5 odd. Every vertex has a directed path of length <=floor(p/2) to the set of residues divisible by 2^p, and each vertex in that set has a direct edge to every even target. Hence the quotient is strongly connected with diameter <=floor(p/2)+1.

**CRT lift for each dyadic edge.** Agent22's canonical reverse word gives paths modulo2^p with edges described by parameters 1<=a<p, 0<=h<p-a. Put D=1+2^(a+1). Choose v by CRT such that

  v=(s2-1)*3^(-h) (mod 2^p),
  2^(h+1)*v=2a-3 (mod D).

Set u=(3-2a+2^(h+1)*v)/D and x=2^a*u. The two moduli are coprime because D odd. Increasing v by 2^p*D*t shifts x by 2^(p+a+h+1)*t, which is a *unit* multiple of t modulo any odd q. Consequently any prescribed source odd-coordinate rq can be realized while preserving dyadic source and target. Use a nonnegative q-period lift of t to guarantee u,v>=5. Follow the canonical dyadic path, prescribing the current odd coordinate at each synthetic edge. In <=floor(p/2) edges the quotient reaches some dyadic-zero vertex.

**Every dyadic-zero class is an outgoing one-step hub.** Fix its odd coordinate r moduloq and any even target s2 mod2^p with odd target sq modq. We need a>=p with

  r+a+(r*2^(-a)-1)/2 = sq (mod q).

Here is one independent constructive proof for **every odd q**. Factor q into strictly increasing odd prime powers ell^k. Start with a=0 and Q=1. After satisfying the congruence modulo the product Q of previous prime powers, let B=Q*phi(Q)*(ell-1), where phi is Euler's totient and phi(1)=1. Every prime factor of Q*phi(Q) is smaller than the new ell, so ell does not divide B. By Fermat, 2^B=1 modell; by Euler and Q|B, the replacement a->a+B*t preserves the previously established congruence modulo Q.

On the new ell^k, the function

  g(t)=r+a+B*t+(r*2^(-a)*(2^(-B))^t-1)/2 (mod ell^k)

is a permutation. Indeed, if v_ell(t'-t)=j<k, then B(t'-t) has exact ell-adic valuation j, while the exponential correction is divisible by ell^(j+1), because 2^(-B)=1 modell and binomial lifting makes (2^(-B))^(t'-t)=1 modell^(j+1). Therefore g(t')-g(t) has exact valuation j; g is injective and hence bijective on ell^k residues. Choose t to solve the target congruence modulo ell^k. Iterate over all prime factors. Finally increase a by q*phi(q), a period of the whole congruence, until a>=p.

Choose u by CRT:

  u = r*2^(-a) (mod q),
  u = 2*s2-2*a+1 (mod 2^(p+1)).

The second residue is odd; adding sufficiently large multiples of q*2^(p+1) makes u>=5. Set x=2^a*u. Then x is 0 mod2^p and r modq. Its exact generic first successor F=x+a+(u-1)/2 is even and equals s2 mod2^p and sq modq, by construction. Therefore its genuine first-even E equals F and lands at any prescribed target s. Combining the lifted path with this final hub proves the diameter theorem.

**Reuse of earlier work.** Agent17's already written ALL-ODD-MODULI.md proves a closely equivalent ascending-prime root lemma, so the above exponent argument is not claimed as new number theory. Agent22 independently found a distinct, shorter all-odd solution by strong induction on q and multiplicative orders, and independently established the full mixed quotient result. The added value here is independent derivation and an alternative source-prescribed CRT construction, not a claim of original discovery.

**Independent reproducibility.** mixed_independent.py constructs exact generic positive witnesses by separate ascending-prime arithmetic and dyadic CRT inverses. It passed 67,360 genuine lifted edges and 159,138 exact zero-layer outgoing edges for p=1..6 and 22 odd cofactors up to105, including composite 15,21,33,35,45,55,63,65,75,99,105. Every source and target congruence and literal E arithmetic is checked. Finite tests do not establish the universal theorem. Original-machine section equivalence depends on Agent16's source-certified EvenSourceBridge.lean, successful CI 41505950547. All-parameter mixed theorem has not yet been Lean-certified or externally novelty reviewed.

**Limitation.** This is a synthetic quotient with independently chosen representatives at each edge. Arbitrary paths through congruence classes cannot automatically be interpreted as a single authentic trajectory from the *exact* blank even-section entry 10. Agent22's separate COHERENT-ORBIT.md addresses freely chosen single starts, still without controlling 10. Keep this proof under intermediate results until peer review.