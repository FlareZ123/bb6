# No regular binary invariant for Sheep's accelerated even section

**Agent 16, 24 November 2026.** The [raw-return no-go theorem](NO-REGULAR-INVARIANT.md) does not immediately exclude a language defined only at even returns, because the intervening odd-run length may be unbounded. The following argument closes this loophole. No nonempty regular language of canonical binary even integers >=6 can be terminal-free and forward closed under the exact first-even section map E. In particular this class cannot certify the authentic entry 10. The proof is mathematical prose with the exact singular-pumping arithmetic checked in Lean.

## 1. Bound the even source valuation

Suppose I is a nonempty regular language of even integers >=6, disjoint from powers of two and closed under E. Every accepted state has a genuine next even state, strictly larger. Hence I is infinite. Let t be the initial zero-transition transient of a DFA recognizing I; choose a common period p for the zero action on all its states and global threshold T beyond all zero transients.

Suppose x=2^a u belongs to I with a>=t, odd u>=3. Pump the leading LSB zeroes to obtain x_e=2^e u in I for every sufficiently large e=a mod p. Write c=3 if u=3, and c=(u-1)/2 otherwise. The first raw successor is x_e+e+c. Choose one sufficiently large e0 in the progression with e0+c-1>0 and put h=v2(e0+c-1). Restrict e to e0 modulo P=lcm(p,2^(h+1)), with e>h. Then the exact odd-run length is h since
```
F(x_e)-1=2^e*u+(e+c-1)
```
has valuation h. The accelerated output is therefore
```
E(x_e)=U*2^(e-h)+delta_e,
U=3^h*u, delta_e=1+3^h*(e+c-1)/2^h.
```
The positive even integers delta_e run through a fixed arithmetic progression of step d=3^h*P/2^h, an even integer. For all sufficiently large e, delta_e has bit length ell_e much less than e-h. The accepted output word consists of the canonical low block for delta_e, then e-h-ell_e zeros, then the fixed high block for U. By zero-gap pumping, I also accepts U*2^b+delta_e whenever b=e0-h mod p, b-ell_e>=T, and e-h-ell_e>=T.

Choose L=lcm(p,ord_{d_odd}(2)), with order 1 for odd part d_odd=1. Restrict b to e0-h mod L and take it sufficiently large. Then U*2^b mod d is constant. Fix 0<alpha<beta<2^(-T-1). For every sufficiently large such b, and every delta in the progression of delta_e satisfying alpha*2^b<delta<beta*2^b, the gap inequalities hold: its e grows linearly with delta and its bit length only logarithmically. Thus I contains all sufficiently large even integers in one residue class modulo d and the open log2 phase interval
```
(e0-h+log2(U+alpha), e0-h+log2(U+beta)) mod L.
```
One may take an interior subinterval to avoid a circle boundary. The interval has length less than one, and for each sufficiently large integer in the cell there is a corresponding b in the selected progression and a delta with the required congruence. The [prepared terminal density theorem](../agent17-sheep-terminal-extension/README.md) gives actual even prepared starts in every such cell which eventually reach a power of two. This contradicts E closure and terminal exclusion.

Therefore a<t for every member of I. If t<=1 this is immediately impossible (all a>=1). Otherwise write A=t-1. The argument treats the special u=3 branch as well as generic starts.

## 2. Full binary growth is impossible even without a bound on odd-run lengths

For each x in I, its entire genuine raw trajectory is infinite, because its E trajectory is infinite and each intervening odd block is finite. Its even raw states have valuations <=A; the odd intervening states have valuation zero. For sufficiently large x all raw states exceed 3*2^A and are generic. Hence the same bounded-valuation cylinder estimate from [GROWTH.md, section 5](GROWTH.md) applies to I itself:
```
#I_n <= (A+1)*lambda_A^(n+A)
```
for large n, where lambda_A<2. This uses the actual raw trajectory between successive E states; it does not assume those odd states belong to I.

In particular, the set of limiting logarithmic phases of arbitrarily large I members cannot be the whole circle. If it were, all m-bit leading patterns would occur in accepted words and the low prefixes could be shortened to length <=|Q|-1 using the DFA, as proved in [NO-REGULAR-INVARIANT.md, section 1](NO-REGULAR-INVARIANT.md). That would force full rate 2.

## 3. Singular odd-run lengths are impossible

Write the generic raw affine formula as
```
F_a(x)=r_a*x+a-1/2,
r_a=(2^(a+1)+1)/2^(a+1).
```
On the even branch v2(x)=a, let h(x)=v2(F_a(x)-1). Suppose these h(x) are unbounded among sufficiently large x in I. Pass to one fixed a (there are finitely many). There is then a sequence of accepted integers tending to infinity with h(x) tending to infinity. The corresponding integers converge 2-adically to the rational singular point
```
z_a=(3/2-a)/r_a = 2^a*(3-2*a)/(2^(a+1)+1).
```
Indeed F_a(x)-1=r_a*(x-z_a), with v2(r_a)=-(a+1), so v2(x-z_a)=h(x)+a+1. The rational z_a has odd denominator and valuation a. Every finite low prefix of its binary expansion therefore has arbitrarily long canonical accepted continuations.

The 2-adic binary digit expansion of a rational with odd denominator is eventually periodic. For completeness, write z=s/D with s an integer and D>0 odd, and let v_k be the integer in [0,2^k) congruent to z modulo 2^k. The residual rational numerator s_k=(s-D*v_k)/2^k is an integer bounded in absolute value for large k. The next bit is s_k mod 2, and s_(k+1)=(s_k-D*(s_k mod 2))/2. This finite-state recurrence gives eventual periodicity, including negative z.

Let q_k be the DFA state after the first k low bits of z_a. By combining the eventual digit period and the finite DFA states, choose k0 and a positive d such that along k=k0+jd both q_k and the infinite remaining digit tail repeat exactly. Choose a fixed nonempty canonical word w accepted from q_k0; such a word exists because arbitrarily long accepted continuations exist. Appending w to each low prefix gives actual members
```
x_k=v_k+2^k*v(w), k=k0+jd.
```
Let V be the numeric value of the repeated d-bit tail block. Its 2-adic sum is V/(1-2^d), hence v_k=z_a+2^k*V/(2^d-1). Thus for all these k
```
x_k=z_a+2^k*B,
B=v(w)+V/(2^d-1)>0,
F_a(x_k)-1=2^k*r_a*B.
```
For large k the valuation of x_k is a, the cofactor is >=5, and the first successor is a positive integer. Set b=v2(r_a*B), an integer independent of k. Then h(x_k)=k+b and the odd part v=(r_a*B)/2^b is a fixed positive odd **integer**: for any one sufficiently large k the right-hand side is the integer odd part of F_a(x_k)-1. The genuine accelerated outputs are
```
E(x_k)=1+3^(k+b)*v.
```
These belong to I and tend to infinity. Their logarithmic phases are dense modulo 1 because
```
log2(E(x_k)) = (k0+jd+b)*log2(3)+log2(v)+o(1)
```
and d*log2(3) is irrational. Thus the set of limiting phases of I is the full circle, contradicting section 2.

This proves that h(x) is bounded on all sufficiently large members of I. No assumption about the authentic orbit's valuations or odd-run lengths has been made.

### Exact discrete singular-pumping identity

For successive k separated by d, the displayed affine family implies
```
N*x' + 2^(a+1)*a + 2^d*(3*2^a)
 = 2^d*(N*x + 2^(a+1)*a) + 3*2^a,
N=2^(a+1)+1.
```
In [EvenPhasePump.lean](EvenPhasePump.lean), successor_shift proves that the genuine raw successors y,y' satisfy y'+2^d=2^d*y+1. The theorem odd_phase_pump proves that when y=1+2^h*v with v odd, the exact raw section paths from x and x' have respectively h+1 and h+d+1 steps and arrive at the even values 1+3^h*v and 1+3^d*(3^h*v). It imports the actual SheepEven relation via RawCylinder. Both declarations compiled locally under Lean 4.36.0-rc2, with precisely [propext, Quot.sound]; SHA256 8700b8307b5a6fa8a0fcf30705e8a555ddd48bd3eb63ff82ee4083dfca1be353. The rational digit-period and logarithmic density argument is a paper proof.

## 4. Apply the finite phase-fibre theorem

Now all sufficiently large I members have a bounded by A and h bounded by some H. The branch domains are clopen 2-adic conditions v2(x)=a and v2(F_a(x)-1)=h, so there are only finitely many. On each branch the exact first-even map is
```
E_(a,h)(x)=1+(3/2)^h*(F_a(x)-1).
```
This is affine with positive slope 3^h*(2^(a+1)+1)/2^(a+h+1). Every nonempty finite product of slopes has odd numerator >1 and a power-of-two denominator, hence irrational base-2 logarithm. All hypotheses of the finite phase-fibre rotation principle in [NO-REGULAR-INVARIANT.md, section 2](NO-REGULAR-INVARIANT.md) are satisfied. It forces I to have full binary growth, contradicting section 2.

**Theorem.** There is no nonempty regular binary language of even integers >=6 that is forward closed under E and excludes powers of two. In particular no such certificate can contain the actual even root 10. The equivalent raw-return and even-return formulations are both excluded.

## Scope and dependencies

The prepared-state density theorem is the existing paper-level result of Agent17, not a Lean theorem; the full proof here is also paper-level. The exact raw path identity and bounded-valuation congruence have independent local kernel proofs, and the original machine-to-even-section reduction was previously source-certified (CI 41505950547). The theorem is a certificate-method obstruction: it does not prove nonhalting or halting, show that the true orbit has unbounded valuations, or give a new BB(6) bound. External novelty and independent review are pending. The singular-pumping argument is relevant specifically when an accelerated return can have an arbitrarily long intervening branch sequence; treating the even map as a finite-branch map without it would have a gap.
