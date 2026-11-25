# Growing gaps after small positive entries

**Status:** mathematical proof using an explicit classical linear-forms-in-logarithms theorem; the integer composition and congruence lemmas are separately formalized. This is an infinite exclusion on signed-return paths, not a decision of any blank machine.

Write P(k)=5·2^k. The existing signed macro gives the relaxed positive orbit

    q_(j+1)+10·2^(k+j) = 3^a_j q_j + 3,
    a_j = positiveCount(k+j,q_j)+1 ≥ 1.

The relaxed orbit is always positive and bounded above by 2P(k+j)-2, even when its next coordinate would fail the real gate. A real ordinary return occurs when q_(j+1) ≥ k+j+7. A failed gate initiates a negative excursion; the signed macro either halts or returns at band K with q ≤ 3K+12. Indeed the special return from negative band b has K=b+1 and q=3b+15; the skip return has K=b+2, q=(3v+3)/2, v≤2b+7. Both obey that bound.

## Exact short obstruction

Suppose two successive relaxed exits have

    3^a q+3=10·2^k+p,
    3^b p+3=20·2^k+r.

If the first gate passes and the second fails, then p≥k+7 and 2≤r≤k+7. Subtract twice the first identity from the second. If both 3^a and 3^b exceeded 2p+3, the two residues r+6 and 2p+3 would be below their common power-of-three divisor and congruent; hence r=2p-3, contrary to the inequalities. Consequently

    3^a ≤ 2p+3  or  3^b ≤ 2p+3,
    2·2^k ≤ qp  or  4·2^k ≤ p².

The product conclusion follows from 2p+3≤5p and the exact equations. This is an all-time exclusion of two simultaneously small successive positive coordinates before a failed gate. See CapExitRigidityCore.lean and CapExitGap.lean.

## Growing reset-to-exception separation

**Theorem.** Let k≥16 and start at any valid positive entry q_0≤3k+12. Put L=ln k, H=10^14 L. For any positive integer t satisfying

    4 L H^t ≤ k,

the first t relaxed exits are real ordinary returns, and each 1≤j≤t satisfies

    q_j > 10·2^(k/2).

Thus every successful negative excursion at sufficiently high band K is followed by a run of ordinary returns of length at least

    floor(ln(K/(4 ln K)) / ln(10^14 ln K)),

whenever this quantity is positive. In particular, the minimum separation grows on the order of ln K / ln ln K, uniformly over all reset coordinates. No statistical assumption about the actual roots is involved.

### Proof

For a prefix of length j, define A_0=C_0=D_0=0 and

    A_(j+1)=A_j+a_j,
    C_(j+1)=3^a_j C_j+2^j,
    D_(j+1)=3^a_j D_j+1.

Induction gives the exact expansion

    3^A_j q_0 +3D_j = q_j+10·2^k C_j.

For j≥1 let S_j=A_j-a_0. We have 1≤D_j≤C_j<2^j 3^S_j. Also C_j ≡ 2^(j-1) (mod 3), whereas 3^A_j q_0 is divisible by 3. Therefore the real rational number

    Λ_j = 3^A_j 2^(-k) · q_0/(10 C_j) - 1

is nonzero. These algebraic facts are proved in CapExitWordCore.lean.

Use the explicit real version of Matveev's theorem as stated in Bugeaud, Mignotte and Siksek, *Classical and modular approaches to exponential Diophantine equations I. Fibonacci and Lucas perfect powers*, Annals of Mathematics 163 (2006), Theorem 9.4, p. 989:
https://annals.math.princeton.edu/wp-content/uploads/annals-v163-n3-p05.pdf

For positive rational factors γ_1,γ_2,γ_3, exponents bounded in absolute value by B, and Λ=∏γ_i^b_i-1 nonzero, it gives

    ln |Λ| > -1.4·30^6·3^4.5·(1+ln B)·A_1 A_2 A_3,

where A_i ≥ max(h(γ_i), |ln γ_i|, 0.16), with rational logarithmic height h(u/v)=ln max(|u|,|v|) after reduction. If γ_3=1, apply the two-factor version, which is stronger than the bound used below.

Take γ_1=3, γ_2=2, γ_3=q_0/(10C_j), exponents A_j,-k,1. The positive-window upper bound gives 3^a_i q_i≤30·2^(k+i), so a_i≤k+i+4. The assumed inequality on t implies t≤L≤k. For j≤t, A_j≤3k² and B≤3k², hence 1+ln B≤4L. Since q_0≤4k, the bound on C_j gives an admissible A_3=5L+j+2S_j. Set A_1=ln3, A_2=ln2. The numerical coefficient 1.4·30^6·3^4.5·ln3·ln2 is less than 2.5·10^11 (even using ln3<1.1, ln2<0.7, 3^4.5<141). Thus

    |Λ_j| > exp(-R_j),
    R_j=10^12 L(5L+j+2S_j).

Prove S_j≤L H^(j-1) by induction, starting with S_1=0. At any j≤t for which this bound holds, j≤L and H≥1 imply

    R_j ≤ 8·10^12 L² H^(j-1)
        ≤ L H^j ≤ k/4 < (k/2) ln 2.

From the exact expansion,

    |q_j-3D_j| = 10·2^k C_j |Λ_j|
                >10·2^(k/2) C_j.

The sign must be positive, because q_j>0 and 3D_j≤3C_j. In particular q_j>10·2^(k/2)≥k+j+6 (strictly above the gate threshold for k≥16 and j≤k). The real signed macro therefore follows the relaxed orbit up to j.

For the inductive bound on the next exponent, retain the stronger estimate q_j>10·2^k C_j exp(-R_j). The positive-window upper bound gives

    3^a_j q_j≤30·2^(k+j),
    a_j ln3 < ln3+j ln2+R_j,
    a_j < 1+j+R_j.

Hence

    S_(j+1) = S_j+a_j
      < L H^(j-1)+1+j+8·10^12 L² H^(j-1)
      ≤ (3+8·10^12 L) L H^(j-1)
      < L H^j.

This proves the induction and all claimed gate inequalities. The order estimate follows by taking logarithms of 4LH^t≤k.

### Significance and limit

This is an unconditional, non-periodic restriction on all high-band exceptional paths. It is qualitatively different from a fixed congruence sieve: the excluded return gap tends to infinity. It eliminates every fixed-length reset-to-exception pattern at sufficiently large band. It does not exclude an exception after a growing number of ordinary returns, nor does it prove that the three blank-root paths avoid all terminal indices. The explicit constants are intentionally loose. The analytic inequality is a written proof using Matveev, not a Lean theorem. The integer source transport and expansion are checked separately.
