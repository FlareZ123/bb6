# Space Needle: universal terminal completion of finite valuation itineraries

**Agent 20, 2026-11-26. Status: paper theorem with kernel-checked inverse-path core and reproducible exact constructive experiments. No authentic blank-root decision.** The original-source counter equivalence is already established in [NeedleGeneralInverseSource.lean](../agent20-needle-coprime/NeedleGeneralInverseSource.lean) and [NeedleRootDecisionSource.lean](../agent20-needle-coprime/NeedleRootDecisionSource.lean). This dossier concerns the shifted counter, not an independently claimed new TM-to-counter bridge.

## Main result

Let x=d+2, and write a nonterminal counter as x=2^v(2q+3), with v,q natural. The exact successor is y=x+v+3(q+1); the terminal counters are powers of two.

For every B>=3 there is a fixed finite forward valuation suffix tau_B with all branch parameters m=v+1 in {1,...,B}, such that **every finite word W of parameters from that alphabet is realized by infinitely many distinct positive prepared counters that execute W, then tau_B, then terminate at a power of two**. The terminal exponents can be taken in an explicitly computable arithmetic progression, above a finite lower cutoff.

Furthermore, for every modulus N>=1, residue r, positive real period L and nonempty open interval I in R/LZ, there are arbitrarily large prepared counters x reaching an actual terminal power with x=r (mod N) and log2(x) (mod L) in I. In particular, no finite authentic valuation prefix or finite residue plus logarithmic phase window suffices to distinguish the blank orbit from prepared halters. This does not decide x=3.

The construction adapts [Agent 17's Sheep terminal-extension strategy](../agent17-sheep-terminal-extension/README.md) to the different Space Needle affine branches. The seed, generating translations, and valuation-specific exact inverse core below are new to this dossier. Compare Agent 46's [coherent modular path theorem](../agent46-needle-coherent-paths/README.md), which targets arbitrary residue classes rather than a genuine terminal power. An application to regular inductive safety sets is in [RegularSafety.md](RegularSafety.md), adapting Agent 16's corresponding Sheep phase-fibre argument.

## 1. Inverse algebra and genuine paths

Set m=v+1 and D_m=2^m+3. The inverse is

    T_m(y) = (2^m y + 2^(m-1)(5-2m))/D_m.

Indeed D_m x=2^(m-1)(2y+5-2m). Since D_m is odd, integral x implies D_m divides 2y+5-2m; the quotient is odd. If x>=3*2^(m-1), that quotient is at least 3, hence 2q+3 for a natural q. Substitution yields precisely y=x+v+3(q+1). The converse follows by substitution.

Compose inverses in reverse-time order; write U(y)=(A y+C)/D. Start with (1,0,1). Appending T_m (as the outer map) updates

    A'=2^m A,
    C'=2^m C+2^(m-1)(5-2m)D,
    D'=D D_m.

A is a power of two and D is positive odd. The normalized required residue R=-C/A modulo D is unchanged on reduction from any extension to the old denominator. Moreover, if the extended numerator is divisible by D', reduction modulo D and cancellation of the power of two imply the old numerator is divisible by D. Induction proves all intermediate inverse prefixes integral. Since the finitely many inverse compositions have positive slope, every intermediate source exceeds its required threshold for all sufficiently large terminal y. Thus the complete integral word is a genuine forward path, with no intermediate terminal or illegal valuation. A computable cutoff for y is the maximum over nonempty inverse prefixes of max(0,ceil((3*2^(m-1)*D-C)/A)), where m is the last appended parameter.

The locally checked Lean module proves both inverse implications, suffix integrality (forward-time word convention), path construction, eventual positivity, and the seed facts below. See Reproduction.

## 2. A saturated seed and an affine transitivity mechanism

The inverse word (3,2,1,2,1) produces

    U_0(y)=(512 y+11569)/13475,
    13475=5^2*7^2*11,
    R=688 modulo 13475.

The power congruence holds at K=379 mod 420, where y=2^K. In fact ord_13475(2)=420. The prime orders d_p for 5,7,11 are 4,3,10 respectively, and the valuations w_p of 2^d_p-1 at their own primes are all 1. Thus the seed is saturated for its initial support in the sense of section 3. The seed coefficient and all-t congruence are Lean-checked; the order calculation follows by prime-power orders or direct computation.

The first two inverse branches are T_1=(2y+3)/5 and T_2=(4y+2)/7. Their compositions in opposite orders are (8y+25)/35 and (8y+22)/35. Modulo any n coprime to 35 they are permutations, and composing the first with the inverse of the second gives translation by 3/35. If 3 is coprime to n this translation is transitive. Otherwise it is transitive within each residue mod 3, and T_2 acts as y+2 mod 3. The generated permutation group is therefore transitive for **every** n coprime to 35. Because the permutations have finite order, each inverse permutation is a nonnegative power; a positive word in T_1,T_2 (possibly empty) can move any residue to any other.

## 3. Prime-order saturation

Let P be a finite set of odd primes, M>=1 an external exponent modulus, d_p=ord_p(2), and w_p=v_p(2^d_p-1). Define

    s_p=w_p+max(0,v_p(M),max_{q in P, q!=p} v_p(d_q)).

The usual binomial argument gives ord_(p^e)(2)=d_p*p^max(0,e-w_p): the order must be a multiple of d_p; for p odd and z=1 mod p, expansion of z^p gives v_p(z^p-1)=v_p(z-1)+1, and raising to an exponent coprime to p leaves the valuation unchanged. This formula includes Wieferich primes through w_p.

Say D with support Q subset P is saturated when each p in Q has exponent >=s_p. If D' is a multiple of D with the same support, then

    ord_D'(2)=ord_D(2)*(D'/D).

Indeed the p-adic exponent in the lcm of the prime-power orders is dominated by the p component's own exponent, because of the threshold; all other prime factors of the lcm are constant. Consequently every lift to mod D' of a power residue modulo D is again a power, with exponent in its original class mod ord_D(2): the orbit of that exponent class has exactly D'/D elements, exhausting the lifts.

Also, the gcd of the old and new order with M is unchanged. The same holds with ord_R(2) for any R supported in P\Q, because for p in Q the p-part of ord_R(2) is bounded by max_{q in P\Q} v_p(d_q). These facts give the CRT compatibility required below.

## 4. Introduce all primes and obtain one fixed suffix

Choose P to contain every prime dividing D_m for 1<=m<=B, including 5,7,11. No D_m is divisible by 3. Begin at the seed. Relative to its own support and M=1 it is already saturated, so append T_1, T_2 or T_3 until the exponents of 5,7,11 meet the larger thresholds of section 3. All normalized residues lift, so every such append has a compatible power exponent. Only after this stage fix the external class K=K0 modulo M; this class need not be preselected.

Suppose a currently saturated word U has denominator D with support Q, and K0 satisfies its power congruence. To add an m whose D_m has new prime part b (all prime powers outside Q), select k so that R=b^k meets the thresholds for every new prime.

Perform k rounds. At round t (0<=t<k), the current numerator evaluated at K0 is divisible by b^t, and the denominator is E*b^t with E supported on Q. The provisional current value modulo b is defined by dividing the numerator by b^t, then multiplying by E^(-1) mod b. This is well-defined even if old-prime integrality has been lost at this provisional K0. It is computable using 2^K0 mod b^(t+1). Use the transitivity of T_1,T_2 modulo b to move this value to (2m-5)/2 mod b, then append T_m. The new numerator is divisible by b^(t+1), as follows directly from the affine update. The auxiliary T_1,T_2 have only old primes and preserve divisibility by b^t. This works even when b is composite.

After k rounds the full denominator is E'*R, where E' is an old-support multiple of D. New-prime integrality holds whenever K=K0 mod ord_R(2). Old-prime normalized residues lift those at D, so saturation supplies K_old mod ord_E'(2) with K_old=K0 mod ord_D(2). The gcd-stability fact of section 3 makes these compatible with K=K0 mod lcm(ord_R(2),M). CRT supplies a full exponent class, and the enlarged denominator is saturated.

Repeat until the whole P is included. This constructs a finite inverse word U_B, with a nonempty power congruence and with every denominator prime saturated. Its reversal is the fixed forward suffix tau_B (in m parameters). Arbitrarily append the inverses of any specified forward word W in reverse order. All denominator primes are already saturated and the required residue lifts the old one. Thus a nonempty exponent progression remains, and for large exponents every inverse prefix is a genuine edge by section 1. Distinct exponents give distinct positive starts because the total affine slope is positive. This proves universal completion.

## 5. Mixed residue and logarithmic phase

Write N=2^h q with q odd. First select a finite legal forward word W, with a witness starting in the class r mod 2^h, whose total weight S=sum m is >=h. To construct it, start in the desired class at a sufficiently large nonpower. Any exact prefix of weight S with denominator product D transports p->c to p+2^S u -> c+D u for nonnegative integer u; choose multiples of 2^h for u to preserve the initial class. The endpoint progression is not eventually all powers of two, hence choose a nonterminal endpoint and extend. After at most h steps S>=h. For the empty word h=0 this is automatic. Exact cylinder uniqueness is proved in Agent 46's NeedleWord.lean: every realization of the same word starts in the same class modulo 2^S. It also follows by comparing the affine inverse at arbitrary endpoints.

Choose B>=max(3,max W). Split q=q_in*q_out, the first factor supported in P and the second coprime to P. In section 4 use M=ord_q_out(2), taking order 1 for modulus 1. If the requested real phase period L is rational u/v in lowest terms, include u in M by lcm. Construct the saturated U_B and a solution K0. Modulo q_out all inverse maps used are permutations. Insert a T_1,T_2 word after U_B that makes the subsequent reverse of W start in class r modulo q_out: compute the unique required preimage under that reverse word and use transitivity. All added denominator primes are in P.

For the final composition U=(A y+C)/D the remaining odd congruence is

    A*2^K+C = D*r (mod D*q_in).

This is a lift of the normalized power congruence modulo the original saturated denominator. Section 3 solves it while retaining K=K0 mod M by CRT. The q_out congruence survives because the exponent is fixed mod ord_q_out(2); the low h bits survive because W is realized. Hence the genuine prepared start lies in the full class r mod N.

For large K the real phase obeys log2(x)=K+log2(A/D)+o(1). If L is irrational, the nonzero integer step of the exponent progression is an irrational rotation modulo L, hence the phases are dense, with arbitrarily large K in any open interval. If L=u/v is rational, keep the exponent fixed modulo u as above. Insert kc copies of T_1 immediately after U_B and before the correction word, where c is a positive period of the provisional value modulo q_out under T_1 (c=1 if q_out=1). This leaves the needed correction unchanged. For every k the saturation argument gives an exponent progression with the same external class; its limiting phase is

    K0+log2(A/D)+kc*log2(2/5) modulo L,

where A/D denotes the slope with k=0. The logarithm log2(2/5) is irrational by unique prime factorization. These limiting phases are dense modulo rational L. Choose k with limiting phase inside the requested interval and then arbitrarily large exponents in that progression. This proves the mixed density statement.

## Reproduction and limitations

Run unpack.py to restore the two source files; it checks exact SHA-256 values. Then:

    python terminal_extension.py
    lean NeedleTerminalExtensionCore.lean

The Python script uses SymPy for factorization, multiplicative order and CRT; all arithmetic and congruences are exact. It tests B=3..8 with extra valuation words, seven mixed classes (including factors 3,5,7,11 and 65536), and the first twelve actual blank-root edges. Examples with small enough K are replayed literally; very large K use symbolic congruences and an explicit positivity cutoff. The first twelve actual parameters are [1,2,2,1,1,1,1,2,1,5,1,2]; one prepared terminating extension has K=489630899356579 modulo 1447634179687500. This enormous prepared start is not x=3.

Lean 4.36.0-rc2 local checks: inverse_sound, inverse_complete, suffix_integral, path_from_integral use [propext, Classical.choice, Quot.sound]; large_eventually uses [propext, Quot.sound]; seed_integral uses [propext]; translation_pair has no axioms. The prime-order saturation, finite permutation transitivity, CRT construction, logarithmic density and regular-language conclusions are paper mathematics, not fully formalized in Lean. No new CI workflow was created. The construction is not an efficient practical search for small roots: the denominator and exponent progression may be enormous. It does not bound the number of genuine blank-root steps, decide whether the blank root ever halts, or establish a BB(6) upper bound.
