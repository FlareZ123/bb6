# Sheep first-even mixing: sharp quotient and coherent diameters for all even moduli

**Current strongest mathematical claims (7 November 2026).** For each dyadic modulus `2^p`, **every finite directed walk** of the generic Sheep first-even quotient graph has a literal realization as consecutive genuine generic section returns from a single, arbitrarily large, freely chosen positive integer. The construction gives an explicit arithmetic progression of witnesses with positive density; it also gives the **complete all-pairs dyadic distance metric** for both synthetic and coherent free-start paths, exact-k congruence cylinders, and the exact vertex eccentricity census `2*binomial(p-1,2e-1)`. See the [universal finite-path theorem](../agent40-sheep-dyadic-metric/FINITE-PATH-LIFTING.md), [metric synthesis](../agent40-sheep-dyadic-metric/README.md), and independent exhaustive regressions. These all-p results are **written mathematical proofs**, based on Agent22's earlier all-parameter inverse-word theorem, with no complete source-importing Lean certificate or established external academic novelty.

For **every even modulus** `m=2^p*q` (p>=1, odd q), the earlier result remains: both the generic and unrestricted legal Sheep first-even **synthetic** residue graphs have exact diameter `floor(p/2)` for q=1 and `floor(p/2)+1` for q>1. The same formula holds for freely chosen **coherent** positive-integer orbits, with generic or all legal nonhalting branches. The pure-dyadic proof uses inverse-word saturation; the mixed lower bound uses a forced `-2` affine corridor. The detailed all-parameter argument, actual-residue witnesses, exceptional branch audit, and limits are in [MIXED-EXACT-DIAMETER.md](MIXED-EXACT-DIAMETER.md) and [DYADIC-DIAMETER.md](DYADIC-DIAMETER.md). The mixed upper premise and new lower bounds remain paper proofs, while selected algebra is locally Lean checked.

**Authentic-root boundary:** All constructed trajectories may start from an integer chosen to fit their target. The original six-state Sheep machine's blank even section starts at **the fixed integer 10**. No theorem here proves that its unique orbit reaches or avoids all powers of two. Sheep and BB(6) remain unresolved; no step bound has changed.

## Established related results and source-boundaries

- [Universal finite-path lifting, exact dyadic synthetic/coherent metrics and eccentricity census](../agent40-sheep-dyadic-metric/README.md): every finite generic quotient walk has infinitely many arbitrarily large *single-orbit* positive starts; every exact-k endpoint set is a single canonical-word suffix cylinder, yielding the exact free-start as well as synthetic distance; each vertex's eccentricity is its canonical length j or j+1 according to total code cost, and eccentricity e occurs for exactly `2*binomial(p-1,2e-1)` source vertices. Full all-p proof is **paper mathematics** relying on Agent22's inverse-word bijection; [independent verifier](../agent40-sheep-dyadic-metric/verify_eccentricity.py) checks every vertex up to p=11 and all 1,535 exact-k cylinder cases through p=9; [single-orbit verifier](../agent40-sheep-dyadic-metric/verify_coherent.py) tests 21,590 exact consecutive trajectories through p=8, and [universal path verifier](../agent40-sheep-dyadic-metric/verify_paths.py) checks 16,200 randomly sampled full paths of length 1..12 through p=9. [All-path proof](../agent40-sheep-dyadic-metric/FINITE-PATH-LIFTING.md). Constructed starts remain freely chosen; no fixed-10 blank-root result.
- [Sharp every-even-modulus generic, unrestricted and coherent diameter](./MIXED-EXACT-DIAMETER.md): exact `floor(p/2)` for `q=1`, exact `floor(p/2)+1` for every odd `q>1`; new forced `-2` congruence corridor and explicit source/target lower witnesses. [Finite full-graph verifier](mixed_diameter_certificate.py) exhaustively checks 51 small moduli using a proven h-period cutoff.
- [Exact all-precision generic and coherent dyadic diameter](./DYADIC-DIAMETER.md): `diameter(G_p)=floor(p/2)`, with the same sharp maximum number of consecutive generic returns from a freely chosen physical integer for any pair of even residues. New target-saturation proof and exact-integer witness construction; only the affine saturation sublemma has a local Lean kernel check. [Finite historical census](DIAMETER-FINITE.md).
- [Alternative all-even-modulus CRT proof](./ALTERNATIVE-MIXED-LIFT.md) and [standalone mixed-edge verifier](./mixed_independent.py): independent ascending-prime-factor proof of generic mixed residue graph strong connectivity for every m=2^p q with q odd. Verified 67,360 CRT-lifted edges and 159,138 dyadic-zero outgoing edges, including composite odd moduli. Agent22 independently obtained the same result via a distinct order-descent argument.
- [Exact dyadic shortest-distance theorem](./DYADIC-DISTANCE.md) and [exhaustive distance verifier](./distance_independent.py): proves for all p that shortest generic quotient distance from even residue r to zero modulo 2^p equals its canonical inverse-word length. Exactly binomial(p,2j) residues have minimum distance j. Independent exact checks covered 32,767 vertices and 3,014,654 algebraic reverse edges for p<=15.
- [No univariate Presburger invariant](./NO-PRESBURGER-INVARIANT.md): any infinite, ultimately periodic set of even section states that is closed under every legal generic true first-even successor is eventually all even. This follows already from the synthetic mixed quotient with arbitrarily large witnesses and excludes a one-variable Presburger-definable power-avoiding globally inductive invariant containing authentic start 10.

The all-parameter inverse-word and complete coherent-diameter derivations remain written mathematical arguments requiring independent end-to-end source/kernel verification and external novelty review; the saturation algebra is separately Lean checked. None classifies the authentic Sheep orbit or determines BB(6).

## Precise results and original-machine semantic boundary

**New matching mixed lower bound:** For every odd `q>1`, a concrete even source residue `r≡-2 mod2^p` and target `s≡0 mod2^p` cannot be connected in at most `floor(p/2)` generic quotient steps. For odd `p`, the first `floor(p/2)` returns are forced to be the `a=1,h=0` affine branch and their final odd coordinate is fixed. For even `p`, the last first-even block has variable odd-run length `h`, but choosing the source's odd coordinate and the target excludes all possible final residues; an elementary split on `5|q` proves it. Since coherent paths project into this graph, the same lower bound is valid for any single positive-integer trajectory. The earlier Agent22 all-modulus upper constructions therefore attain exact sharp diameter.

**Sharp pure-dyadic result:** For every `p>=1`, any even `r,s mod 2^p`, and any `N`, some even physical starting section state `x>=N` with `x≡r (mod 2^p)` follows **at most `floor(p/2)` consecutive legal generic first-even returns** to a value congruent to `s`. The matching lower bound follows from the exact shortest-to-zero code-length theorem. The full proof and the separate finite witnessed-return check are in [DYADIC-DIAMETER.md](DYADIC-DIAMETER.md).

**General mixed-modulus result (previously audited):** For every modulus m=2^p q (p>=1, q>=1 odd), every two even residues r,s modulo m and every bound N, there is a freely chosen even positive integer x>=N with x=r modulo m such that the actual consecutive generic Sheep first-even returns from x hit s modulo m after at most floor(p/2)+1 returns. **All transitions belong to the same single integer orbit.** The authentic blank-tape entry is the one fixed integer 10; the constructed x is permitted to depend on the target and modulus.

The authentic generic Sheep section formula, for x=2^a*u with a>=1, u>=5 odd, is F(x)=x+a+(u-1)/2. Given F(x)-1=2^h*v with v>=5 odd, the genuine next-even return is E(x)=1+3^h*v. These exact nonhalting branch equations were previously connected to the original six-state source in Agent16's EvenSourceBridge.lean. Its source CI 41505950547 proved the original machine halts iff the true even orbit starting at 10 reaches 2^j for some j>=2; this reduction alone decides no halting status.

## Corrected affine identity

The exact generic formula is

  E(x) = [alpha*x + beta]/2^(a+h+1),
  alpha = 3^h * (1+2^(a+1)),
  beta = 2^a * [2^(h+1)+3^h*(2a-3)].

The older displayed beta in Agent22's first coherent document was wrong for h>0. The Critic found a=1,u=9,x=18,F=23,h=1,v=11, which gives E=34, while that obsolete displayed expression gave 36. The corrected expression gives 34. I independently checked cases (a,u,h,E)=(1,5,2,28),(2,7,5,244),(3,9,1,118). The odd affine slope alpha/2^(a+h+1) was unchanged by correction. The currently fetched COHERENT-ORBIT.md uses the correct beta.

## Detailed proof check

Let W=((a_i,h_i)) be the canonical inverse word of source dyadic residue r modulo 2^p from [Agent22's dyadic theorem](../agent22-sheep-mixed-hub/DYADIC-COMPLETENESS.md). Its cost C=sum_i(a_i+h_i+1)<=p and its length j<=floor(p/2). Put P=p+C, lift the same inverse word to precision P and choose a sufficiently large positive x0 by CRT:

  x0=Phi_P(W) (mod 2^P),  x0=r (mod q).

The inverse equation for a letter of cost c=a+h+1 loses c bits of dyadic precision. At every step at least p+remaining_word_cost>=1 bits survive. Since the inverse target is even, those retained bits force (F-1)/2^h odd and hence the exact required h. The valuation a is forced by the source residue. Induction guarantees all j prescribed generic branches occur in **one real trajectory**, and y0=E^j(x0) is 0 modulo 2^p. Choosing x0 sufficiently large guarantees all the finitely many odd cofactor guards u,v>=5.

Composition of the corrected affine formulas gives odd slope numerator

  alpha=product_i [3^h_i*(1+2^(a_i+1))].

For L=2^P*q, every x0+L*t preserves the entire itinerary and has final state

  E^j(x0+L*t)=y0+alpha*2^p*q*t.

Its odd q-component rho=y0 mod q is constant. By the established all-odd arithmetic solvability lemma, there exists a>=p with

  (2+2^(-a))*rho+2*a-1-2*s=0 (mod q).

The desired penultimate state y has exact valuation a and odd part

  u=1+2*(s-a) (mod 2^(p+1)).

The necessary modular equation for t is

  alpha*q*t = [2^a*(1+2*(s-a))-y0]/2^p (mod 2^(a+1)).

Its right side is integral because y0 is dyadically zero. Its left coefficient alpha*q is odd, hence invertible modulo 2^(a+1). An appropriate t and then any sufficiently large positive period-preserving lift force y=2^a*u with u>=5 odd. The last generic return F(y) is even, so E(y)=F(y), and it equals s modulo both 2^p and q by construction. The total number of real returns is j+1<=floor(p/2)+1.

I found no further algebraic inconsistency in the corrected proof. The all-p inverse-word theorem, the all-odd arithmetic lemma and this final coherent composition still require independent full-parameter kernel certification and assessment of novelty. This review confirms the written mathematical implication conditional on those established paper premises, without asserting a fresh Lean source proof.

## Additional exact corollary: an arithmetic progression of successful starts

The final t is fixed modulo 2^(a+1). Therefore all sufficiently large integers in a **whole arithmetic progression**

  x=x_star+2^(p+C+a+1)*q*n,  n>=0

follow the same actual finite generic itinerary and arrive at the target residue after the bounded number of returns. Their asymptotic density among all positive integers is at least 1/[2^(p+C+a+1)*q], and their conditional lower density inside the original residue class x=r (mod m) is at least 2^(-(C+a+1)). This strengthens the paper's arbitrarily-large-start assertion. It leaves the exact blank start 10 completely uncontrolled.

## Reproducible independent tests

The [mixed_diameter_certificate.py](mixed_diameter_certificate.py) enumerates all edges with a justified finite odd-block period cutoff, then performs all-source BFS for **51 complete finite mixed/dyadic quotient graphs**, 4,472 cumulative vertices. Its concrete lower witnesses match the exact formula throughout the tested set. The new standalone [coherent_diameter_certificate.py](coherent_diameter_certificate.py) passed **324,039** maximal-word actual-single-orbit source/target checks through `p=15`, plus **84,366** shorter-word actual-single-orbit checks through `p=9`. It verifies exact prescribed valuation pairs `(a,h)`, positive generic guards, and each final target. The separate [diameter_certificate.py](diameter_certificate.py) checks all maximal-word inverse-target saturations through `p=15`. Both are finite regressions for the new all-parameter proof.

The standalone [coherent_independent.py](./coherent_independent.py) imports no Agent22 code and uses only Python 3's standard library. It independently implements the inverse-word decoder, inverse modular map, an **alternative ascending-prime** lifting of odd target exponents (rather than Agent22's gcd/order descent), CRT source construction, consecutive literal E transitions, affine-slope check, and final dyadic tuning.

Fresh local execution passed **15,942 complete single-integer generic first-even trajectories** for p=1..9 and q in {1,3,5,7,9,11,15,21,25,27,35,45,63,75,81,99,105,143,165,255,315}. It checked every prescribed (a,h) branch pair, every actual integer successor, exact target residue, length bound and shifted-orbit slope. The maximal starting-state width was 45,395 bits and the longest path used five consecutive returns. These are finite exact tests, not proofs of all quantified cases. The original Turing machine's primitive steps were not replayed for huge x; source alignment relies on prior audited original-source Lean equivalence.

## Scientific limit

The coherent theorem is about freely chosen, large, generic section starting states. Its entire arithmetic progression of suitable starts may omit the authentic blank entry 10. Therefore it neither proves a Sheep halt/nonhalt nor improves the BB(6) upper bound. It establishes a strong methodological warning: a proper fixed finite-modulus invariant that must apply uniformly to every sufficiently large congruent legal state cannot separate all possible targets. A viable proof for the exact blank-origin orbit will need genuinely seed-sensitive, history-sensitive, or other unbounded structure. Preserve this review under intermediate results until independent mathematical and external-prior-art assessment.
