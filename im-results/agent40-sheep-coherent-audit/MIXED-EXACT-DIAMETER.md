# Exact Sheep first-even quotient and free-start coherent diameters for every even modulus

**Agent 40, 6 November 2026. Intermediate mathematical theorem.** For any \(p\ge1\) and odd \(q\ge1\), put \(m=2^p q\). Let \(G_m\) be the **generic synthetic first-even** Sheep residue graph, with even residues modulo \(m\) as vertices, and every edge witnessed by some positive legal generic Sheep first-even return. The *full* synthetic first-even graph \(H_m\) also includes every legal exceptional odd-part-three section return. **Both graphs** have the same exact directed diameter

\[
\boxed{\operatorname{diam}(G_{2^p q})=
\begin{cases}
\lfloor p/2\rfloor& q=1,\\
\lfloor p/2\rfloor+1& q>1.
\end{cases}}
\tag{1}
\]

The same formula holds for the maximum **coherent free-start directed distance**, whether every consecutive genuine first-even return is restricted to the generic branch or all legal nonhalting returns (including odd-part-three exceptions) are allowed. In each case the trajectory begins from **one suitably selected positive integer**. These are mathematical statements about arbitrarily chosen starting integers and independent synthetic edge witnesses. The actual Sheep blank-entry integer \(10\) is fixed and is not shown to realize any such route. **Sheep and BB(6) remain unresolved.**

The upper bounds are previous written all-parameter arithmetic theorems, with extensive exact checks: [Agent 22's inverse-word and mixed-CRT graph](../agent22-sheep-mixed-hub/MIXED-COMPLETENESS.md) proves \(\operatorname{diam}\le \lfloor p/2\rfloor+1\) for any odd \(q\), and [his coherent source theorem](../agent22-sheep-mixed-hub/COHERENT-ORBIT.md) proves the same bound for a **single freely chosen actual integer trajectory**. For \(q=1\), the stronger bound \(\lfloor p/2\rfloor\) and matching lower bound are [proved in the companion note](DYADIC-DIAMETER.md). The **new result here is a matching all-\(p\), all-odd-\(q>1\) lower bound**, established directly from residue forcing in the original section map. The prerequisite all-parameter upper constructions and the present lower proof have **not** been combined into a complete source-importing Lean certificate or independently externally reviewed for academic novelty. The key forced-corridor identity and the all-valuation modulo-five obstruction are separately verified in standalone [SheepCorridor.lean](SheepCorridor.lean), compiled locally with Lean 4.36.0-rc2 and only standard axioms.

## Exact section semantics

The source-certified machine-level halting reduction and published formula for the Sheep machine are recorded by [Agent 16](../agent16-sheep-even-return/README.md); original-source CI [41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547). For a generic first-even section return, \(x=2^a u\), \(a\ge1\), \(u\ge5\) odd, the first section return is
\[
F(x)=x+a+(u-1)/2.
\]
Writing \(F(x)-1=2^h v\), where \(v\ge5\) odd for the generic intervening branch, the first even return is
\[
E(x)=1+3^h v=1+(3/2)^h(F(x)-1),
\]
with the latter expression an **integer** even though written rationally. These equations are genuine source-connected returns; for modular arithmetic \(q\) odd, \(2^{-1}\bmod q\) exists.

## The forced \(-2\) corridor

**Lemma 1 (fixed two-bit contraction).** If \(x\) is a legal positive generic even-section source and \(2^b\mid x+2\) for \(b\ge3\), then its first-even return is *already the first section return* (\(h=0\), \(E(x)=F(x)\)), and
\[
4(E(x)+2)=5(x+2).
\tag{2}
\]
In particular, \(2^{b-2}\mid E(x)+2\), and modulo any odd \(q\),
\[
E(x)\equiv f_q(x)\pmod q,\qquad
f_q(z):=4^{-1}(5z+2)\pmod q.
\tag{3}
\]

**Proof.** From \(8\mid x+2\) we have \(x=8w+6=2(4w+3)\) for a natural \(w\), hence the exact 2-adic valuation of \(x\) is \(a=1\). With odd part \(u=4w+3\), the generic formula yields
\[
F(x)=2u+1+(u-1)/2=(5u+1)/2=10w+8,
\]
which is even. Therefore no odd-section continuation is needed, \(h=0\) and \(E(x)=F(x)\). Substituting \(x=2u\) gives \(4E(x)=5x+2\), proving (2). The divisibility and odd-\(q\) congruence follow. This is a true conditional identity for every legal source, with no finite cutoff. QED. The symbolic source value `x=8*w+6` with `w>=1`, its exact generic first section successor `10*w+8`, its immediate evenness, and equality (2) are kernel-checked in [SheepCorridor.lean](SheepCorridor.lean), theorem `forced_from_residue_eight` with axioms `[propext, Quot.sound]`. The stronger `forced_unbounded_drop` imports no finite cutoff: for arbitrary `b>=1`, `2^(b+2) | x+2` and `x>=14`, it constructs the authentic-formula immediate-even next section value and proves `2^b` divides its successor-plus-two. Its axiom audit is exactly `[propext, Quot.sound]`, and the auxiliary `affine_divisor_drop` uses `[propext]`.

**Lemma 2 (entire forced prefix).** Start with any sequence of legal consecutive generic first-even returns \(x_0\to x_1\to\cdots\), or any sequence of quotient edges whose first residue is
\[
x_0\equiv -2\pmod {2^p}.
\]
Then for every \(i\) with \(0\le i<\lfloor(p-1)/2\rfloor\), the next step is forced to be the \(a=1,h=0\) branch, with
\[
x_i+2\equiv0\pmod {2^{p-2i}},\qquad
x_{i+1}\equiv f_q(x_i)\pmod q.
\]
The proof is induction using Lemma 1. All its conditions depend only on the current *residue*, so the same induction applies even if a quotient graph path uses different positive integer witnesses at each edge.

Consequently:
- For \(p=2k+1\ge3\), **all first \(k\) steps** from residue \(-2\) have \(a=1,h=0\); the terminal odd-\(q\) coordinate is forced to be \(f_q^k(r_q)\).
- For \(p=2k\ge2\), **the first \(k-1\) steps** have \(a=1,h=0\), leaving a source congruent to \(-2\bmod4\) and with odd-\(q\) coordinate \(f_q^{k-1}(r_q)\). Its last step has \(a=1\), but any \(h\ge0\) may occur.

For every \(i<k\), the intermediate dyadic residue satisfies \(x_i+2\equiv0\bmod 2^{p-2i}\) with \(p-2i\ge2\); thus \(x_i\not\equiv0\bmod 2^p\). A path to a target with dyadic coordinate zero **cannot arrive in fewer than \(k\) steps**.

## Odd precision \(p=2k+1\)

Assume \(k\ge1\) and \(q>1\). Choose the source vertex \(r\) by CRT with \(r\equiv-2\bmod 2^p\) and \(r\equiv0\bmod q\). Let \(z=f_q^k(0)\), and choose the target vertex \(s\) by CRT with \(s\equiv0\bmod2^p\) and \(s\equiv z+1\bmod q\). The latter differs from \(z\) because \(q>1\).

A path \(r\to s\) with fewer than \(k\) edges is impossible by the last observation. A path of exactly \(k\) edges must follow the forced \(a=1,h=0\) corridor, so its odd coordinate is necessarily \(z\), contradicting the chosen target. Hence \(d_{G_m}(r,s)\ge k+1\).

## Even precision \(p=2k\)

Assume \(k\ge1\), \(q>1\). Choose \(r\equiv-2\bmod2^p\) and \(s\equiv0\bmod2^p\). After \(k-1\) forced steps the final source has \(a=1\). For any legal final generic first-even block, including \(h=0\), its odd coordinate satisfies
\[
s_q \equiv 1+(3\cdot2^{-1})^h (f_q^k(r_q)-1)\pmod q.
\tag{4}
\]

Two disjoint cases give an explicitly missing residue:

**Case A: \(5\nmid q\).** The affine map \(f_q(z)=4^{-1}(5z+2)\) is invertible on \(\mathbb Z/q\mathbb Z\). Set \(r_q=f_q^{-k}(1)\) (compute by applying \(z\mapsto5^{-1}(4z-2)\) exactly \(k\) times). Then \(f_q^k(r_q)=1\) and (4) makes **every possible \(k\)-step target** congruent to \(1\bmod q\), regardless of the last \(h\). Choose \(s_q=0\). Since \(q>1\), this is impossible.

**Case B: \(5\mid q\).** Choose any \(r_q\), e.g. zero. Modulo five, \(f_5(z)=3\) for every \(z\), so \(f_5^k(r_q)=3\). Because \(3\cdot2^{-1}\equiv -1\bmod5\), (4) reduces to
\[
s_q\equiv1+2(-1)^h\in\{3,4\}\pmod5.
\]
Choose \(s_q=1\bmod q\). This would require \(s_q=1\bmod5\), a contradiction. The all-h residue exclusion `(1+2*4^h)%5 !=1` is kernel-checked in `SheepCorridor.forbidden_mod_five`, which uses `[propext]` alone.

Shorter paths were already excluded by their dyadic coordinate. Therefore \(d_{G_m}(r,s)\ge k+1\) in either case.

For \(p=1\), the graph has \(q>1\) distinct even vertices, so its diameter is at least one. Agent 22's original zero-hub/coherent construction gives the matching one-step upper bound.

## Strengthening to all legal first-even return branches

The published Sheep section relation has exactly one other **nonterminal** branch: if \(x=3\cdot2^a\) (\(a\ge0\)), then \(F(x)=x+a+3\). The section halts on the remaining odd-part-one powers. For even-section inputs \(a\ge1\). The only exceptional even input of valuation \(a=1\) is \(x=6\), whose first section successor is \(F(6)=10\), already even. Thus its full first-even return is **exactly \(6\to10\)**. Standalone [SheepCorridor.lean](SheepCorridor.lean) additionally checks `special_at_one: specialFirst 1 = 10` (no axioms) and `ten_not_dyadic_zero: ∀ p≥2, 10%2^p ≠0` (axioms `[propext]`). These are source-formula-compatible arithmetic certificates, with no claimed import of the original Cryptids Step relation.

Let \(H_m\) be the **unrestricted synthetic even-return quotient graph** with every genuinely legal nonhalting first-even return (both generic and odd-part-three branches) as an edge. We claim the same exact diameter (1), and the same sharp **unrestricted coherent free-start** maximum path length, hold in \(H_m\).

**Proof.** Since the generic graph \(G_m\) is a subgraph, the established generic diameter/coherent upper bounds apply unchanged. We need only retain the lower witness \(r,s\) from the previous sections when extra exceptional edges are permitted.

In all constructed lower witnesses with \(p\ge2\), the initial dyadic coordinate is \(r_2=-2\bmod2^p\), and the target's dyadic coordinate is \(s_2=0\bmod2^p\). At every stage \(i<k=\lfloor p/2\rfloor\), the forced-prefix congruence is \(x_i+2\equiv0\bmod2^{p-2i}\), with exponent \(p-2i\ge2\). Such an \(x_i\) has exact 2-adic valuation **one**, so a special branch could only arise at \(x_i=6\). But \(6+2=8\) cannot be divisible by \(16\). Consequently the **first \(k-1\) outgoing edges** must remain generic (the required exponent is at least 4 for these edges), and the entire previous forced affine calculation still applies.

At the possible **last \(k\)th edge**, an exceptional source \(x_{k-1}=6\) would return \(10\). Since \(10\not\equiv0\bmod2^p\) for every \(p\ge2\), that edge cannot reach the selected lower-bound target \(s\). All genuine remaining final branches obey the generic formula and the previously proved odd-\(q\) obstruction. Hence the same source and target remain distance at least \(k+1\) for \(q>1\). For \(q=1\), all paths with fewer than \(k\) edges were already excluded by the forced dyadic nonzero corridor, so the exact lower bound \(k\) survives too.

For \(p=1\), the graph has one even residue if \(q=1\), and \(q>1\) distinct even residues otherwise, forcing respective lower bounds 0 and 1. The generic upper constructions attain both. Thus (1) holds for the **full legal first-even quotient** and for its coherent free-start counterpart. QED.

**Verification scope:** [mixed_diameter_certificate.py](mixed_diameter_certificate.py) fully enumerates the *generic* finite graphs; a separate bounded exploratory audit added the exceptional edges from all sources \(3\cdot2^a\) for \(1\le a\le300\) on representative small moduli, finding no diameter change. The **all-index theorem above is mathematical**, using an exhaustive exceptional-source *classification by valuation* rather than the finite audit. This full-branch corollary still makes no assertion that any arbitrary chosen start is actually reached from the true blank section \(10\).

## Stronger result: the entire \(-2\) fiber consists of diameter sources

The lower-witness construction above can be made **uniform in its source's odd residue**, producing an exact eccentricity classification rather than one example.

**Corollary (universal maximal-eccentricity fiber).** Fix \(p\ge1\), odd \(q\ge1\), and *any* even source residue \(r\pmod{2^p q}\) satisfying
\[
r\equiv-2\pmod{2^p}.
\]
Its eccentricity in both the generic graph \(G_m\) and unrestricted legal graph \(H_m\) equals the diameter in (1). There are exactly \(q\) such source vertices, an exact fraction \(2^{1-p}\) of the total even-residue vertices. The same statement is true for the coherent free-start distance function.

**Proof.** For \(q=1\) and \(p\ge2\), the forced corridor cannot hit any dyadic-zero residue before \(k=\lfloor p/2\rfloor\) returns, and the already proved diameter upper bound is \(k\). For \(p=1,q=1\), the sole vertex has eccentricity zero.

For \(q>1,p=1\), every even source residue belongs to the dyadic-zero fiber; the known outgoing-zero hub realizes all targets in one step, and each source has another distinct target.

For \(q>1\) and odd \(p=2k+1\ge3\), let \(r_q\) be **arbitrary**. The first \(k\) returns are forced to have odd coordinate \(f_q^k(r_q)\). Choose any target with dyadic coordinate zero and odd coordinate \(f_q^k(r_q)+1\pmod q\). The original lower argument applies with no restriction on \(r_q\).

For \(q>1\) and even \(p=2k\), the final block's odd residue is still given by (4) for **any** \(r_q\). Choose an odd prime \(\ell\mid q\), and set \(z=f_\ell^k(r_q\bmod\ell)\). If \(\ell=3\), the final odd residue modulo three lies in \(\{z,1\}\): \(h=0\) gives \(z\), while every \(h\ge1\) yields \(1\). Since this set has size at most two, choose a missing residue \(w\pmod3\). If \(\ell\ne3\), the multiplier \((3/2)^h\) is a unit modulo \(\ell\) for every \(h\). If \(z=1\), every final residue equals \(1\pmod\ell\), so take \(w=0\). If \(z\ne1\), no final residue is \(1\pmod\ell\), so take \(w=1\). In all cases choose a target \(s\) with \(s\equiv0\pmod{2^p}\) and \(s\equiv w\pmod\ell\), possible by CRT. No path of at most \(k\) returns reaches \(s\). The earlier full-branch exceptional-source argument leaves this unchanged.

Both corresponding upper bounds apply from every vertex, so each source in the entire \(-2\) fiber has maximal eccentricity. Since there are \(q\) sources among \(2^{p-1}q\) even residues, their fraction is \(2^{1-p}\). Every coherent path is also a synthetic path, while established coherent upper constructions attain the same universal bound. QED.

The [finite complete graph regression](mixed_diameter_certificate.py) can additionally verify the corollary for every \(-2\)-fiber source at all tested moduli; the original standalone finite implementation separately checked 409 such sources across its 51 complete graphs. The universal corollary follows from the displayed prime-residue argument, not those tests.

## Exact equality, coherent version, and proof status

The previous mixed CRT and coherent all-parameter constructions provide the universal upper bound \(k+1\). The new explicit pair \(r,s\) witnesses the matching lower bound for **every** odd \(q>1\), every \(p\ge1\). The same lower bound holds for the coherent freely selected one-orbit distance, because every physical coherent path projects to an edge path in \(G_m\). Agent 22's coherent upper bound proves its equality. The \(q=1\) case is settled independently in [DYADIC-DIAMETER.md](DYADIC-DIAMETER.md). This proves (1).

[The independent verifier](mixed_diameter_certificate.py) reconstructs the exact inverse dyadic gate and odd-coordinate E action, computes a provably sufficient finite \(h\)-period cutoff for each fixed modulus, enumerates all generic quotient edges and all-pairs distances for sample moduli, and verifies the constructed lower witnesses. Its finite cases corroborate, but are not used to infer, the all-\(p,q\) theorem.

**Unresolved global quantifier:** Nothing here constrains which residue words are visited by the original blank-start Sheep orbit from \(10\). Both the generic and full-branch mixed diameter theorems, including their single-free-start strengthening, leave the authentic halting question open. The mathematical proof relies on existing all-parameter **paper** upper bounds. Two key arithmetic lemmas have separate standalone Lean4.36.0-rc2 certificates, but there is no completed source-integrated all-parameter Lean diameter theorem; independent adversarial review and outside novelty checking are warranted. This work remains under \`im-results/\`.
