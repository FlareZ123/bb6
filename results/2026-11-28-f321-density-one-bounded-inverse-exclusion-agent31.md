# F321: an explicit density-one modular family of bounded-depth terminal exclusions

**Theorem (paper-level derivation; 28 November 2026).** For the formalized two-counter map of the F321 six-state Busy Beaver holdout, there is an **explicit recursively enumerable collection of modular certificates** proving that the halting gate `H_d=(d+1,d)` cannot be reached from the genuine seed `(1,1)`, and the set of certified terminal parameters has **natural density one**. For each integer `n≥1`, a finite, effectively constructible union of dyadic residue classes suffices to exclude a set of `d` of natural density **at least** `1−(3/4)^n`; the exclusion is valid beyond the explicit finite cutoff `d≥6·2^n−3`. In particular, the proportion not excluded by these *bounded-depth modular arguments* tends to zero as the permitted certificate depth grows.

**Important limitation:** This is **not** F321 nonhalting. There may still be exceptional terminal parameters (potentially including the authentic one if it halts), and the density-one union does not bound the first possible terminal index or decide the actual orbit. The theorem concerns the upstream exact counter map of [google-deepmind/cryptids at `c86f15861709b76042998c5211c7b2f83991621b`](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean). The new *density-one counting conclusion* is self-contained below and not yet Lean kernel-certified, but the central **all-depth finite modular exclusion criterion is now Lean 4.36.0-rc2 kernel-checked** on a literal implementation of the upstream two-counter map: see [F321BackwardBarrier.lean](../im-results/agent31-f321-bulk/F321BackwardBarrier.lean), [FiniteResidueCheck.lean](../im-results/agent31-f321-bulk/FiniteResidueCheck.lean), and [ExplicitResidueFamilies.lean](../im-results/agent31-f321-bulk/ExplicitResidueFamilies.lean). These do not import the upstream physical six-state reduction; the original-machine bridge remains separate. The six-state maximality problem BB(6) remains open.

## 1. Exact inverse structure

For a counter pair `(A,D)`, the only possible immediate predecessors with `D≥3` are

```
H^{-1}(A,D) = (A+(D+1)/2, (D−3)/2)          when D≥3 is odd,
F^{-1}(A,D) = ((A−6)/4, D+3(A−6)/4)        when A≥6, A≡2 (mod4), D≥1.
```

These are the inverses of the upstream *high* branch `(a,d)↦(a−d−2,2d+3)` and the *far* branch `(a,d)↦(4a+6,d−3a)`. The other two nonhalting branches always output second coordinate **1 or 2** (equality and middle), and therefore cannot be inverse antecedents at second-coordinate values `D≥3`. Both formulas follow by direct algebra and carry their exact forward guards. See the [complete inverse classification](2026-11-28-f321-70-percent-halt-ray-exclusion-agent31.md) for the small-coordinate branches.

The initial gate has `(A,D)=(d+1,d)` and `A+D=2d+1`. A high inverse changes the parameter sum by `−1`; a far inverse changes it by `−6`. Thus after a formal sequence `w` of `h` high inverses and `f` far inverses, the sum is **exactly**
```
A_w(d)+D_w(d) = 2d+1−h−6f,
```
whenever the inverse path is valid.

## 2. A uniform second-counter barrier

Let `w` be any valid inverse chain consisting only of H/F moves, and let `D_j` be its second coordinate after `j` inverse moves, starting `D_0=d`. Then
```
D_j ≥ (d+3)/2^j − 3                        (j≥0).
```
This is an elementary induction. A high inverse gives `D_(j+1)=(D_j−3)/2`, exactly propagating the lower bound; a far inverse gives `D_(j+1)=D_j+3(A_j−6)/4≥D_j` because the far guard requires `A_j≥6`, and so also propagates the lower bound.

Consequently, for any `n≥1`,
```
d ≥ 6·2^n−3          ⟹          D_j ≥ 3 for all j≤n.
```
Induction on the inverse-path length now shows **every** possible inverse path of length at most `n` from such a gate uses only H/F branches: at all intermediate configurations the other inverse branches are impossible because `D≥3`. No configuration on such a path can equal the genuine seed `(1,1)`, whose second coordinate is 1.

## 3. Odd-numerator dyadic congruence theorem

For a word `w∈{H,F}^*`, even if its guards fail, apply the H/F algebraic formulas *formally* to the gate. Write its first coordinate in reduced dyadic-power form
```
A_w(d) = (u_w d+v_w) / 2^(s_w),
s_w = #(H in w)+2·#(F in w).
```
**Claim:** `u_w` is always an **odd integer**. This is proved with the following exact integer recursion, initialized at `(u,v,s,c)=(1,1,0,0)`, where `c=h+6f` is the decrease in counter sum:

```
Append H:
  u' = u + 2^(s+1)
  v' = v + 2^s (2−c)
  s' = s+1
  c' = c+1

Append F:
  u' = u
  v' = v−6·2^s
  s' = s+2
  c' = c+6.
```

To derive H, substitute `D=2d+1−c−A` into `A' = A+(D+1)/2`, giving `A'=(A+2d+2−c)/2`. F uses `A'=(A−6)/4`. These substitutions prove both recurrences. The numerator `u` starts odd and each H adds an even number while F does not change it, so the parity property follows by induction.

If the word `w` occurs as a **valid integer** inverse path from a gate indexed by `d`, then necessarily
```
u_w d+v_w ≡ 0 (mod 2^(s_w)).
```
Since `u_w` is odd and hence invertible modulo `2^(s_w)`, this congruence has **exactly one** residue solution
```
d ≡ r_w := −u_w^(-1) v_w (mod 2^(s_w)).
```
Thus all potential gates admitting a given length-`n` H/F inverse word belong to a single, algorithmically computed arithmetic progression of natural density `2^(−s_w)`.

## 4. Explicit infinite exclusion sieve and exponential tail bound

For any positive integer `n`, enumerate the **finite** set of `2^n` words `w∈{H,F}^n`. Compute each residue `r_w` by the recursion above and the modular inverse of the odd coefficient `u_w`. Define the *candidate superset*
```
U_n = union_{w∈{H,F}^n} { d≥0 : d≡r_w (mod 2^(s_w)) }
```
and the explicitly excluded set
```
E_n = { d≥6·2^n−3 : d∉U_n }.
```

For `d∈E_n`, §2 says every hypothetical inverse path of length `n` would be H/F, and §3 would force membership in `U_n`, a contradiction. Hence its inverse ancestry has length **strictly less than n**, and all its vertices have second coordinate at least three. It therefore cannot contain the genuine seed `(1,1)`: **every d∈E_n is rigorously excluded.**

A union bound on modular densities gives
```
dens(U_n) ≤ Σ_{w length n} 2^(−s_w)
          = (1/2+1/4)^n = (3/4)^n.
```
Removing finitely many parameters below the explicit cutoff does not change density, so **`E_n` has natural density at least `1−(3/4)^n`**. More quantitatively, for every finite `X≥0`, the number of terminal parameters `0≤d≤X` that either lie below the cutoff or are not excluded at depth `n` satisfies
```
#([0,X] \ E_n) ≤ 6·2^n + (X+1)(3/4)^n + 2^n
                ≤ (X+1)(3/4)^n + 7·2^n.
```
The `2^n` term accounts for rounding in the at-most-one residue count for each of the `2^n` words. There is no probabilistic independence assumption.

**Exact finite first-moment identity.** For a length-`n` word with `h` high and `f=n−h` far letters, its integrality congruence has exactly `4^n/2^(h+2f)=2^h` representatives among the `4^n` residues `d mod4^n`. Summing with multiplicity over all `2^n` words gives the precise combinatorial identity
```
Σ_(d mod 4^n) # {w∈{H,F}^n : A_w(d) is integral}
  = Σ_(h=0)^n binomial(n,h) 2^h
  = 3^n.
```
The mean number of **formal integral** inverse words at depth `n` is therefore exactly `(3/4)^n`, and the sum of these means over **all finite depths** is `Σ_(n≥0)(3/4)^n=4`. This is a *first-moment identity* for dyadic arithmetic words, not a claim of independent paths or of an actually infinite Turing-machine execution. It explains why the modular sieve becomes sparse and why exact reverse symbolic searches can be economical. The union bound above is the corresponding first-moment estimate for *existence* of a candidate path.

Finally put `E=⋃_{n≥1}E_n`. As a countable union of explicitly modularly certified exclusion sets it is constructively enumerable. For any `n`, `E⊇E_n`, hence its complement has upper natural density at most `(3/4)^n`; letting `n→∞` gives

```
                       dens(E) = 1.
```

The substance is **not** the tautology that a deterministic machine can halt at most once: this theorem gives an effective, input-independent, arithmetic **finite-depth certificate construction** for a density-one set of all potential terminal parameters, together with a quantitative exponential bound on the unresolved depth-`n` inverse language.

## 5. Lean 4 kernel-certified source-counter modular exclusion

The exact upstream counter map has been restated as an inductive `CounterMove` relation in [SourceCounter.lean](../im-results/agent31-f321-bulk/SourceCounter.lean). Its high/far inverse exhaustiveness when output second coordinate is at least three and its strict counter-sum growth are proved without `sorry`.

The chain of checked theorems is:

- `DensityOneCore.compiled_numerator_odd` and `DensityOneExtension.formal_inverse_congruence`: arbitrary words of high/far inverse moves have the exact odd-coefficient terminal identity from §3.
- `F321BackwardBarrier.backward_to_formal`, `backward_end_large`, and `no_backward_root`: the cutoff in §2 transports **every genuine finite inverse chain** to a formal high/far word at the chosen depth and excludes both shorter and longer seed-reaching paths whenever the modular condition fails.
- **`F321BackwardBarrier.no_halting_gate_from_seed`**: for **every** `n,d` with `6·2^n≤d+3` and `NoResidueWord n d`, proves `∀m, ¬CounterReach 1 1 m (d+1) d`. This quantifies over *all* forward lengths, not merely the length of the test.
- **`FiniteResidueCheck.no_halting_gate_after_decide`**: the same universal result follows directly from the finite executable Boolean `residuePass n d=true`. `words_complete` kernel-proves that every possible inverse word of length n occurs in the enumeration; `gate1000_never` is a fully closed example with `n=4,d=1000`.
- **`ExplicitResidueFamilies.even_gate_never`, `seven_mod8_gate_never`, and `one_mod8_gate_never`**: kernel-checked all-time exclusion of every even `d`, every `d≡7 (mod8)`, and every `d≡1 (mod8)`, including small cases below the generic depth-n threshold. Together these are a simple kernel-proved density-`3/4` subfamily of the broader paper theorem.
- **`F321Periodicity.residuePass_periodic` and `residue_class_never`**: the Boolean test at depth n is periodic in d with exact period `4^n`; any accepted residue defines an *entire infinite progression* of forbidden terminal indices, apart from the explicit finite cutoff. The companion `source_gate_forces_congruence` constructively extracts one congruence word from any hypothetical genuine gate-reaching counter orbit.
- **`F321FiniteDensity.accepted_depth5`**: a normal kernel `by decide` calculation, without `native_decide` or any extra trust axiom, checks exactly **898 of the 1,024 residue classes modulo 4⁵** pass the depth-5 test. Consequently an explicitly defined **natural-density 898/1024 = 87.6953125%** set of terminal parameters is excluded (ignore only finite d<189). Depth 4 similarly checks 210/256. These are computer-evaluated *kernel* theorems, unlike the independent 2²⁰ Node affine result.

Local compilation with pinned Lean **4.36.0-rc2** has been completed for these modules. Their `#print axioms` report only standard `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. A dedicated GitHub Actions source check is configured in [agent31-f321-affine-terminal.yml](../.github/workflows/agent31-f321-affine-terminal.yml), while cross-system CI acceptance must be stated separately from local acceptance. The **density-one measure-theoretic union bound of §4 remains a paper proof**; an additional Lean formalization would need the 2-adic modular counting argument. None of these checked counter-map statements is a direct theorem about the original six-state tape machine until it is composed with the pinned upstream reduction.

## 6. Relation to other F321 results and research frontier

The [elementary 33/40 explicit residue-family theorem](2026-11-28-f321-70-percent-halt-ray-exclusion-agent31.md) gives simple closed progressions with very short inverse contradictions, including small parameters below the density-one sieve's cutoff. The [maximal high/far bulk accelerators](../im-results/agent31-f321-bulk/README.md) provide exact forward and inverse arithmetic and a finite blank-root counter experiment. The [conservative affine residue-class checker](../im-results/agent31-f321-bulk/affine_terminal_sieve.cjs) offers complementary finite exhaustive certificates: at modulus `2^20`, a V8 prototype found `1,038,925` of `1,048,576` residue classes provably excluded by symbolic inverse trees; this count requires independent workflow acceptance before promotion to a source-certified result. Neither computational count is used in §§1–4.

**Remaining hard quantifier:** The exceptional 2-adic inverse rays may have zero density yet contain the single authentic terminal parameter if the machine halts. Deciding F321 requires a root-specific all-time exclusion of those exceptional rays, or an explicit reached halt; this result alone does neither. To deepen the proof, study the nested exceptional congruence sets `U_n` and their intersection, and construct an induction excluding the exact rooted seed from every surviving branch. A kernel-accepted Lean version of the general odd-numerator lemma and safe inverse-prefix rule would make this density-one mathematical theorem reusable in source-connected verification.
