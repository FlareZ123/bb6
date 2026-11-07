# P1 inverse shadow: periodic-depth rays are excluded (paper proof)

**Status:** Proposed all-period analytic argument, 7 November 2026, extending Agent 13's previously certified fixed-depth, alternating-depth, and finite-block potential work. The integer-drift lemma is independently **Lean 4.36.0-rc2 kernel-checked** in [PeriodCore.lean](PeriodCore.lean), axioms exactly `[propext, Quot.sound]`. **The entire arbitrary-word source-equation-to-affine-block reduction is now independently Lean kernel-checked** in [PeriodWord.lean](PeriodWord.lean), including its `periodic_run_integral_slope` corollary for infinite repetitions of any finite word; axioms `[propext, Classical.choice, Quot.sound]`. Both modules use standard Lean axioms and no `sorry` or `native_decide`. The separate [PeriodWordBounds.lean](PeriodWordBounds.lean) now kernel-checks the exact marker decomposition `2^S=H+loss+1`, proves `H<2^S`, and certifies `H<2^S-1` whenever at least one depth is positive; axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`. The derivation of all-cost **primitive marker impossibility** is now fully Lean kernel-checked in [PeriodPrimitive.lean](PeriodPrimitive.lean), using [PeriodMarker.lean](PeriodMarker.lean), [PeriodRotate.lean](PeriodRotate.lean), [PeriodCycle.lean](PeriodCycle.lean) and the exact [PeriodWord.lean](PeriodWord.lean) grammar. It has `#print axioms` output exactly `[propext, Classical.choice, Quot.sound]`, no `sorry`. **The final nonprimitive-word reduction and original-source feeder `ShadowReach` import remain paper-level, without source CI.** The finite-state pigeonhole mechanism for cyclic residues is independently Lean-checked in [PeriodPigeonhole.lean](PeriodPigeonhole.lean) and [PeriodCycle.lean](PeriodCycle.lean): for a deterministic periodic orbit whose S residues all lie in {1,...,S-1}, there must be a return in fewer than S steps. Those modules still assume the orbit and state bounds, so the crucial connection to rotating marker words is not yet checked. This is a source-equation-derived *paper theorem*, pending independent proof review. It does not decide P1, any BB(6) holdout, or BB(6).

## Prior art and precise incremental scope

The closest pre-existing mathematics in [Agent 13's BlockPotential.lean](../agent13-p1-adaptive-param/BlockPotential.lean) gives the identical affine-block potential and its primary modular nonvanishing test, including an abstract unlimited-repetition impossibility whenever `(A-1)∤H*S`. [AlternatingDepth.lean](../agent13-p1-adaptive-param/AlternatingDepth.lean) already kernel-certifies nonrepetition of the two mixed period words `[0,1]` and `[1,0]`. [BlockSecondary.lean](../agent13-p1-adaptive-param/BlockSecondary.lean) adds a secondary modular obstruction where the primary test fails. [periodic_word_modular.py](../agent13-p1-adaptive-param/periodic_word_modular.py) exhaustively screened the arithmetically admissible words through total cost `2048`, with zero unresolved nonzero-depth words, as a **finite computation**. These results predate the present attempt.

The substantive **new all-cost theorem** is that an infinite exact scalar inverse ray cannot repeat any primitive marker word containing a positive depth. It is now Lean kernel-certified as `PeriodPrimitive.no_infinite_primitive_ray`, making secondary modular tests unnecessary for primitive words. The conversion of an arbitrary nonprimitive period to an actual shorter depth list is still a paper-level argument. The new kernel-checked modules `PeriodWord.lean` and `PeriodFiniteWord.lean` provide a generic exact arbitrary-depth-word bridge and explicit finite-repetition bound in a different proof style. These support the proposed unbounded theorem, but overlap the earlier potential mechanism. No independent mathematical novelty assessment has been completed.

## New all-cost Lean theorem for primitive depth words

[PeriodPrimitive.lean](PeriodPrimitive.lean), `PeriodPrimitive.no_infinite_primitive_ray`, compiled locally in Lean 4.36.0-rc2, with final kernel axioms exactly `[propext, Classical.choice, Quot.sound]`, no `sorry`. For any nonempty finite inverse-depth word `w` containing some `t>0`, put `S=cost w`, `H=weight w`. Define **primitive** to mean that no `0<r<S` satisfies the exact cyclic marker equation `(2^r*H) mod (2^S-1)=H`. The theorem proves that for any feeder constant `L` and any natural-valued functions `m(n),z(n)`, the propositions

```text
forall n, Run L w (m n) (z n) (m(n+1)) (z(n+1))
```

are inconsistent whenever w is primitive and contains a positive depth. Here `Run` is the exact finite predecessor relation built from unchanged original-source scalar arithmetic, defined explicitly in [PeriodWord.lean](PeriodWord.lean). The theorem has no period-length, depth, cost, initial-state, or finite-step cap.

The proof uses the already checked all-word drift necessity `(2^S-1)|S*H`, the marker bound `0<H<2^S-1`, and a **fully checked** all-integer shorter rotation lemma [PeriodMarker.lean](PeriodMarker.lean), `shorter_marker_rotation`. The latter shows that any marker with an integer slope `Q=S*H/(2^S-1)` strictly between zero and S necessarily has a shorter cyclic binary return. Its proof maintains the exact rational relation under binary doubling [PeriodRotate.lean](PeriodRotate.lean), then applies the finite deterministic-cycle [PeriodCycle.lean](PeriodCycle.lean) pigeonhole theorem. All these are general arithmetic theorems, with standard Lean axioms.

This establishes the claimed impossibility **for primitive depth periods** beyond the earlier finite cost 2048 scan. A complete no-eventually-periodic source theorem must additionally prove in Lean that every nonprimitive repeating depth list admits a strictly shorter *actual inverse-depth word* whose repetitions describe the identical infinite scalar path, and compose Agent 13's verified zero-depth feeder margin. That final logical reduction is given as a paper proof below and is **not** yet a kernel-certified total-period theorem. The original BB(6) problem is unaffected.

## Claim and original-source boundary

Consider any infinite path of nonnegative integers `(m_i,z_i)` under the exact P1 scalar predecessor grammar, with fixed natural `L`:
```text
z_i = 2^t_i * v_i,
2*z_(i+1) + 1 = L + m_i + t_i + v_i,
m_(i+1) = m_i + t_i + 1.
```
The paper argument below establishes: **if the depth sequence `(t_i)` is eventually periodic, its eventual period consists solely of zeros**. If the initial node is descended from either genuine P1 feeder
`(L,z_0)=(16q+8,12q+4)` or `(16q+9,10q+4)`, even the all-zero case is impossible, since the source-proved preserved margin `z+4≤L+m` excludes any infinite zero-depth tail. Thus **no infinite genuine feeder shadow path has an eventually periodic depth sequence**, conditional on the exact equations and the paper combinatorial lemma detailed below.

This is an exclusion of one type of possible infinite inverse history. Infinite **aperiodic**, unbounded-depth, and mixed histories remain completely open. In particular, no source `Reach` target or blank machine behavior is decided.

The upstream-equation bridge is documented in [Agent 9's source `ShadowReach`](../agent9-p1-q33/UniformPrecisionPath.lean), and the certified preserved margin and homogeneous-depth exclusion in [Agent 13's dossier](../agent13-p1-adaptive-param/FixedDepthDossier.md), [CI 42314919290](https://github.com/FlareZ123/bb6/actions/runs/42314919290). These predecessors are source-verified; the new mixed-word conclusion has only the proof status stated above.

## Exact arithmetic of one finite depth word

Fix a nonempty period `t_1,...,t_k` and put `l_j=t_j+1≥1`, partial cost `s_j=l_1+...+l_j`, total `S=s_k`, and `A=2^S`. Rewriting one scalar edge without division yields

```text
2^(t+1)*z' = z + 2^t*(L+m+t-1).
```

Multiplying successive equations by the appropriate powers of two telescopes to

```text
A*z_after = z_before + H*(L+m_before) + D,
H = Σ_(j=1)^k 2^(s_j-1),
D = Σ_(j=1)^k 2^(s_j-1)*(s_j-2).
```

The exact natural-number inequality and its all-zero equality case are independently Lean-checked in [PeriodWordBounds.lean](PeriodWordBounds.lean) (SHA-256 `bc08eb422a1d990aab43c156903eedd697e70813ce6f21c95e1893174acf3881`). The powers appearing in `H` are distinct: `H` is the binary word of length `S` whose one-bits occur exactly at the *ends* of the individual cost blocks. In particular `2^(S-1)≤H≤2^S-1`, and equality at the upper bound occurs exactly when every `l_j=1`, meaning all depths zero.

Under an infinite repetition of this word, take the end-of-block values `Z_n` and `X=L+m_0`. The total cost increases by `S` at every block, so

```text
A*Z_(n+1) = Z_n + H*X + H*S*n + D,    n≥0.
```

Put `Δ_n=Z_(n+1)-Z_n`. Subtract consecutive equations:

```text
A*Δ_(n+1) = Δ_n + H*S.
```

The integer error `E_n=(A-1)*Δ_n-H*S` satisfies `E_n=A*E_(n+1)`. Since `A≥2`, the integer `E_0` is divisible by `A^n` for *every* `n`; taking `n=|E_0|` forces `E_0=0`. Consequently,

```text
(2^S-1) divides H*S.                            (★)
```

The error argument is Lean theorem `PeriodCore.periodic_integral_slope`. The source-equation reduction for an arbitrary depth word, using exact inductive `PeriodWord.Run` and no assumed block formula, is Lean theorem `PeriodWord.block_affine`; `PeriodWord.periodic_run_integral_slope` proves (★) for any infinite sequence of actual wordwise shadow predecessor runs. Its axiom audit lists `[propext, Classical.choice, Quot.sound]`. The `no_mixed_01_ray` theorem separately gives a sample concrete mixed-depth obstruction. The core source SHA-256 is `d94d03e1e9f2312bba1a4f37fba5edb4de72e12ee2568b299c53c1d8361f0aac`; the fully checked arbitrary-word source SHA-256 is `41ddcdce1b48d5c69dee9f45fc0477c2d39a264a9d4db0be709caa4f93f96dcc`.

## Why every nonzero-depth repeating word is impossible

Assume at least one `l_j>1`, giving `0<H<B=2^S-1`. Reduce the rational `H/B=h/d` to coprime numerator and denominator, so `d=B/gcd(H,B)>1`. The necessary condition (★) gives **`d|S`**.

The rational number `h/d` has the purely periodic base-two expansion formed by endlessly repeating the `S` binary digits of `H`. Because `d` is an odd divisor of `2^S-1`, the smallest digit period is `r=ord_d(2)`, the multiplicative order of 2 modulo `d`. Elementary modular arithmetic gives `r|S`; the `r` residues `1,2,...,2^(r-1)` modulo `d` are distinct nonzero residues, so **`r≤d-1<d`**.

The marker word therefore repeats every `r` bits. Its most significant digit is one, so every length-`r` block also ends with a marker. Thus the original list of depths repeats a shorter, nonempty depth list of total cost `r`. Let its marker be `H_r`. Equality of the periodic binary fractions gives

```text
H_r/(2^r-1) = H/(2^S-1) = h/d
```

in lowest terms. Apply the same integer-drift necessity (★) to the infinite path grouped in this *shorter* period: `(2^r-1)|r*H_r`, hence **`d|r`**. This contradicts `0<r<d`. Therefore no infinite periodic path can have a positive depth in its period.

### Alternative finite-state proof of the shorter binary period

The necessary divisibility (★) also permits a proof without multiplicative orders. Put `B=2^S-1` and `Q=S H/B`. It is an integer in `1,...,S-1` whenever the period contains a positive depth, by the checked marker bounds. Regard the S-bit marker H as a cyclic binary word. One cyclic left rotation sends `H` to `H'=2H-bB`, where `b∈{0,1}` is the outgoing most significant bit. Accordingly `Q'=2Q-bS` is again an integer between 1 and `S-1`: this holds at every rotation because the rotated marker remains strictly between 0 and B. The induced map is deterministic, `Q→2Q mod S`.

Among the S cyclic rotations, S integer values Q belong to a set of only S-1 elements. The pigeonhole principle gives a repeated value at a shift `0<r<S` (the abstract deterministic-cycle shortening is source-independent and Lean-checked in [PeriodCycle.lean](PeriodCycle.lean), SHA-256 `3b9b93e0d190ebdaf9ffe46d0b4bef086180dc55ede70f8ae255adcb36b2dc25`; its finite injection proof is [PeriodPigeonhole.lean](PeriodPigeonhole.lean), SHA-256 `8ebb2467af4319962f5f1074f4974ef4a1d7c62470e16fa4fd91b91b68978fd4`). Iterating the deterministic doubling map forces the cyclic binary marker to repeat after r positions. Because the top marker bit is 1 at the original block boundary, the shorter marker block of length r ends in 1 and is a genuine shorter list of inverse costs. Choose a shortest-period depth list if there were an infinite eventually periodic run; that list would have a strictly shorter period, contradiction. The all-zero-depth case follows from the original feeder margin below. This is a second **paper proof** of the finite-word combinatorial step; its rotation/pigeonhole formalization remains pending.

The remaining case `H=B` is the all-zero-depth word. For both authentic feeder roots `z_0+4≤L`, and Agent 13 has already source-checked preservation of `z+4≤L+m` and the impossibility of an infinite zero-depth tail. A finite prefix before a repeated tail changes `m,z` but preserves the required margin. That completes the paper proof of the stated genuine-feeder conclusion.

## Certified finite-horizon repetition bound

An additional pair of original new modules, [PeriodFinite.lean](PeriodFinite.lean) (source SHA-256 `f3b57ddb04c0491ffcc5bf54c18f48319a9a64f38dbfa0af91a81d3514000c17`) and [PeriodFiniteWord.lean](PeriodFiniteWord.lean) (SHA-256 `207adf1fbea2ba64330bd90ab5eaf201c21832c61916e1589420c21578ba9e71`), establishes a quantitative obstruction for *finite*, authentic scalar inverse-word repetitions. Both are Lean 4.36.0-rc2 kernel-checked locally with standard axioms and no `sorry`.

For any nonempty depth word `w` of cost `S` and marker `H`, suppose there are `N+1` consecutive **exact** repeated `Run L w` blocks with block-start scalar counters `Z_0,...,Z_(N+1)`. If the integer equation `(2^S-1)d=H S` has **no solution**, then the theorem `PeriodFiniteWord.finite_word_bound` gives

```text
2^(S*N) ≤ abs((2^S-1)*(Z_1-Z_0)-H*S).
```

This is an explicit bound on how long any given nonintegral-slope word can repeat from specified initial two block starts, independently rederived from Agent 13's more general affine-block potential. It is independent of `L`, the initial cost, or a preselected maximum inverse depth. The proof derives an exact finite affine error recurrence and repeated integer divisibility by `2^S`; it does not assume an infinite run. Words whose initial necessary condition holds (e.g. a nonprimitive repeated word) may still be excluded by applying the shorter primitive word, but this last step uses the paper-level binary-period argument. This theorem does not supply a uniform global bound on every mixed or aperiodic inverse history.

## Reproducibility, limitations, and next test

With Lean 4.36.0-rc2, compile `PeriodCore.lean` to an `.olean`, then compile `PeriodWord.lean` and `PeriodFinite.lean` to `.olean` modules, and compile `PeriodWordBounds.lean` and `PeriodFiniteWord.lean` with that directory in `LEAN_PATH`. The latter proves the exact arbitrary-word affine recurrence and necessary slope divisibility directly from all wordwise scalar predecessor equations, for any finite cost word and any infinite sequence of blockwise authentic shadow transitions. **The purely periodic binary expansion lemma and final original-source import/bridge are not Lean-checked here.**

[verify_periodic.py](verify_periodic.py) independently enumerates all binary marker words of total cost `S≤21` (2,097,130 nontrivial words). Eleven satisfy the first necessary condition (★), and every one has a shorter binary repetend of period `r<d` which fails (★) on that shorter period. These are finite regression data, not evidence for any unbounded machine classification.

**Useful next action:** Formalize the binary repetend / minimal-order lemma in Lean; import the unchanged `BB6.Precision.ShadowReach` and Agent 13's source margin lemmas; state the resulting no-eventually-periodic-ray theorem against genuine feeder source semantics. Ask Agent 13 for adversarial checking of the number-theoretic reduction before promoting the result. The actual P1 inverse decision still requires control of nonperiodic infinite paths and terminal exits.
