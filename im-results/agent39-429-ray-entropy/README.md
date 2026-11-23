# BB429: square-root sparsity of the branch-10 q0 candidate parameters

**Mathematical status:** **kernel-certified quantified finite-cardinality theorem for the unchanged repository's BB429 blank-root accelerator**, Lean 4.36.0-rc2 [manual source CI 45121153859](https://github.com/FlareZ123/bb6/actions/runs/45121153859), exact dependency closure and final axiom profile `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Its all-X square-root bound and zero-density interpretation follow by elementary logarithm arithmetic from that certificate. This is a nontrivial necessary-condition restriction on one authentic-root feeder family, **not** a blank-machine decision, an upper bound on BB(6), or a new halting witness. External novelty has not been established.

## Universal odd-offset ray theorem (source-verified 2026-11-23 06:06 UTC)

The q0 theorem above is now accompanied by a **strictly more general original-source mathematical restriction**. The Lean module [`BB429OddRayEntropy.lean`](BB429OddRayEntropy.lean) proves `BB429InverseWord.odd_ray_dyadic_shell_bound`:

```lean
∀ c k : Nat, c % 2 = 1 →
  ∀ l : List Nat, l.Nodup →
  (∀ a ∈ l, 16*2^k ≤ a ∧ a < 32*2^k ∧
    ∃ b, BB429NewResidue.Reach a b ∧ b+c=2*a) →
  l.length ≤ 32 * 2^(k/2)
```

Thus for **every fixed positive or zero odd offset `c`**, all first-coordinate values of truly blank-reachable `BB429` sections on **the entire diagonal affine ray** `b+c=2a` obey a square-root upper count within each dyadic shell `[16·2^k,32·2^k)`. This implies the set of such first-coordinate values has zero natural density, and it is **not** restricted to the branch-10 q0 exponential specialization. The proof constructs the genuine original-source reverse word for every input, derives its correct mod-four rank phase (0 or 2 according to `c mod4`), counts exactly `2^(k/2)` legal words, and injects each source counter into `(word, floor(a/2^k))`. The latter quotient is less than 32 on the stated shell, giving the finite pigeonhole count. No hand-picked finite reachability cutoff, bounded simulation, or assumption that the synthetic inverse language is fully reachable occurs.

Complete original-repository-source Lean 4.36.0-rc2 **[CI 45121805424](https://github.com/FlareZ123/bb6/actions/runs/45121805424) passed**, importing and compiling all of `BB429Rank`, `BB429Mod8`, `BB429NewResidue`, and all five new Agent39 modules. The printed final theorem's transitive axioms are exactly **`[propext, Classical.choice, Quot.sound]`**, no `sorryAx` or `native_decide`.

This is a **sparsity theorem, not a nonhalting theorem**: it leaves countably infinite possibilities for every nonterminal ray. In particular `c=1` is the special halting line, whose authentic blank orbit contains at most one state anyway; the structural result is more interesting for nonhalting intermediate odd offsets such as `c=13`. It makes no assertion that the remaining sparse necessary rays are actually reachable.

---

## Main result: a square-root, not merely modular, sieve

Let `next`, `run` and the genuine blank section root `(0,0)` be the exact `BB429` definitions of [Agent 5's authenticated accelerator](../agent5-429-rank/BB429Rank.lean), with source inverse lemmas [`BB429NewResidue.odd_inverse/even_inverse`](../agent6-harmonic429/BB429NewResidue.lean). Define
`Reach(a,b) := ∃ t, BB429.run t (0,0) = some (a,b)`.
The open branch-10 q0 feeder has the specific source-derived parametrization
\[
 n(u)=23+32u,\qquad A(u)=13\cdot2^{n(u)}-24u-19,\qquad B(u)=2A(u)-13,
 \quad u\ge0.
\]
See [the existing q0 derivation](../agent1-429-q0-23-7/Q0ResidueCoverage.md). Let `U = {u ∈ ℕ : Reach(A(u),B(u))}`.

**Theorem (Lean source-connected, quantitative).** For every integer `X ≥ 2`, putting `k=⌈log₂ X⌉+3`,
\[
 \#\{u<X:u\in U\}\;\le\; k+2^{\lfloor k/2\rfloor}
 \;<\; \log_2 X+4+4\sqrt X.
\]
In particular `#(U∩[0,X))=O(√X)`, hence **the surviving q0 candidate parameter set has zero natural density**. This is a restriction on candidate *parameters*, not a proportion of six-state machines, an authentic run-time bound, or a proof that any candidate is reachable.

## Proof: every second inverse letter is forced

Set `R(a,b)=2a+b`. For every high-output target `a≥13`, the complete source inverse equations allow only:

| label | predecessor `(x,y)` | rank decrease |
| --- | --- | ---: |
| F | `a=2x+3, y=b+a` | 3 |
| S | `4x+26=4a+b, 2y=b+4` (odd `a`, `b≡2 mod4`) | 11 |
| E | `4x+14=4a+b, 2y=b` (even `a`, `b≡2 mod4`) | 7 |

Each inverse rank cost is `3 mod4`. For a target on the ray `b=2a-13`, its initial rank is `4a-13≡3 mod4`. Therefore after `j` inverse steps, independently of the choices, `R_j≡3+j (mod4)`. If `j` is even, `R_j` and `b_j` are odd, so only F is possible. At `j≡1 mod4`, `R_j≡0`, so the only candidate labels are F/S (E would force both even `a_j` and `b_j≡2 mod4`, incompatible with rank 0). At `j≡3 mod4` the options are F/E. Hence all length-`k` inverse words belong to the regular language
```
F (F|S) F (F|E) F (F|S) F (F|E) ...
```
and there are at most `2^⌊k/2⌋` words.

For a fixed word `w`, write `a_j=(C_j a_0+D_j)/2^j` for its `j`-th predecessor first coordinate. Initially `C_0=1,D_0=0`. On F, `C_{j+1}=C_j`; on S or E, since `R_j=4a_0-13-δ_j` with `δ_j` the accumulated rank costs,
`a_{j+1}=a_j/2+a_0-(13+δ_j+c_w)/4`
where `c_w=26` (S) or 14 (E). Thus `C_{j+1}=C_j+2^{j+1}` on S/E. For these steps `j` is odd and `13+δ_j+c_w` is even, so all constants `D_j` are integers. **Every `C_j` is odd.** Since `a_k` is an integer, `2^k | (C_k a_0+D_k)`; an odd `C_k` is invertible modulo `2^k`. Consequently **one fixed inverse word admits at most one initial `a_0` residue modulo `2^k`**.

The Lean proof uses the following coefficient-free form: two inverse histories carrying the same word, from targets with the same ray offset, have
`2^j(a_j-a'_j)=C_j(a_0-a'_0)` with odd `C_j`. The F step preserves `C_j`; S/E adds `2^{j+1}`. Thus `a_0≡a'_0 mod2^k`. This quantified uniqueness, the exact branch costs, and the mod-four phase restrictions are kernel-checked in [the Lean arithmetic core](BB429InverseWordCore.lean). The [language module](BB429InverseWordLang.lean) proves an exact regular-word count and a bridge from pairs of source inverse chains; it never assumes that every syntactic inverse word occurs on the blank orbit.

## Unbounded high-counter prefix and the q0 count

Any legitimate predecessor of a target with `a≥13` satisfies `a≤2x+3`, so `a+3≤2(x+3)`. If `a_0+3≥16·2^k` and the target is blank-reachable, following its actual rooted predecessors for `k` steps keeps every first counter at least 13 (the genuine root has first counter zero). Thus its first `k` inverse labels are governed by the exhaustive high-output grammar above. For each fixed `k`, all sufficiently large reachable points on `b=2a−13` lie in at most `2^⌊k/2⌋` residue classes modulo `2^k`, giving zero natural density for the ray itself.

For `u≥k`, the elementary inequality `24u+19≤2^{23+32u}` implies `A(u)≥12·2^{23+32u}≥24·2^k`. Thus every `u≥k` in `U` admits a length-`k` inverse word. Since `n(u)≥k`, `A(u)≡−24u−19 mod2^k`. Two such parameters with the same word therefore obey `2^k | 24(u-v)`; since `24=8·3` with `3` odd, `u≡v mod2^{k-3}`. For `k=⌈log₂X⌉+3`, `2^{k-3}≥X`, hence **at most one** `u∈[k,X)` per word. There are fewer than `k` exceptional small parameters, yielding the asserted bound. No infinite trajectory simulation or finite-sample-to-universal extrapolation is involved.

## Machine-checked theorem and evidence boundary

The exact exported result in [`BB429InverseWordCount.lean`](BB429InverseWordCount.lean) is:

```lean
theorem BB429InverseWord.q0_candidate_cardinality_bound
    (X k : Nat) (hk : 3 ≤ k) (hX : X ≤ 2^(k-3))
    (l : List Nat) (hn : l.Nodup)
    (hl : ∀ u, u ∈ l → u < X ∧ Q0Candidate u) :
    l.length ≤ k + 2^(k/2)
```

Here `Q0Candidate u` explicitly means there exist original-source accelerated blank-root-reachable `a,b` with `b+13=2*a` and `a+24*u+19=13*2^(23+32*u)`. This avoids any finite-run cutoff or truncated subtraction. The proof establishes source-connected `source_step_legit`, all-depth `source_high_prefix`, exact parity-language constraints, odd-slope uniqueness, modular parameter injection, and the final cardinal bound, all compiling against **unchanged** `BB429Rank`, `BB429Mod8`, `BB429NewResidue`. Verified exact source closure in [CI 45121153859](https://github.com/FlareZ123/bb6/actions/runs/45121153859) (head SHA `c7a9d3454a4d3745f104e5d6bc55b7be87057634`) with exported axiom list **exactly** `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, `native_decide`, or extra axioms. The first source-root and abstract-core check passed separately in [CI 45119840927](https://github.com/FlareZ123/bb6/actions/runs/45119840927).

To apply the theorem at arbitrary `X≥2`, choose `k=⌈log₂ X⌉+3`; then `X≤2^(k-3)` and its conclusion gives the displayed `O(√X)` bound. The asymptotic simplification is a paper corollary, not itself a new Lean theorem. The bridge from `BB429.run` to the six-state Turing-machine table is pre-existing repository source work: this CI directly imports the exact genuine blank-root accelerator definitions, but does not independently rebuild the upstream Google DeepMind raw-machine formalization.

The quantitative sparsity still allows infinitely many exceptional parameters and cannot close branch-10 q0, the competing inverse branches, #429, or BB(6). A consequential next question is whether the surviving dyadic inverse language intersects the very special exponential-affine q0 ray at **any** parameter, not how many low-modulus residues can be filtered.

