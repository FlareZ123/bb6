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

## All diagonal offset rays, including even offsets (source-certified 06:09 UTC)

The [`BB429AllRayEntropy.lean`](BB429AllRayEntropy.lean) module removes even the odd-offset hypothesis above. For **every natural number** `c`, every `k≥0`, and every finite distinct list of genuinely source-root-reachable first counters `a` satisfying `b+c=2a` and `16·2^k≤a<32·2^k` for their corresponding `b`, Lean proves

\[
\boxed{\#\{a\in[16\cdot2^k,32\cdot2^k): \exists b,\operatorname{Reach}(a,b)\land b+c=2a\}\;\le\;64\cdot2^{\lfloor k/2\rfloor}.}
\]

The proof uses the exact rank phase `(5−(c mod 4)) mod4`, which allows at most `2·2^(k/2)` source-compatible reverse words at length `k`, then pairs each word with a first-counter quotient below 32. This quantifies **all offsets and both parities uniformly**, rather than a guessed subset of original blank reaches; no finite prefix or numerical assumption. Thus every fixed diagonal line `b+c=2a` has zero-density first-coordinate intersection with the authenticated #429 blank-root orbit. Uniformity in `c` refers to the explicit theorem's bound, not to simultaneous summation over all lines.

**CI accepted** [run 45122113591](https://github.com/FlareZ123/bb6/actions/runs/45122113591) with all unchanged original-source dependencies and all six new Lean modules. Exported transitive axioms of `BB429InverseWord.any_ray_dyadic_shell_bound` are **exactly `[propext, Classical.choice, Quot.sound]`**, no `sorryAx`. This stronger theorem subsumes the existence of a square-root exponent for odd rays (but not the sharper factor 32 odd-ray bound), and complements the separate q0 parameter theorem.

It still **does not prove any particular ray unreachable, decide machine #429, or bound BB(6)**; it is an all-time source-root necessary sparsity restriction.

---

## Global all-offset first-counter bound (now source-kernel-certified)

The [`BB429AllRayGlobal.lean`](BB429AllRayGlobal.lean) module strengthens the per-shell result to a single **entire-prefix** cardinal bound, with no nonconstructive asymptotic summation:

```lean
theorem BB429InverseWord.any_ray_global_dyadic_bound
    (c m : Nat) (l : List Nat) (hn : l.Nodup)
    (hl : ∀ a, a ∈ l → a < 32*4^m ∧
      (∃ b, BB429NewResidue.Reach a b ∧ b+c=2*a)) :
    l.length ≤ 256*2^m
```

This is a **uniform in `c`**, genuine-blank-root, fully quantifier-closed square-root bound over the whole integer range `[0,32·4^m)` for **every** `m≥0` (no exceptional initial parameters or finite cutoff). Proof: base `m=0` by uniqueness of integers below 32; increase `m` by one, splitting the new range into a former prefix and two dyadic shells (at `k=2m+1` and `k=2m+2`) and applying the source-certified factor-64 shell theorem. The two fresh shells contribute ≤ `64·2^m+128·2^m`; the old prefix contributes ≤`256·2^m`, within the next factor-two budget `512·2^m`.

The theorem was accepted **against unchanged repository source** in [Lean CI 45122501656](https://github.com/FlareZ123/bb6/actions/runs/45122501656), with printed transitive axioms exactly **`[propext, Classical.choice, Quot.sound]`**, no `sorryAx` or `native_decide`. This converts the preceding paper zero-density interpretation into a precise, entirely kernel-verified global finite-cardinality statement. It still does not establish emptiness of any ray or solve BB(6).

---

## Reusable source-certified arbitrary affine-feeder counting theorem

The [`BB429GenericFeederEntropy.lean`](BB429GenericFeederEntropy.lean) module takes an arbitrary nonnegative diagonal offset `c`, any integer-dyadic coefficient `D=2^s d` with `d` **odd**, any affine correction `e`, and **arbitrary** candidate functions `A(u),B(u)`. If every candidate in a finite distinct-parameter list `l` satisfies
```
u < X,             X ≤ 2^(k-s),       s ≤ k,
Reach (A u) (B u), B u + c = 2*(A u),
16*2^k ≤ A u+3,  2^k ∣ A u + D*u + e,
```
then the Lean theorem `generic_feeder_cardinality_bound` proves
```
l.length ≤ 2*2^(k/2)
```
for **all** `k,c,s,d,e,X,A,B,l` meeting those conditions. It does **not** assume that the candidate functions have a particular exponential closed form: only the stated necessary divisibility is used. The proof takes a legitimate length-k inverse word for each genuine blank-reachable candidate, applies source-proved fixed-word first-counter congruence, cancels the exactly known `2^s` part of the affine coefficient, and injects the parameters into the regular inverse-word language. This is a transferable counting theorem, not another numerical residue table.

**Unchanged source Lean 4.36.0-rc2 [CI 45123217034](https://github.com/FlareZ123/bb6/actions/runs/45123217034) passed**, with exported transitive axiom list **`[propext, Classical.choice, Quot.sound]`** only, no `sorryAx`. The original q0 theorem is a more sharply constants-adapted specialization (the generic theorem's factor 2 is unnecessary for its particular initial phase).

---

## Branch-9 exceptional S-parent family: full-interior square-root entropy

**Lean-checked result.** \`BB429Branch9FeederEntropy.lean\` proves \`branch9_side_feeder_entropy\`. Fix \(t,r,q,K\in\mathbb N\) with \(t\ge5\), \(r<4\), \(t+14=r+4q\), and \(K\ge1\). For a distinct finite list \(l\), suppose every \(v\in l\) satisfies

\[
K\le v<2^K,\qquad t+3\le N(v),\qquad
\operatorname{Reach}(A(t,q,r,v),B(t,q,r,v)),
\]

where

\[
J(v)=4v+r,\quad N(v)=8\cdot2^{J(v)}+J(v)-11,
\quad k(v)=2\cdot2^{J(v)}+v-q,
\]

\[
A=12\cdot2^N+6\cdot2^t-6\cdot2^J-8-3k,
\qquad
B=24\cdot2^N+5-12\cdot2^t-12\cdot2^J-6k.
\]

Then

\[
\boxed{|l|\le 2^{\lfloor K/2\rfloor}.}
\]

The proof applies the reusable affine-feeder cardinality theorem with the exact branch-9 parameters. The offset is (c=24\cdot2^t-21\equiv3\pmod4), so (\operatorname{anyRayPhase}(c)=2) is even. The even-phase word language has exactly (2^{\lfloor K/2\rfloor}) words, eliminating the factor of two in the phase-uniform bound. Its key identities and bounds are:

- \(t+3\le N\), together with \(t+14=r+4q\), implies \(q\le2\cdot2^J+v\); the natural subtraction defining \(k\) is therefore exact.
- With \(C=6\cdot2^t+3q-8\), the affine identity is
  \(A+3v=(12\cdot2^N-12\cdot2^J)+C\).
  Since \(J\ge K+2\) and \(N\ge J+1\), the first term is divisible by \(2^K\). The correction \(e=(C+1)2^K-C\) makes \(A+3v+e\) divisible by \(2^K\).
- The ray offset \(c=24\cdot2^t-21\) satisfies \(B+c=2A\), and \(t+3\le N\) gives \(c\le2A\).
- The high-counter condition \(16\cdot2^K\le A+3\) follows from the same affine identity and exponent separation.

This removes the earlier draft's artificial restrictions \(t\le K\) and \(q\le v\). The estimate now covers every \(t\ge5\) in the actual interior range \(t+3\le N(v)\), for each fixed \(t,r,q\). It is a parameter-sparsity theorem, not an exclusion of the branch or a BB(6) solution.

**Validation:** the existing manual workflow \`.github/workflows/agent39-429-1021-source.yml\`, input \`proof_target=entropy\`, passed on 2026-11-23 (run [45181698589](https://github.com/FlareZ123/bb6/actions/runs/45181698589), which also checks the sharper even-phase specialization). The Lean source ends with \`#print axioms branch9_side_feeder_entropy\`; no \`sorry\` or \`admit\` was introduced in this module.

### Additional finite-sieve observation (not yet Lean-certified)

A separate BigInt reimplementation of the existing \`agent30-429-branch9-zero-feeder/side_branch_sieve.js\` predicates and inverse-parent rules reproduces the reported depth-16 and depth-18 counts (3068 and 4962), and extends the computation to depth 20: **12088** surviving residues modulo \(2^{26}\). Already at depth 4, the surviving low-seven-bit classes shrink from the depth-2 eleven-class set to

\[
\{9,11,25,41,43,57,75,107\},
\]

eliminating \(89,105,121\pmod{128}\). This is an exact finite computation, not yet a kernel-checked theorem. The three eliminated classes fail at the next inverse levels under existing root constraints (\`even16\`, \`odd8-7b8\`, \`odd8-1-3\`, and \`odd32-5\`); the result suggests that a short extension of the depth-2 Lean proof may strengthen the branch-9 residue gate from eleven classes to eight.

**Exponent-scope caveat:** the sieve starts from the ghost pair \((-8-3k,5-6k)\), whereas the actual branch-9 side-parent coordinates differ from it by \(12\cdot2^N+6\cdot2^t-6\cdot2^J\) and \(24\cdot2^N-12\cdot2^t-12\cdot2^J\). To transfer the depth-\(d\) sieve at modulus \(2^{d+6}\), sufficient conditions are \(t\ge d+5\), \(J\ge d+5\), \(N\ge d+4\). Thus the depth-4 eight-class observation requires \(t,J\ge9\) and \(N\ge8\); the depth-20 count requires \(t,J\ge25\) and \(N\ge24\). These stronger exponent thresholds are separate from the full-interior entropy theorem's \(t\ge5\) scope. Do not apply the eight-class gate to the small-\(t\) part of that theorem without a stronger congruence argument.

The one-bit-per-level precision budget has a useful algebraic explanation. Let \((\Delta x,\Delta y)\) be the difference between an actual side-parent state and its ghost pair. If \(2^m\mid\Delta x\) and \(2^{m+1}\mid\Delta y\), then the inverse maps transform the error pair as follows:
- F: \((\Delta x,\Delta y)\mapsto(\Delta x/2,\Delta x+\Delta y)\);
- S/E: \((\Delta x,\Delta y)\mapsto((4\Delta x+\Delta y)/4,\Delta y/2)\).

In either case the new first-coordinate error is divisible by \(2^{m-1}\), while the second-coordinate error is divisible by \(2^m\). Thus the one-bit gap is preserved and each inverse level consumes at most one bit of initial precision. Starting with congruence modulo \(2^{d+6}\) therefore preserves the modulo-64 root tests through \(d\) levels. This algebraic invariant explains the script's modulus budget; a Lean proof of the transfer invariant should accompany any future formal D4 theorem.

See the Agent30 sieve script for the underlying predicates and transition rules.

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

