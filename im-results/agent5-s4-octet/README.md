# S4 triple-drain and 16-period genuine-root prefix reduction

**Agent 5, 2026-11-05. Research-stage source-verification dossier.** All mathematics here concerns the six-state, two-symbol S4 machine `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF` and the exact original-source accelerated blank configuration. **No halting/nonhalting decision for S4 or BB(6) follows.** External novelty of the internal reductions is unreviewed; retain this in `im-results/`.

## Source-connected halting-equivalent triple drain

Use the exact compact source-shaped transducer `F`, initialized at stack `[42,12,8,5]`, as connected to the original Cryptids machine by Agent 5's [raw source bridge](../agent5-s4-source-bridge/README.md) and [native compact bridge](../agent5-s4-length/README.md). Define `W([])=0`, `W(b::T)=b+1+2W(T)`; let `H(a,L)` be the all-input recursive odd-drain function in [S4PowerGate.lean](../agent5-s4-length/S4PowerGate.lean), and `G(c,R)` the corresponding positive additive-head drain:

```text
G(c,[])       = H(c-1,[])
G(c,b::S)     = H(b+c,S)
Q(R)          = G(107,R) >>= (U => map(bumpN(253), G(148,U)))
P(S)          = G(509,S) >>= (U => G(290,U) >>= G(219))
```

Here `Q` represents eight consecutive exact compact `F` returns with a fixed leading pair, and `P` represents two `Q` returns after an exact four-`Q` initial sequence. On all finite input stacks `S`, the new exact unbounded identities are:

```text
Q(471::S) = map(472::, G(509,S))
Q(472::S) = G(290,S) >>= (U => map(471::, G(219,U)))
Q²(471::S) = map(471::, P(S)).
Q⁴([481,133,28,25]) = [471,301,650,645,322,163,160].
```

Consequently the **unchanged original six-state raw S4 machine halts from blank tape if and only if**:

```text
there exists n≥0 for which P^n([301,650,645,322,163,160]) = none.
```

The `P` system is a partial infinite-state map; the criterion does not assert that such an `n` exists. Proofs are [S4Toggle.lean](S4Toggle.lean) and [S4RawToggle.lean](S4RawToggle.lean); true original-source GitHub Actions [run 41965231342](https://github.com/FlareZ123/bb6/actions/runs/41965231342) passed the complete imported module chain and `#print axioms` recorded only standard Lean axioms. An earlier [run 41964574608](https://github.com/FlareZ123/bb6/actions/runs/41964574608) failed solely because the predecessor source was compiled without an importable `.olean`; the workflow was corrected and the later successful run supersedes it.

## Uniform four-mode normal forms

For all finite `S`, independent of root reachability:

```text
P(283::S) = map(282::, G(1023,S))
P(281::S) = map((U => 283::bumpN(281,U)), G(739,S))
P(280::S) = G(395,S) >>= (U => map(281::, G(624,U)))
P(282::S) = G(396,S) >>= (U => G(343,U) >>= (V => map(280::,G(281,V))))
```

[S4TogglePhases.lean](S4TogglePhases.lean) gives direct quantified Lean proofs. [S4ToggleGates.lean](S4ToggleGates.lean) derives exact power-of-two failure descriptions for the four modes via `G(c,S)=none ↔ W(S)+c=2^k`. These gates are *conditional* on the actual deeper suffix. The four-mode decomposition is a way to expose the remaining indefinite reachability problem; it cannot be used to assume the deeper suffix is arbitrary along the true orbit.

## Genuine-root prefix dynamics

Let `h(c,b)=(b+c)/2+2` for even `b+c`, and `h(c,b)=(b+c)/2` for odd `b+c`. On a successful `P(b::S)` the new leading head is `f(b)=h(219,h(290,h(509,b)))`. From the true `P` seed, the first head after the first successful transition is **283,282,280,281** periodically, provided each transition survives. See [S4ToggleHead.lean](S4ToggleHead.lean), original-source CI [41965231342](https://github.com/FlareZ123/bb6/actions/runs/41965231342).

More precisely, for every successful `P( a::b::S )` with `a∈{280,281,282,283}`, its first two digits are calculated solely from `(a,b)`:

| Current a | Next two-digit prefix |
| --- | --- |
| 280 | `(281, h(624,h(395,b)))` |
| 281 | `(283, h(739,b)+281)` |
| 282 | `(280, h(281,h(343,h(396,b))))` |
| 283 | `(282, h(1023,b))` |

[S4TogglePair.lean](S4TogglePair.lean) proves the all-input two-digit step and the *rooted* exact 16-cycle: `P^7([301,650,645,322,163,160])=[280,397,1227,3564,1195,2422,323]`, and for every `n≥0` for which `P^(7+n)` survives, its first two digits are `pairRun(n)`; `pairRun(n+16)=pairRun(n)` for **all natural n**. The 16-step pair cycle begins:

```text
(280,397), (281,513), (283,909), (282,968),
(280,399), (281,511), (283,908), (282,965),
(280,398), (281,512), (283,906), (282,964),
(280,396), (281,509), (283,907), (282,967).
```

This is a condition-on-survival theorem with no finite-horizon cutoff, and does not imply that every deeper tail remains nonhalting. The `S4TogglePair` original-module CI check is pending; the proof was locally checked under Lean 4.36.0-rc2 with faithful source-shaped stand-ins and standard axioms only. The root `P^7` equality was kernel-evaluated with `simp`, with no axioms beyond standard Lean.

## Verification and frontier

All new scripts are deliberately incorporated into the existing **manual-only** `.github/workflows/agent7-s4-original.yml` rather than a per-commit workflow. The original import is Cryptids revision `c86f15861709b76042998c5211c7b2f83991621b`; successful CI is the boundary for direct-source verification. The previous S4 tail-gate arithmetic, stack-length laws and weighted-growth theorems are reused, not claimed as new discoveries.

The remaining decisive task is an all-time, **history-sensitive whole-tail** exclusion or actual hit for one of the exact `G` power gates on the genuine `P` orbit. A 16-period prefix is too little on its own because matching finite prefixes can admit synthetic terminal suffixes. Avoid repeating finite traces or conflating a necessary gate with its reachability. Rigorous completion of this individual root would still leave universal six-state BB(6) coverage open.
