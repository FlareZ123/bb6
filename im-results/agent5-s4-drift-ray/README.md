# S4 uniform infinite drifting cylinder

**Claim and status (6 November 2026; source-checked).** For the exact finite-list S4 three-drain map `P` from [S4 triple-drain reduction](../agent5-s4-octet/README.md), every list in the four-digit cylinder

```text
[284,1646,1026,x] ++ S,     x ∈ ℕ, S any finite list of natural digits
```

survives indefinitely. Each return leaves the first three digits and entire suffix `S` unchanged while increasing the fourth digit by exactly 1024. This is a genuine **all-input, all-time symbolic nonhalting result for the reduced transducer**. It is **synthetic**: the known authentic S4 blank-tape reduced seed is `[301,650,645,322,163,160]`, and no reachability of the displayed cylinder from that seed has been established. Neither this theorem nor the preceding reduction decides S4 from blank tape or BB(6). Its external novelty remains to be assessed.

## Exact theorem

Define `G(c,[]) = H(c-1,[])` and `G(c,b::S)=H(b+c,S)`, where the original compact S4 odd-drain `H` is given in [S4PowerGate.lean](../agent5-s4-length/S4PowerGate.lean). Define

```text
P(T) = G(509,T) >>= G(290) >>= G(219).
prun(0,T)=some T;
prun(n+1,T)=prun(n,T) >>= P.
```

The new [Lean module](S4DriftRay.lean) proves, for **all** `n,x : Nat` and `S : List Nat`:

```text
P ([284,1646,1026,x] ++ S)
  = some ([284,1646,1026,x+1024] ++ S),

prun n ([284,1646,1026,x] ++ S)
  = some ([284,1646,1026,x+1024*n] ++ S),

¬∃n, prun n ([284,1646,1026,x] ++ S) = none.
```

The first identity follows by finite unfolding of the three deterministic odd-drain stages. None of those stages needs to inspect beyond the fourth digit, regardless of `x` and the suffix. Induction gives the second identity; the third follows from the explicit `some` result.

This is a parameter-uniform, infinite nonhalting cylinder rather than a single long finite simulation. The fourth digit grows without bound; the complete stack also changes without ever repeating, although every suffix `S` is preserved. It complements the [all-depth prefix projection](../agent5-s4-prefix-causal/README.md), which gives conditional finite-prefix dynamics without guaranteeing survival.

## Reproducibility and provenance boundary

- `S4DriftRay.lean` imports the repository's unchanged `S4Toggle` and uses the same `P` and `prun` definitions as the existing source-certified S4 reduction; it adds no axioms or new semantics.
- Local Lean **4.36.0-rc2** compiled the proofs against a definition-matching copy of the three-drain interface, with `#print axioms` yielding only `[propext, Quot.sound]`. The source proof uses `simp [P,G,H]` and an arithmetic induction.
- The exact checked-in theorem passed the existing **manual-only** [original-Cryptids source CI workflow](../../.github/workflows/agent7-s4-original.yml), [run 42287516418](https://github.com/FlareZ123/bb6/actions/runs/42287516418), at pinned repository revision `1cffc9fc95cc16cf93bfde8c4cce28878cf713cc`. The run built the unmodified original Cryptids machine acceleration at `c86f15861709b76042998c5211c7b2f83991621b`, compiled the complete S4 adapter chain, then compiled `S4DriftRay.lean` immediately after the real `S4Toggle.olean`; the job's full source-check step and all other steps succeeded. This validates compilation and axioms against the genuine imported source, beyond the local stand-in check. The established original raw-machine to `P` connection was separately certified in [run 41965231342](https://github.com/FlareZ123/bb6/actions/runs/41965231342).
- The source of `H` is [S4PowerGate.lean](../agent5-s4-length/S4PowerGate.lean); the original public Cryptids revision is `c86f15861709b76042998c5211c7b2f83991621b`.

## Scientific boundary and next test

This cylinder is separated from the authentic reduced seed by different leading digits. The existing [rooted 32-phase triple theorem](../agent5-s4-octet/README.md) fixes the authentic surviving orbit's first digit inside `{280,281,282,283}` after its transient. Thus that authentic phase cannot enter this `284`-leading cylinder. The new result does not bridge the unresolved halting gates.

The useful next question is whether this drift pattern belongs to a wider structural class of forward-closed parametric cylinders, and whether any analogous **history-respecting** invariant controls the authentic `280..283` phases. Prior inverse-collision work already shows that general synthetic reachability has large branching, so only seed-sensitive proofs can decide the genuine root. See [S4 inverse collisions](../agent5-s4-inverse-collision/README.md) and the [S4 research board](../../research/BOARD.md).
