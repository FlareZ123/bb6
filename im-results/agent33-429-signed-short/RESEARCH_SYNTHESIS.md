# Authentic BB429 last-reset inverse constraints and self-similar feeder

**Current status (2026-11-28 UTC).** All results below refer to machine #429 in the shared six-state BB(6) frontier. The exact Busy Beaver value remains open. **Distinguish** (a) the genuinely blank-start `BB429.run` source orbit, (b) possible nonblank accelerator trajectories, and (c) algebraic signed-inverse overapproximations. An inverse branch may be a valid ordinary source transition without its input ever being reachable from the blank tape.

## 1. Uniform necessary conditions on blank-reachable last-reset inputs

The source's exact near-terminal line is `w+3=2*u`. For the two still-important first-counter classes:

- **13-line:** `u=32q+13`, `w=64q+23`. The source-level theorem `BB429Forced13More.rooted_13_q_mod16` proves, **for all q≥16**, that `Reach u w` forces `q mod16 ∈ {4,12,13}`.
- **15-line:** `u=32q+15`, `w=64q+27`. `BB429Forced15More.rooted_15_q_mod8_necessary` proves, **for all q≥16**, that `Reach u w` forces `q mod8 ∈ {0,3,4,6,7}`.

These were built by extracting one or a small number of true reachable predecessors using the existing source-proved `BB429NewResidue.odd_back/even_back`, then using the source-proved unconditional gates `BB429RootEven8.rooted_positive_even_eight`, `BB429RootMod16.rooted_not_7_7` and `BB429Mod8.Allowed` to eliminate alternatives. No finite history limit, signed model, or bound on the unknown halting time is used.

**Kernel evidence:** `BB429Forced13.lean` passed pinned Lean 4.36.0-rc2 CI [46098071239](https://github.com/FlareZ123/bb6/actions/runs/46098071239). Both `BB429Forced13More.lean` and `BB429Forced15.lean` completed compilation, with exported axioms restricted to `[propext, Classical.choice, Quot.sound]`, in [46098289073](https://github.com/FlareZ123/bb6/actions/runs/46098289073). `BB429Forced15More.lean` completed compilation with the same axiom list in [46098533877](https://github.com/FlareZ123/bb6/actions/runs/46098533877). The *entire* latter two jobs failed **afterward** in a separate last-reset composition module; do not mistake those job-level failures for failures of the individual named accepted source theorems. The follow-up composition `BB429LastResetImproved.lean` remains under repair/re-check and must not be cited as accepted yet. The original upstream Cryptids highLevelNext wrapper `BB429NativeCylinder.lean` is separately pending CI.

For branch13 the exact last-reset equation requires `n=63+128k` and
`q+(3k+2)=3*2^(n-5)`. For branch15, it requires `n=103+128k` and
`q+(3k+3)=3*2^(n-5)`, for n≥18. Thus once `BB429LastResetImproved.lean` is compiled, genuine branch13 last resets can only have `k mod16 ∈ {6,11,14}`, and genuine branch15 only `k mod8 ∈ {2,3,5,6,7}`. These restrictions do not empty either candidate family.

## 2. Why the surviving lines demand more than deeper residue tables

New exact source-affine four-transition candidate, in
[`BB429UnboundedFeeder.lean`](BB429UnboundedFeeder.lean), currently a **Lean proof candidate pending CI correction**:

```text
anchor(z,V) := (8z+15, 8z+1536V+27), z>=0, v>=1.

source forward:
anchor(z+960v-1, v) --S--> (...) --F--> (...) --E--> (...)
                             --F--> anchor(z,16v).

Therefore run(4, anchor(z+960v-1,v)) = anchor(z,16v).
```

Each edge is an authentic `BB429.next` edge with natural-number input and output; no signed negative state. This defines a renormalization of the offset parameter `V ↦ V/16` in *backward* time and a shift `z↦z+960v-1`. The inverse block's intermediate states are exactly

```text
A0 = (8z+15,          8z+24576v+27)
A1 = (4z+6,          16z+24576v+42)
A2 = (8z+6144v+13,   8z+12288v+21)
A3 = (4z+3072v+5,   16z+18432v+34)
A4 = (8z+7680v+7,    8z+9216v+19)
```

where A0 is the target and each A(i+1) is its actual predecessor. Every state on the block satisfies all currently used universal blank-root modular necessary gates (though they are **not** thereby shown blank-reachable). At `q=3*16^(N+1)`, choose `z=4q=192*16^N`, `V=16^N`; A0 is precisely the **15 odd-reset line** `(32q+15,64q+27)`. Iterating N source-correct blocks produces a genuine nonblank-start forward trajectory of length 4N ending at that very line. A uniform finite inverse-depth cutoff cannot eliminate all such q through only local transition legality. It remains possible that a stronger global *blank-start* invariant excludes these trajectories, and the construction alone says nothing about actual #429 nonhalting.

The broader earlier `BB429Tower.inverse_tower` from Agent1 already certifies unbounded actual-source preimage depth for complementary 9/17 families and a synthetic 9-halting gate. This new 15-line FEFS tower, if checked, is targeted at a different source last-reset family and should be compared to that prior theorem rather than misrepresented as the first instance of an unbounded inverse depth phenomenon.

## 3. Genuine unsolved mathematics

The 13-line residual classes `q≡4,12,13 (mod16)`, 15-line residual classes `q≡0,3,4,6,7 (mod8)`, the 29-line source last-reset family, and other machine #429 feeders remain unresolved. The root-start predicate cannot be replaced by arbitrary predecessor existence. The known positive rank drift means every fixed finite target has only finitely many ancestors; the renormalization ray escapes by allowing the target's size to grow with desired depth. This observation does not contradict the rank theorem. More powerful progress likely needs a global separator invariant, return-map recurrence, or proof of impossibility for the exact exponential-minus-linear `q(n,k)` candidates, not another fixed-depth 2-adic table.

## Reproduction

- Pinned source-only modular proofs: `.github/workflows/agent33-429-five-shift.yml`, manually dispatch `target=root-short`.
- FEFS nonblank source ray and signed auxiliary closures: same workflow, `target=signed-short`.
- Unmodified upstream original Cryptids semantic transport: `.github/workflows/agent33-429-native-24.yml` (large dependency closure), check final new native source section.
- Existing signed-compressed all-parameter family closures: `Branch1315Finite.lean`, [CI 46097084000](https://github.com/FlareZ123/bb6/actions/runs/46097084000); signed-only result, not blank-root exclusion.
