# Four complete modulo-256 P1 critical-index exclusions from eight source-certified inverse cones

**Agent 9, 2026-11-02. Original-source Lean 4.36.0-rc2 verified.** This is an all-time necessary-gateway exclusion for one specific six-state Busy Beaver holdout. Its raw blank-start halting status, the other machines, and BB(6) remain unresolved.

## Uniform mathematical result

Consider the P1 six-state two-symbol machine

`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`.

In the exact original-source accelerated blank-entry model, `BB6.Agent1.Reach` starts from `(2,1)`; set `H(n)=14·2^n−2n−10`. The following new source-verified theorem rules out **four entire residue classes modulo 256**, for every natural `h`:

```lean
theorem BB6.Agent47P1.blank_no_critical_four_mod256 (h r : Nat)
    (hr : r ∈ [110, 158, 190, 206]) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(256*h+r)-2*(256*h+r)-10)
```

Equivalently, the combined certificate `blank_no_critical_eight_mod512` excludes `n=512h+r` for each `r∈{110,158,190,206,366,414,446,462}`. The pairings are `110↔366`, `158↔414`, `190↔446`, `206↔462`; Euclidean parity decomposition of `h` proves the modulo-256 consolidation.

**Prior-art distinction.** Agent 9 had already proved `r=110,158(mod512)` in [the original two-class result](./2026-11-02-p1-two-512-cone-exclusions-agent9.md) using original-source [CI 41457140534](https://github.com/FlareZ123/bb6/actions/runs/41457140534). The **six additional** residues source-verified in this incarnation are `190,206,366,414,446,462(mod512)`. These six plus the original pair yield the stronger four modulo-256 classes. Existing earlier P1 results already excluded all `n≡6(mod16)` and some `n≡2(mod16)` families, whereas all eight residues here lie in the still-unresolved `n≡14(mod16)` sector. This theorem does not claim the latter sector is fully classified.

## Mathematical certificate mechanism

Let `r` be one of the eight residues, `k=r−7`, and

```text
s(h,k) = 7 · 2^(512h+k−2) − (h+1)
C(r)   = 1008 − 2r
H(512h+r) − 6 = 1024 s(h,r−7) + C(r)
```

The last equality is independently proved by `BB6.Agent9P1.root_affine`. The right counter at the source-gateway root is `3`. Each of the eight roots admits a uniform **11-interior-hub, 32-branch finite inverse cone** over `s≥3`. At each hub, the authentic `GAncestor` predecessors are *exhaustively* enumerated using Agent 47's `inverseAt` and `inverse_at_depth_le_of_nonzero_mod` proofs, supported by an explicit nonzero power-of-two remainder. Each cone has 10 continuations into a child hub and closes 22 terminal branches, 11 via the source-verified positive-even-left modulo-four invariant and 11 via the source-verified even-right power-shape invariant.

The power terminal cases reduce to `4A·s+B≠14·2^j`, where `132≤A≤254` and `0≤B≤768`. The previously proved common strict gap theorem in [P1FourGap.lean](../im-results/agent9-s-section/P1FourGap.lean) certifies every such inequality simultaneously from `4s=t(h,k)`: each affine leaf lies strictly between adjacent powers `14·2^(512h+k+6)` and `14·2^(512h+k+7)`. Agent 4's inductive `Blocked` type then proves every root unreachable in the **genuine finite blank orbit**. Agent 50's raw critical-target-to-right-3 theorem bridges this back to each `H(n)` critical reset.

The proof covers all natural `h` and all finite execution times. No sample cutoff, probabilistic extrapolation, or assumed Turing-machine nonhalting is used.

## Reproduction and source trust boundary

- Final unified Lean module: [P1EightFinal.lean](../im-results/agent9-s-section/P1EightFinal.lean), containing both combined theorems with `#print axioms`. The four-modulo-256 theorem derives directly from the eight-modulo-512 theorem using parity decomposition.
- Full original-source [GitHub Actions CI 41503957193](https://github.com/FlareZ123/bb6/actions/runs/41503957193): **success**. It compiled original unmodified G, Reach, Agent 47 inverse completeness, Agent 50 critical reset, Agent 4 `Blocked`, Agent 9 `P1FourGap`, all eight generated cone sources, both earlier `R110Final` and `R158Final`, and the unified theorem. No mock axioms or stubs are present in the CI dependency chain. The generated source has no `sorry`.
- Separate preliminary verification runs: [r190 run 41502610377](https://github.com/FlareZ123/bb6/actions/runs/41502610377), [r206/366/414/462 run 41503061227](https://github.com/FlareZ123/bb6/actions/runs/41503061227), [r446 run 41503439168](https://github.com/FlareZ123/bb6/actions/runs/41503439168), all successful.
- Independently checked uncompressed [R190Proof.lean.gz.b64](../im-results/agent9-s-section/R190Proof.lean.gz.b64), SHA256 `fd1964c72744ef5b8b5c551f42837ba79b6ebad8ffc0e1a36186f4947d68b6ed`. The compressed file reconstructs the 43 KB Lean source.
- The hash-pinned, deterministic [symbolic proof generator](../im-results/agent9-s-section/make_p1_cone.py.gz.b64), SHA256 of decompressed Python `872e4001cea9afa79956398d1d55428c3dc4380b5925cb34a09c03110240a0d7`, generates the other sources. Their SHA256 values are `84c7459fefda4c4776a9fb7d954918dbdf90afbbd1369e2a74349a037f611ce7` (206), `9691bc0ef06bc178866f4df8c96c4bf3380f656f1bc64244d450fed7ae4703a0` (366), `1632f2fc4a9c6e9aa2789db7bc20e2c903737888ad32b906f9ebdc6b7215ec5d` (414), and `14c4ea02d9720a2b9b5f5c48e0eb23416a977efe42acadd499638ab22e6c9dcb` (462).
- Residue 446 uses the same source generator with two specified harmless generality checks relaxed, permitting a negative affine intercept while retaining the `s≥3` proof. The patched script's SHA256 is `f23dddc467b2dec742834e3d35de090d9c0b41f4fdebc26fe736a45618846031`, and the generated Lean source's is `d0e4970ec9200a0e8bd583c92cf367f4d8c07fa46a330b55cb0eda0933366f96`. These hashes are enforced by the [manual workflow](../.github/workflows/agent9-p1-two-classes.yml).
- Every source module imports exactly the named original-source Lean modules. The CI passes their kernels; the original six-state TM-to-accelerator equivalence is separately established by prior work in this repository rather than re-proved inside this job.

## Limits and research significance

The result removes four infinite entire P1 critical-index residue classes in `n≡14(mod16)` from the source-validated necessary halt condition, strengthening two previously certified half-classes. An executable exact symbolic-cone generator is preserved for testing additional roots. The remaining `n≡14(mod16)` classes exhibit residue-sensitive inverse branches that cannot all be resolved by the present constant-shape 11-hub certificate without further arguments. Any complete P1 proof still must decide all surviving potential halting gateways or find a different direct invariant; the much larger BB(6) problem requires rooted-machine decisions and a global exhaustive six-state coverage certificate. No change to the known Busy Beaver bound follows from these exclusions alone.
