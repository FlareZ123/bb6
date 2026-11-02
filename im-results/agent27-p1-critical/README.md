# Agent 27: source-certified infinite P1 exclusion, n ≡ 206 (mod 256)

**Status (2026-11-02):** Fully quantified, kernel-verified *intermediate* reachability theorem for the actual published P1 accelerated blank entry. This does not decide the six-state holdout, establish a Busy Beaver bound, or determine BB(6). External mathematical novelty has not been independently assessed. Accordingly this record belongs to `im-results/`.

Machine: `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`. Certified accelerated blank entry: `(2,1)`.

## Main theorem

```lean
BB6.Agent27.blank_no_critical_206_mod256 (k : Nat) :
  ¬BB6.Agent1.Reach 2
    (14*2^(256*k+206)-2*(256*k+206)-10)
```

The statement uses the **unmodified, original** `BB6.Agent1.Reach` relation. The terminal predecessor reduction is Agent 50's kernel-proven `critical_target_implies_three`; the relevant pre-halting odd-right configuration is `(512t+84,3)`, where `t=7·2^(256k+198)−(k+1)` is at least 20.

## Mathematical certificate

The proof exhaustively classifies `GAncestor` inverses of eleven odd-right hubs. Repeated backward reachability is provided by Agent 50's complete `positive_G_feeder`. The eleven hubs, as symbolic functions of `t`, are:

```text
(512t+84, 3)
  (256t+36,256t+49)
    (128t+12,384t+71)
      (64t,448t+81)
      (400t+56,112t+21)
      (456t+64,56t+11)
  (448t+68,64t+13)
    (224t+28,288t+51)
      (112t+8,400t+69)
      (312t+40,200t+35)
  (480t+72,32t+7)
```

Every other branch contradicts the global reachable-even-left congruence (positive-right even-left states have first coordinate either 2 or 0 modulo 4), or requires an even-positive hub whose first coordinate plus 12 equals `14·2^j`. Exactly eleven candidate power expressions occur:

```text
392t+66, 434t+70, 370t+60, 484t+80, 320t+58,
398t+64, 334t+54, 412t+68, 368t+64, 376t+64, 496t+86.
```

For every `k`, each lies between `320t+58` and `496t+86`, and Lean proves the strict bound

```text
14·2^(256k+205) < 320t+58 ≤ 496t+86 < 14·2^(256k+206).
```

The interval lies between consecutive values `14·2^j`, hence all eleven power conditions are impossible. Exhaustive symbolic `GAncestor` classifications, parity constraints, branch elimination, and the final reachability theorem are proved by kernel-checked induction, arithmetic, and exact power bounds. No `sorry`, `native_decide`, finite search limit, or new axiom is used.

## Verification and reproducibility

- **Successful unmodified-source manual CI:** [run 41404260662](https://github.com/FlareZ123/bb6/actions/runs/41404260662), head commit `a2f8f153054b46ed46dd8ec58dd1909630e25296`, 2026-11-02 07:08 UTC.
- The workflow `/.github/workflows/agent27-p1-206-verify.yml` reconstructs this exact 552-line proof, checks its SHA-256, compiles eight **unmodified** source files in order (`GParity,GInverse,PosEvenForm,ResetGate,P1Triple,P1ResidualArithmetic,P1ResidualReach,P1Gate`), and then compiles `P1Critical206.lean`.
- Exact source: [`P1Critical206.lean.xz.b64`](./P1Critical206.lean.xz.b64), XZ-compressed Base64 of UTF-8 source; decompressed SHA-256 `1248b72b2ccb65838cd0ff1e9b12e69872d43276f9ec7f9fd40b07cf542db81c`.
- The CI log for the final theorem reports **`[propext, Classical.choice, Quot.sound]`** and no `sorryAx`. Warning-only unused parameter messages do not affect proof success.
- The original Turing-machine/accelerator semantic bridge is separately verified in Agent 19's previous CI; the current run independently checks the theorem in authentic Agent 1 `Reach`. A newly named one-shot original-machine composition theorem has not yet been checked here.

The novelty relative to *this repository* is exclusion of the previously untreated family `206(mod256)`, a strict subfamily of the difficult `14(mod16)` critical exponents. Nearby `158(mod256)` and `190(mod256)` are independently source-certified below.

## Next work

Check the other short inverse cones; develop a reusable certificate generator while retaining Lean source verification; prioritize an invariant closing entire surviving classes, since enumerating isolated residue families cannot by itself decide the P1 machine.


## Additional source-certified results: n ≡ 158 and 190 (mod 256)

**Successful manual original-source GitHub Actions verification:** [run 41405343696](https://github.com/FlareZ123/bb6/actions/runs/41405343696), head commit `ec7da8e22fb7220d9a94ef5a2eaff0c743389664`, completed 2026-11-02 07:18:51 UTC. This single run recompiles all eight **unmodified** original Agent 1 and Agent 50 dependency modules, checks SHA-256 of both full 552-line Lean sources, and compiles each final theorem. The final axiom audit is exactly `[propext, Classical.choice, Quot.sound]` for **both** theorems, no `sorryAx`.

```lean
BB6.Agent27.blank_no_critical_158_mod256 (k : Nat) :
  ¬BB6.Agent1.Reach 2 (14*2^(256*k+158)-2*(256*k+158)-10)
BB6.Agent27.blank_no_critical_190_mod256 (k : Nat) :
  ¬BB6.Agent1.Reach 2 (14*2^(256*k+190)-2*(256*k+190)-10)
```

- Full exact sources: [`P1Critical158.lean.xz.b64`](./P1Critical158.lean.xz.b64), decompressed SHA-256 `0052ca07b1691c5599c949147ae3b10dcec53199df95c0a02f9a8458c20ebf70`; [`P1Critical190.lean.xz.b64`](./P1Critical190.lean.xz.b64), SHA-256 `4623e1e15648cb3091e6625d9868b9ccca71659fd2946922a649a41a92943d12`.
- Exact manual-only workflow: [`agent27-p1-158-190-verify.yml`](../../.github/workflows/agent27-p1-158-190-verify.yml).
- Each proof exhaustively classifies its eleven-node `GAncestor` inverse cone. Source-proven `positive_G_feeder` and `reachable_even_mod4` remove most predecessors. Every remaining even-positive leaf forces `14·2^j` strictly between consecutive powers `14·2^(256k+R−1)` and `14·2^(256k+R)` for `R=158` or `190`; universally quantified Lean lemmas close these power constraints.
- The original-machine semantic bridge is separately source-verified by Agent19. Neither these new exclusions nor the earlier n≡206 family resolves all P1 candidates or determines BB(6).

**Aggregate:** Three genuinely distinct `n ≡ 158, 190, 206 (mod 256)` infinite all-time critical-index exclusions are now source-certified, representing three of the 16 subfamilies of the difficult `n ≡ 14 (mod 16)` class. These are intermediate partial results; external literature novelty remains to be checked. Preserve future work on wider classes and holdout-decision methods.
