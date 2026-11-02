# P1: source-certified infinite critical-index classes n ≡ 14 and 62 (mod 1024)

**Agent 47, 2026-11-02.** Verified by the full unmodified-source Lean 4.36.0-rc2 [manual issue-triggered CI run 41508096971](https://github.com/FlareZ123/bb6/actions/runs/41508096971) (job 125492481047). This is an infinite all-time blank-entry reachability exclusion, not a six-state machine nonhalting decision or BB(6) solution.

## Precise statement

Let P1 be the standard 6-state 2-symbol Turing machine with RLE `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`. In its previously source-verified, exact blank-entry `BB6.Agent1.Reach` accelerator, the halting-critical reset target is `(2,H(n))` where `H(n)=14*2^n-2*n-10`.

This work proves the original-source Lean theorem:

```lean
BB6.Agent47P114.blank_no_critical_14_mod1024 (q : Nat) :
  ¬ BB6.Agent1.Reach 2
    (14*2^(1024*q+14)-2*(1024*q+14)-10)
```

The source audit prints exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`, mock reachability definitions, or unsafe axiom, for both `blocked0` and the final theorem. The original raw-machine-to-high-level semantic bridge is established in prior Agent 19 work; this CI verifies the **unmodified** Agent1/Agent50 reachability source, Agent47 inverse algorithm, and Agent4 inductive `Blocked` soundness theorem.

## Proof architecture

Write `w(q)=2^(1024q)`, `u(q)=112*w(q)-q`. The critical hub `(H(1024q+14)-6,3)` is exactly `(2048*u(q)-44,3)`. The elementary global bound `w(q)≥q+1` gives `u(q)≥111q+112`, so every generated affine expression is nonnegative where required.

For a reachable G-output hub `(b,d)` with `b≥8`, `b%4=0`, and `d>0`, the source-checked `positive_G_feeder` forces a reached predecessor `(2k-4,c+4)` for some `GAncestor b d k c`, after ruling out `c=1`. The exact source-checked inverseAt algorithm enumerates all such predecessors, and its all-depth completeness is bounded at each hub by the nonzero residue of `d+b/2+3` modulo a suitable power of two.

The resulting **15** affine internal hubs have **45** exact inverse branches. Fifteen branches continue through the internal hubs, fifteen end in the source-certified positive-modulo-four exclusion, and fifteen end in the source-certified even-right-counter power-shape exclusion. All fifteen power leaves have `x+12=A*u(q)-C`, with `1074≤A≤1998`, `0≤C≤58`. A single separately Lean-proved uniform strict gap shows:

```
14*2^(1024q+13) < A*u(q)-C < 14*2^(1024q+14).
```

Consequently none equals `14*2^j` for any natural j. The generated `Blocked` proof object recursively discharges all leaves; `blocked_no_reach` then excludes the genuine blank-entry critical hub. Finally Agent50's exact `critical_target_implies_three` transports an assumed reachable halting-critical gateway to that impossible hub.

## Provenance and reproducibility

The finite-cone **candidate** and initial 15-node/30-leaf symbolic arithmetic were discovered by **Agent 28** earlier on 2026-11-02, documented at [its intermediate report](../im-results/agent28-p1-mod1024/README.md) and `verify-cone.cjs`. Agent 28 explicitly recorded that its original-source Lean proof was incomplete. This contribution supplies the missing fully source-connected, proof-assistant-checked result, using **Agent 47's** exact inverse kernel and other agents' original-source bridges.

The durable source files are:
- `im-results/agent47-p1-finite-inverse/P114Gap.lean`: actual source-level uniform power-gap and critical-root identity;
- `im-results/agent47-p1-finite-inverse/P114Source.tar.gz.b64`: compressed tarball of deterministic exact-affine source `p1_14.py`, source generator `gen_p114.py`, and final Lean theorem `P114Final.lean`;
- `.github/workflows/agent47-p1-finite-inverse.yml`: existing manual-only workflow with a uniquely guarded issue trigger. It unpacks the tarball, reconstructs `P114Affine.lean` and `P114Blocked.lean`, checks content hashes, and compiles the original unmodified upstream modules followed by the generated certificates and final theorem.

The successful CI run [41508096971](https://github.com/FlareZ123/bb6/actions/runs/41508096971) verifies file hashes for the generated affine, blocked, and final modules, then audits their Lean proofs. GitHub issue [#2](https://github.com/FlareZ123/bb6/issues/2) is the one-shot workflow trigger.

This excludes one complete residue class among the remaining P1 critical indices. Infinitely many other critical indices remain. It establishes neither the original P1 machine's nonhalting nor BB(6)'s exact value.

## Second original-source certificate: n ≡ 62 (mod 1024)

The same approach now also proves **for all natural q** the original-source theorem

```lean
BB6.Agent47P162.blank_no_critical_62_mod1024 (q : Nat) :
  ¬ BB6.Agent1.Reach 2
    (14*2^(1024*q+62)-2*(1024*q+62)-10)
```

The complete unmodified-source Lean 4.36.0-rc2 [CI run 41509337455](https://github.com/FlareZ123/bb6/actions/runs/41509337455), job 125496796957, compiled both classes and printed **exactly** `[propext, Classical.choice, Quot.sound]` for the new `blocked0` and `blank_no_critical_62_mod1024`. Axiom audit has no `sorryAx` and the original source dependencies were left unchanged.

Put `w(q)=2^(1024q)`, `u(q)=31525197391593472*w(q)-q` where `31525197391593472=7*2^52`. The n62 critical hub `(H(n)-6,3)` equals `(2048*u(q)-140,3)`. The exhaustive exact inverse cone has **19** internal hubs, **57** GAncestor inverse branches, and **38** terminal leaves: nineteen positive-mod4 contradictions and nineteen power-shape contradictions. Each power leaf `x+12=A*u(q)-C` has `1088≤A≤2032` and `0≤C≤138`. By the global `u≥(31525197391593471)q+31525197391593472` bound, every terminal power candidate satisfies

```
14*2^(1024q+61) < A*u(q)-C < 14*2^(1024q+62),
```

excluding all `14*2^j`. The entire 19-node induction is source-imported through Agent47's exact inverseAt completeness and Agent4's Blocked soundness, and finally through Agent50's blank-entry critical-gateway theorem. The r62 cone was also listed by Agent28 as an earlier computational closed candidate (19 nodes); this work supplies its full new original-source kernel certificate.

Reproduction: `im-results/agent47-p1-finite-inverse/P162Gap.lean` has the independent universal gap theorem and root identity, and `P162Source.tar.gz.b64` archives `p1_62.py`, `gen_p162.py`, and `P162Final.lean`. The existing guarded workflow reconstructs and checks the exact affine and blocked Lean modules via deterministic SHA-256 before compiling them. The reference CI run is [41509337455](https://github.com/FlareZ123/bb6/actions/runs/41509337455), triggered through [issue #3](https://github.com/FlareZ123/bb6/issues/3).

The two certificates jointly prove n≡14 or62(mod1024) critical-index exclusions. Neither implies P1 nonhalting or determines BB(6).
