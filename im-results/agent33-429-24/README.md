# Machine #429: source-integrated 24/2048 necessary halting gates (Agent 33)

**Intermediate research, 2026-11-05. BB(6) remains open.** This is a source-provable refinement of necessary terminal configurations of one six-state two-symbol Turing machine. It does not prove that any surviving configuration is ever reached, decide machine #429, or bound the global BB(6) maximum.

## Mathematical statement

For the exact original Google DeepMind Cryptids machine
`1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA`, the genuine high-level accelerator starts from the true blank section `highLevelStart`. Denote its state after `n` accelerated steps by `sourceRun n highLevelStart`. Machine #429 halts precisely if it reaches a terminal high-level section `J(u,w)` with `highLevelNext (.J u w) = none`. The accelerated terminal line is `w+1=2*u`.

The strengthened source theorem `BB429Final24.raw_halts_iff_24_classes` is intended to establish:

```lean
IsHalt target ↔
  ∃ n u w,
    BB429SourceLadder.sourceRun n highLevelStart = some (.J u w) ∧
    highLevelNext (.J u w) = none ∧
    u % 2048 ∈ liveClasses
```

where the exact `liveClasses` list is:

```text
[9,73,117,201,209,245,337,465,565,637,765,849,
 949,1021,1033,1097,1141,1233,1361,1673,1789,1917,1973,2045]
```

**Proof logic and credit.** Agent 1 derived and proved 49 genuine-root excluded terminal cylinders and a 25-candidate list modulo 2048. Agent 6 independently proved that every genuine-root terminal has `u%512≠81`, which removes the single still-listed 81(mod2048) residue (its 593(mod2048) lift was excluded already). Agent 33 repaired the source proof elaboration blockers, authenticated the full Agent 1 result against pinned original Cryptids, composed the two independent true-root sieves, and proved the exact arithmetic intersection universally over natural counters. The 24 arithmetic list is an **intersection of previously separately established mathematical exclusions**, not a new 24th standalone inverse barrier.

The 24-class theorem is equivalent to the exact 25-gate original raw iff augmented by Agent 6's 81(mod512) exclusion. It is only a **necessary candidate family**: the iff retains the actual original halting terminal existence and does not assert any of the 24 residues are reachable. A finite number of necessary residues modulo 2048 is not a finite number of remaining states or machines.

## Reproducible source and formal proof

1. [BB429Source24Mod2048.lean](BB429Source24Mod2048.lean) imports `BB429Source25Mod2048` and `BB429No81mod512`. `source_halt_not_81` transports the independent exact-root theorem into the original machine, and `raw_halts_iff_24_gates` composes the two genuine-source results.
2. [BB429GateArithmetic24.lean](BB429GateArithmetic24.lean) computes the 24 representatives by a simple finite `decide` certificate over 2048 residues.
3. [BB429Gate24Class.lean](BB429Gate24Class.lean) proves the stronger parameter-uniform arithmetic equivalence: `finite_cert` checks a full modulus period, `gate_periodic` and `good_periodic` use exact divisibility identities to extend it to all natural counters, `native_filter_iff_gate24` proves a proposition-to-Boolean reflection (including all 49 exclusions), and `raw_halts_iff_24_classes` connects the resulting exact set to the physical machine.

**Verification history:** Agent 33 fixed three earlier Lean proof-source defects in Agent 1's original files:
- `BB429No11Odd.lean`: explicit contradiction elimination for `rooted_eleven_even`.
- `BB429Shift53And721.lean`: dependent equality normalization for two exceptional inputs, and two exact successor-index arithmetic replacements for unsupported `convert`.
- `agent1-429-181-source.yml`: saving imported `.olean` modules for `BB429New34` and `BB429GateArithmetic` instead of compiling them as one-off scripts.

The **complete original-repository accelerator-source audit passed** [manual CI 41957167610](https://github.com/FlareZ123/bb6/actions/runs/41957167610), with `BB429New49.blank_halt_not_newGate` importing all 49 proofs and `BB429GateArithmetic25.survivors_exact` computing the 25 candidates. The **pinned unchanged upstream raw-machine proof of Agent 1's 25-gate theorem passed** [manual CI 41957639737](https://github.com/FlareZ123/bb6/actions/runs/41957639737) at exact original Cryptids SHA `c86f15861709b76042998c5211c7b2f83991621b`, Lean 4.35.0-rc4; final printed axioms were `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. Previous 25-gate source uncertainty is resolved.

**24-gate source status:** The independent 24-class arithmetic core has been checked locally in Lean 4.36.0-rc2 with standard axioms. The full pinned unchanged original-source integration and source-axiom audit is dispatched as [manual CI 41958805910](https://github.com/FlareZ123/bb6/actions/runs/41958805910); check its actual result before claiming source-native certification. The updated manual-only [workflow](../../.github/workflows/agent33-429-native-24.yml) includes `BB429Gate24Class.lean` for a subsequent run. The displayed 24-class source theorem is **pending** until that last proof compiles.

## Remaining obstruction

A uniform obstruction of the whole surviving true-blank halting locus is still needed; infinitely many terminal configurations survive this 24/2048 necessary mask. Further lifting to finer moduli without eliminating a whole infinite family will not settle nonhalting. Possible next work: genuine-root inverse and forward invariants that eliminate an entire residual feeder cone, or a real original-source halting witness. Also compare this intersection to newer overlapping external formal and informal work before considering publication novelty.

This dossier belongs in `im-results/`; `results/` is reserved for independently justified original academic advances.

## New exact whole-cylinder inverse certificates (2026-11-05)

[BB429New9Lift.lean](BB429New9Lift.lean) derives two **new entire families** on the genuine blank-root accelerator:

```lean
BB429New9Lift.no_halting_2_mod8192 : ∀ n a b,
  BB429.run n (0,0) = some (a,b) → b+1=2*a → a%8192≠4105

BB429New9Lift.no_halting_3_mod8192 : ∀ n a b,
  BB429.run n (0,0) = some (a,b) → b+1=2*a → a%8192≠6153
```

Both are **formally proved with no `sorryAx`**, verified in [manual source audit 41961249321](https://github.com/FlareZ123/bb6/actions/runs/41961249321). Exact printed dependencies: `[propext, Classical.choice, Quot.sound]`. They cover all `a=8192q+4105` and `a=8192q+6153` for any natural `q`, hence exclude entire unbounded families rather than a finite prefix. There are still infinitely many live classes.

### Generalizable method

For the local accelerated `BB429.next` function, Agent 6's certified `odd_back` lemma implies that any genuinely reachable odd first counter `a≥13` with second counter `b` must have an actual reachable predecessor satisfying one of

```text
F:  a = 2*x + 3;             y = b+a
S:  4*x + 26 = 4*a+b;       2*y=b+4;    b mod 4=2
```

An even `a≥6` has one necessary predecessor

```text
E:  4*x + 14 = 4*a+b;       2*y=b;      b mod 4=2
```

These formulas are necessary conditions on *real reachability*, not guessed reverse simulator transitions. For each entire affine terminal cylinder `a=8192q+r, b=2a-1`, substitute the formulas and split **all** possible inverse branches, checking the congruences uniformly for arbitrary `q`. At each ancestor, immediately reject a branch when its affine counters violate the already formally proved true-root invariant `BB429Mod8.Allowed` or `BB429RootMod16.rooted_not_7_7`. All noncontradictory branches require further inverse proofs. The new 4105 and 6153 certificates have a full binary-branch analysis of maximal predecessor depth **ten**, with every leaf ruled out.

Common branching tree for both cases:

```text
root --F--> F --F--> FF [forbidden Allowed]
                   --S--> FS --F--> FSF --E--> FSFE --F--> FSFEF
                                           FSFEF --F--> FSFEFF [forbidden Allowed]
                                                 --S--> FSFEFS --F--> FSFEFSF
                                                                --E--> FSFEFSFE
                                                                --F--> FSFEFSFEF
                                                                --F--> FSFEFSFEFF [forbidden Allowed]
                                                                --S--> FSFEFSFEFS [forbidden invariant]
```

Here `FSFEFSFEFS` has `a%8=7,b%8=7` for the 4105 family, violating Agent 39's source theorem; the 6153 family violates `Allowed` directly. The tree display is conceptual; the checked Lean file spells out each affine coefficient and proves all necessary inverse cases and leaf contradictions.

**Methodological caution:** A finite reverse search at a few sample `q` values is never enough to prove an infinite cylinder. The Lean proof quantifies over `q : Nat`, uses exact arithmetic `omega` at every predecessor branch, and checks every possible inverse case. Other 8192 lifts can need arbitrarily deeper inverse trees; the approach is a conditional semidecision method rather than a complete algorithm. It is useful where a *uniform* finite inverse contradiction can be found.

[BB429Source9Lift.lean](BB429Source9Lift.lean) transports these new gates into the unchanged original six-state Cryptids machine and composes the exact 24-class gate to get `raw_halts_iff_94_candidates` (a nominal 94/8192 count before integrating other agents' independent fine-modulus exclusions). The full raw-machine CI is **pending** at this writing; this statement must only be called source-authenticated after the original Cryptids workflow succeeds.
