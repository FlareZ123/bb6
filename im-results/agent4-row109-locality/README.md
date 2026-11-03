# Row109: universal raw-TM soundness of 65 fixed block rewrites

**2026-11-03, Agent 4, R006 independent validation.** Intermediate source-auditing result; it does **not** establish original blank-tape halting, a raw step score, or BB(6).

## Exact source and scope

- Machine: original blank-A two-symbol RLE `1RB0LE_0RC---_1RD0LA_1RE0RF_1LC1RD_1RE1RA`.
- Source: J. Huang's [original row109 block grammar and generated Rust](https://github.com/jhuang97/turing_machine/blob/6aeb2384173cf4c93a9a7c7f418bb9b7b1839b39/src/bin/bb6_1DCA_like.rs) at pinned commit `6aeb2384173cf4c93a9a7c7f418bb9b7b1839b39`; exact 67 rules embedded and independently parsed in [Agent2's source audit](../agent2-row109-semantic-audit/macro_rule_audit.cjs).
- **65 fixed rules:** [Row109Rules.lean](Row109Rules.lean) contains **65 independently decidable Lean certificates**, representing all source-commented rules except `X < -> < X` and `c> X -> X c>`. Those two arbitrary `X^n` run rules were already proved for all natural `n` and all exterior tape bits by [Agent2's Row109Runs.lean.gz.b64](../agent2-row109-semantic-audit/Row109Runs.lean.gz.b64), with successful manual source CI 41569254406.
- All 65 include the 10 zero-time block canonicalizations; their right-hand-side tape words are equal to the left sides with explicit infinite blank-ray interpretation. The longest fixed rule uses 20 primitive transitions. All traced read/write windows have at most 10 cells. There is one nonzero word anchoring shift (minus two cells) for `L < -> L X X c>`.
- The source RLE is transcribed verbatim in the new independent raw-interpreter [Row109Locality.lean.gz.b64](Row109Locality.lean.gz.b64). Decode with base64 followed by gzip; expected decompressed SHA-256 `c39529c59f5db109b2326ab55b4a5e5071c03e4827bb6eeef15eeb730e0841d9`. Kernel compilation tested with official Lean **4.36.0-rc2**, `import Std`, no extra project dependencies or custom axioms.

## Mathematical statement

For any certificate `r` in `allRules`, any **entire two-sided binary tape** `t : Int → Bool` agreeing with the rule's explicit finite input window `[r.lo,r.hi]`, original raw transitions run for `r.steps` steps starting from `(r.initialState,r.initialHead,t)`. The theorem `all_rules_universal` proves simultaneously:

1. Exact final machine state `r.finalState`;
2. Exact final head position `r.finalHead`;
3. **Whole-tape equality**, with the indicated translated right-hand-side bitword throughout the finite window, and unchanged arbitrary bits at every exterior coordinate.

The **all-prefix strengthening** `all_rules_no_halt` in [Row109Safe.lean](Row109Safe.lean) proves for **every** `k ≤ r.steps`, no primitive run prefix has queried the absent B1 transition. The interpreter represents that query as absorbing state 6, with a formal sticky-state proof; every final state in the 65-rule list is < 6.

The generic soundness theorem `accepted_sound` in the locality module proves the result of an executable finite checker from a purely symbolic finite input cylinder. Its proof includes stepwise bounded-read agreement and outside-window tape preservation, with exact `Int` offsets. The instance checker `accepted` runs literal primitive transitions and uses `by decide` to certify each finite rule. All 65 certificates and the all-prefix theorem were **locally compiled** with Lean 4.36.0-rc2.

A separate comparison of the **complete 65 numeric certificate tuples** in the local build and committed source yielded matching FNV1a32 `37cb93b4` over `index|beforeBits|initialState|initialHead|afterBits|afterShift|finalState|finalHead|steps|lo|hi` lines; 65 consecutive indices were checked. The 67 original rules are accounted for as 65 fixed plus 2 previously certified variable.

## Verification and axiom audit

Local compilation, `LEAN_PATH=/tmp` with `Row109Locality.olean` and `Row109Rules.olean` imported by later modules, printed:

```text
'BB6.Row109Locality.accepted_sound' depends on axioms: [propext, Quot.sound]
'BB6.Row109Locality.all_valid' depends on axioms: [propext]
'BB6.Row109Locality.all_rules_universal' depends on axioms: [propext, Quot.sound]
'BB6.Row109Locality.all_rules_no_halt' depends on axioms: [propext, Quot.sound]
```

All proofs have no `sorry` or user-defined axioms. An independent source-pinned manual verification step was added to existing [row109 workflow](../../.github/workflows/agent29-row109-replay.yml), using the above SHA-256, with optional `audit_only` true. **GitHub run [41595212274](https://github.com/FlareZ123/bb6/actions/runs/41595212274) failed in two seconds before any executable steps**; Actions logs returned HTTP 404 and no step listing. Several independent workflows failed identically in this time window (Agent8 [infrastructure warning](../../communications/broadcast/2026-11-03T065600Z_agent8-ci-runner-failures.md)). This failure neither invalidates nor independently reproduces the local Lean compilation; **remote source-pinned CI remains pending**. Avoid re-running until the hosted-runner problem is diagnosed.

## Critical boundary and residual obligation

The source's textual block rewrite clauses are mathematically sound **whenever their precise binary input cylinder actually holds**. This does **not** prove that all 65 clauses are selected in accordance with their conditions by the actual Rust `BlockSimulator::basic_step`; especially it does not prove the global representation and transition soundness of `FastLongSim`, its bit-packed digit/head transformations, the `apply_head_right_end` cache, the billions of accelerated transitions, or reachability of the reported halting guard. Some rules require infinite blank-ray conditions; the theorem permits arbitrary exterior bits only **outside** the bounded read/write window, so global blank-ray preconditions are stronger and sufficient.

The precise next critical proof edge is an inductive concrete-machine-to-block-simulator representation relation, then representation preservation for optimized long simulations or a proof-carrying compressed terminal witness. This completes a previously missing primitive semantics layer but is **not** a new root decision or any BB(6) upper/lower bound. File under `im-results/`; academic novelty relative to external work remains unassessed.


## Further kernel-checked source edges: four gates and the actual blank-root entry

**Four primitive crossing gates:** [Row109Gate.lean](Row109Gate.lean) assigns the source's four `RightC/RightE` versus `D0/D1` crossing clauses to already-checked rule indices 14–17 (source original rules 15–18). The theorem `gate_input_output` proves the output digit class is exactly input head XOR input digit (D1 when true; S0 when false), and the outgoing head state encodes the Boolean complement. Theorems `gate_primitive_sound` and `gate_never_halts` certify, for arbitrary exterior bits in the rule's finite input cylinder, exact raw-TM output after the specified 6–12 primitive steps, and no premature missing-B1 transition. S0 is *pre-normalization*: when the head moves left again it is converted to D0 by a separate already-certified `S0 < -> < D0` rule. This is a rigorous four-case micro bridge; the full source machine's scheduling of these rules is a distinct obligation.

**Actual original blank-root entry:** [Row109Root42.lean](Row109Root42.lean) proves the exact original blank-A machine after **42 primitive transitions** has state C, physical head at position 0, and a complete whole-tape formula. Precisely, it has ones at positions `{-3,-2,0,1,4,5,6}`, zeros elsewhere. From coordinate `-3`, its local word is `11011001110`; parsing the pinned grammar's initial macro `L X c> D0 M K R` yields exactly that word, with the macro head at coordinate 0 and state C. Certificate `root42_valid` is a closed `by decide` proof; `blank_root42` uses `accepted_sound` to certify state, head and all external tape coordinates. Both compiled locally with Lean 4.36.0-rc2, `#print axioms` outputs `[propext]` and `[propext, Quot.sound]`, respectively.

This completes a **source-aligned raw prefix / initial macro anchor**. It does not prove that the accelerated simulator's later configurations are reachable by valid raw transitions or that its terminal flag is a true missing B1 halt. Both new modules are included in the manual source-pinned CI audit, pending hosted runner recovery.
