# Machine C: 86 additional reset-index classes at modulus 8192

Agent 29, 2026-11-04. **Status: candidate all-parameter exclusions, each locally Lean-kernel-checked; unchanged-source GitHub Actions certification remains pending.** This dossier is deliberately in `im-results/`. It does not solve Machine C or BB(6).

## Statement

For each of the 86 distinct residues `r` in [manifest.json](./manifest.json), for every `t : Nat`, the local Lean 4.36.0-rc2 proof has the exact conclusion

```lean
¬ BB6CLine.Reach (2*(8192*t+r)+1, 3*(8192*t+r)+4, 0)
```

Here `BB6CLine.Reach` is accelerated Machine C blank-entry reachability from `(5,0,1)`, for `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. All proof branches are explicit symbolic inverse transitions, with universal natural-number parameter `t`. No run-length cutoff, finite-only assertion, oracle, `sorry`, or custom axiom is used in the locally checked modules.

Each of 86 separate Lean modules compiled locally successfully with `#print axioms` exactly `[propext, Classical.choice, Quot.sound]`. The local environment independently compiled source-equivalent copies of `CLine`, `CReachBridge`, `CRange`, `CBack` and `CHubSplit` with all used inverse lemmas proved. These copies do not yet constitute an audit of the original repository dependency files. The manual source-original CI workflow is [agent29-c8192-new.yml](../../.github/workflows/agent29-c8192-new.yml). Upgrade verification status only after that workflow succeeds on its complete set of four shards.

## Comparison with the earlier gateway filters

The benchmark source is Agent 41's modulus-1024 overapproximate quotient, reproduced locally by compiling the independently published `validate_bits.cpp` algorithm. Its run returned exactly **385,473,152 reachable quotient vertices**, **3,050,991,229 examined edges**, and **678 reset index classes excluded modulo1024**, agreeing with the repository's recorded count.

Lift that 678-class quotient, the 43 published source-verified reset classes modulo2048, the four previously source-verified reset classes modulo512, and the **85 pre-existing modulo4096 candidates** from [Agent 29's November 2 manual workflow](../../.github/workflows/agent29-c4096-new.yml) to modulus8192. Their union covers **5,806/8,192** index residues. The 86 entries in our new manifest are pairwise distinct and lie outside that union. Conditional on source-level verification of both candidate corpora, the combined necessary reset-gateway filter reaches **5,892/8,192**, leaving 2,300 residue classes outside this particular filter. The previously published sources and source-CI runs justify their own portions; the 85 old candidates and 86 new candidates must be labeled separately until their original-source CI statuses are established.

The old 85 at modulus4096 were already proposed in an Agent29 workflow dated **2026-11-02 08:44 UTC**. They are not being claimed as new here. An independent second locally checked reconstruction of those 85 is preserved in [agent29-c4096](../agent29-c4096/) only as reproducibility support.

## Reproduction

1. Run the existing SHA256-pinned `im-results/agent29-c31/reconstruct.py` to restore `C31.lean`.
2. Run `im-results/agent29-c4096/reconstruct.py` to restore the universal affine inverse-tree generator. That bundle was locally checked and pins generator SHA256 `d9bb28af7329bc21945ca9b856c8d0ee35080c10dcaa2d83f10f747264632bee`.
3. Run [generate8192.py](./generate8192.py) to reconstruct all 86 theorem modules. The generator verifies the complete concatenated Lean-source corpus with SHA256 `08ff13f12d0e599ab15f1bff1e27907e968ed7c7cbe641ef6bac909a3a3144c5`. This pins the ordered residue list and every generated proof byte.
4. The manual workflow compiles the **unchanged checked-in** `CLine`, `CReachBridge`, `CRange`, `CBack` and `CHubSplit` dependencies and then all 86 modules, divided across four independent jobs. Each file displays an explicit theorem axiom audit.

The deterministic generator transports reachability through exact source-proved high-sector split, reset contraction and portal contraction rules, recursively producing finite affine predecessor trees. Arithmetic leaves contradict the universal odd-zero `mod4` exclusion or exhaustive branch equalities.

## Limitations and worthwhile follow-up

The source-original CI still needs manual dispatch and successful completion. The quotient and the 43 previously proven classes provide a **necessary condition** on halting-gateway reachability. Neither 86 new finite symbolic trees nor any aggregate residue count decides all infinitely many reset parameters, let alone the second Machine C gateway family or any other BB(6) holdout. The 2,300 unexcluded classes remain unknown, and external novelty review has not been performed.

Follow up by certifying the new 86 directly against unchanged source, reviewing any overlap with stronger modern Machine C reverse cores, and prioritizing uniform two-parameter halting-family obstructions over a continuing stream of small residue refinements.
