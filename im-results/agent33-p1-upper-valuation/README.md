# Exact P1 upper inverse-chain depth (Agent 33, 2026-11-02)

**Source-certified intermediate structural theorem.** No blank-reachability or halting conclusion.

For P1's exact critical target `H(n)=14*2^n-2*n-10`, Agent 27's real two-step inverse family has `upperB(r,0)=4r` and `upperB(r,h+1)=2*upperB(r,h)+12`. For all naturals `n≥2` and `h+1≤n`, the new Lean proof establishes:

```lean
BB6.UpperDiv.source_upper_depth_iff (n h : Nat)
    (hn : 2 ≤ n) (hh : h+1 ≤ n) :
  (∃ r : Nat, BB6.Agent27.upperB r h =
    14*2^n - 2*n - 16) ↔ 2^(h+1) ∣ n+2

BB6.UpperDiv.source_critical_has_upper_path (n h : Nat)
    (hn : 2 ≤ n) (hh : h+1 ≤ n)
    (hd : 2^(h+1) ∣ n+2) :
  BB6.Agent27.TwoStepPath h (14*2^n - 2*n - 16) 3
```

`TwoStepPath h` contains 2h genuine, exact accelerated-T transitions imported from Agent 27, which in turn imports the unmodified Agent 1 P1 definition. **Every** critical index in any sufficiently large residue class `n≡-2 (mod 2^(h+1))` admits the specified synthetic upper chain, strengthening Agent 27's earlier construction restricted to `n=2^(k+3)-2`. Other inverse branches may exist; no maximality over all predecessor families is claimed.

**Derivation.** `upperB(r,h)+12=4*2^h*(r+3)`. Hence `upperB(r,h)=14*2^n-2n-16` iff `7*2^n=(n+2)+2^(h+1)*(r+3)`. The forward divisibility follows from `h+1≤n`. Conversely, write `2^n=2^(h+1)*m` and `n+2=2^(h+1)*q`. The Lean-proved global inequality `n+2≤2^n` implies `q≤m`, so `r=7m-q-3` is natural and provides the desired chain.

**Verification:** [Original-source Lean CI 41430749002](https://github.com/FlareZ123/bb6/actions/runs/41430749002), successful job 125228415147, commit `8b43a6a627e18667f5fac1231e2d3a376f98eb21`. Workflow: [agent33-p1-upper-depth.yml](../../.github/workflows/agent33-p1-upper-depth.yml). Lean 4.36.0-rc2 compiled all full unmodified Agent 1 and Agent 27 dependencies and the complete new proof sources, with standard axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

Source archives: `UpperDiv.lean.xz.b64` unpacked SHA-256 `69768a4f6641889d27173a12c9def5fc4277eea4fb3a6d8ea78b38e1c4744c94`; `UpperBridge.lean.xz.b64` unpacked SHA-256 `62e831ce4b339ea53a102c732003bf26f285b89616d882fd0fa3c7091ab25576`. The original Agent 27 module unpacks to SHA-256 `b8045299f45dd1144726d921642c400056c65610c17650829bbbf6373dc7ae44`.

**Limit:** These paths are synthetic predecessors. Their existence is fully compatible with P1 blank-orbit nonhalting. No new BB(6) bound or decision is established. Source provenance for actual upper two-step transitions belongs to Agent 27; this contribution is the uniform exact divisibility classification. Further work needs genuinely blank-reachable barriers. External publication novelty is unassessed; retain in `im-results/`.
