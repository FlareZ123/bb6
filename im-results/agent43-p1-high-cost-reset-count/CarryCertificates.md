# Full-P carry certificates: right-five and critical reset reachability

The right-five source wrappers for n=30 and n=350 are accepted by [pinned Lean CI 45424975061](https://github.com/FlareZ123/bb6/actions/runs/45424975061) at commit b318fa9199327067f7d2edcba04ed07eeefea243. The new stronger margin core and both numerical margin certificates compiled locally with Lean 4.36.0-rc2 and ordinary axioms. The original-source blank-reachability integration passed [CI 45426720678](https://github.com/FlareZ123/bb6/actions/runs/45426720678) at 0c5e74b5584e88a5c4006225b70816a1a36d7750. Agent28 subsequently certified n=286 via a shared-boundary chain [CI 45439869906](https://github.com/FlareZ123/bb6/actions/runs/45439869906). Agent28's n=1614 certificate passed [CI 45439883987](https://github.com/FlareZ123/bb6/actions/runs/45439883987), and Agent28's earlier half-carry proof of n=2990 passed [CI 45441634110](https://github.com/FlareZ123/bb6/actions/runs/45441634110); the independent faster block method also certified n=2990 in [CI 45468827027](https://github.com/FlareZ123/bb6/actions/runs/45468827027) at 01755f0e31182be70a628cb5bb0abd99928627c5. The previously outstanding n=3342 source exclusion passed all four shards and final source closure in [CI 45470826613](https://github.com/FlareZ123/bb6/actions/runs/45470826613) at 9512492198181eda3b5845c0fc0e6813841ef661. All even critical indices in [14,10000] are now excluded. No unbounded P1 decision is claimed.

## Strengthened certificate and exact source argument

Set Q=7*2^n-(n+3). The full-P carry starts at 1 and at layer j admits c/2 or (c+Q-j)/2 when integral. Every original OddCone endpoint transports to carry c=(d-1)/2 (Agent28's exact-block theorem, adapted directly to OddCone). If the layer K is empty and every earlier carry satisfies c≠2 and c+L+j≤Q+2, with L=2*(n+3*K+10)+6, then every genuine critical OddCone endpoint satisfies:

- m<K, by persistence of emptiness;
- d≠5, by exact endpoint membership;
- b/4≥n+3*K+10, by the original mass relation b+d+2*m+2*n+13=14*2^n.

[MarginCert.lean](MarginCert.lean) proves the computational certificate sound, including persistent emptiness and the last arithmetic implication. [MarginSource.lean](MarginSource.lean) generalizes Agent50's blank-reachability induction from early small-carry extinction to these three gate conditions, with no K≤n restriction. Large left counters rule out exceptional b=2; odd right-five exclusions rule out c=1 G-inputs; every even output lies strictly between adjacent powers 7*2^n and 14*2^n. Remaining odd outputs give genuine parents at strictly higher cost, so strong induction on K-m excludes every authentic reachable cone state. The original critical target reduction then excludes Reach 2 (14*2^n-2*n-10) for even n. The source declarations for n=30,286,350,1614,2990,3342 have passed their pinned original dependency closures.

## Finite results

| n | Empty K | Minimum left-margin bit length (experiment) | Layer attaining minimum | Kernel right-five and margin | Blank reset wrapper |
|---:|---:|---:|---:|---|---|
|30|82|19|38|accepted|accepted|
|286|1442|271|1319|accepted|accepted|
|350|586|335|438|accepted|accepted|
|1614|5824|1597|2568|accepted|[CI 45439883987](https://github.com/FlareZ123/bb6/actions/runs/45439883987)|
|2990|6154|2973|3787|accepted|[CI 45468827027](https://github.com/FlareZ123/bb6/actions/runs/45468827027)|
|3342|13730|3320|7084|accepted|[CI 45470826613](https://github.com/FlareZ123/bb6/actions/runs/45470826613)|

[margin_scan.py](margin_scan.py) is an exact-integer experiment for all six cases; it asserts emptiness, carry-two avoidance and the required margin at every earlier layer. Agent28's [modular budget screen](../agent28-p1-modular-screen/README.md) passed original-source CI for the other 4988 even indices ≤10000. Together with all six full-P source theorems, all 4994 even indices in [14,10000] are excluded.

[gen_margin_cert.py](gen_margin_cert.py) generates untrusted literal checkpoints and kernel-checked composition proofs. Use `python gen_margin_cert.py 350 586 16` from a temporary directory, then Lean with LEAN_PATH including this dossier. The locally compiled margin350 used the same checkpoint data and equivalent theorem calls with the literal requiredMargin argument rather than the helper definition. The generator's new helper definition is definitionally equal. The n286 full literal file (1.7 MB) hit a memory limit with default parallel elaboration; a serial run was stopped after 4m29s to preserve RAM for the stronger margin checks, not a mathematical counterexample. Agent28 solved the n286 resource failure with [gen_chain_margin.py](../agent28-p1-modular-screen/gen_chain_margin.py), sharing boundaries across explicit kernel-checked composition groups. The n1614 shared-boundary chain succeeded; the n2990 block chain is described below.

## Block certificates for the expensive remaining indices

[BlockCarry.lean](BlockCarry.lean) gives a kernel-checked sound block transition. For h bits, let M=2^h and let s range over weighted offsets sum(x_i*(Q-j-i)*2^i), i<h, with natural subtraction. Every true endpoint v from c satisfies M*v=c+s. Index offsets by residue (-s) mod M, storing ceil(s/M); the matching bucket gives v=c/M+ceil(s/M). A binary trie implements these buckets.

[BlockMargin.lean](BlockMargin.lean) proves that the two distances c and Q+2-j-c each shrink by at most a factor of two per step (j≤Q). Thus if a block starts with 3*2^h≤c and c+2^h*L+j≤Q+2, all its intermediate layers meet the required margin. A Cover certificate only requires containment at its final layer, composes across arbitrary groups, and converts an empty final layer to MarginSafe. The initial carry 1 uses a separately checked single step.

[Generate.lean](Generate.lean) and [BlockProposal.lean](BlockProposal.lean) generate untrusted candidate boundary lists as literal Nat expressions, avoiding huge text parsing. Every transition equality and start envelope is subsequently checked by decide +kernel; the proposal elaborators add no axioms. [gen_block_chain.py](gen_block_chain.py) produces independent groups, a balanced composition tree, and the source wrapper. Example: `python gen_block_chain.py 2990 6154 8 12 /tmp/blocks`; compile modules in modules.txt order with this dossier and the output directory on LEAN_PATH, then compile the Source module. The existing manual workflow target margin-block uses this procedure and unchanged original-source dependencies.

Local Lean 4.36.0-rc2 checks against the exact minimal CarryCert/MarginCert definitions proved the general block and margin lemmas (ordinary axioms only), the complete already-settled n=350 certificate (h=8, group=20), and n=2990 group 20 (h=8, group=12; 32.70 s, peak RSS 2,078,180 KiB). Original-source n2990 CI 45468827027 completed successfully in 7m51s. It certified both margin2990 and critical_reset_no_reach_2990 with only propext, Classical.choice, Quot.sound. The 65 independent groups ran two at a time. The n3342 case used the same checker in four bounded CI shards, with the final source job importing their kernel-checked .olean files and composing the original-source theorem. All jobs passed; the final margin3342 and critical_reset_no_reach_3342 audit only propext, Classical.choice, Quot.sound. Local shell GitHub DNS failed, so source-closure validation uses the manual workflow.

## Previous right-five-only certificate

[CarryCert.lean](CarryCert.lean), [gen_carry_cert.py](gen_carry_cert.py), [CarryCertSource.lean](CarryCertSource.lean). The source integration CI above accepted n30 and n350. These are retained for comparison and dependency history; the margin certificates strictly strengthen the finite arithmetic claim.


## Finite halting criterion and unbounded residue lift (19:47 UTC)

[EarlyGate.lean](EarlyGate.lean) and [GateJoin.lean](GateJoin.lean) passed [original-source CI 45472384572](https://github.com/FlareZ123/bb6/actions/runs/45472384572) at a2390700e24fc4ec1403f01278b14a91a21833fe. The former excludes every critical reset index n<=12 via a kernel-checked bounded exact orbit plus a strict mass-growth proof. The latter excludes every odd critical index, proves the exact forward macro gate implies the original reset target, and supplies the logical composition theorem full_finite_cover and halt_iff_remaining. The separately accepted modular screen and six full-P theorems discharge the exact premises of full_finite_cover at B=10000. Hence SourceHalt (2,1) iff there is an even n>=10002 with MacroReach (7*2^n-n-3) 1. This is the mathematical composition of separately source-checked theorem declarations; a single imported .olean of all six large numerical proofs has not been built. It is not an all-n exclusion.

[ModularSource.lean](ModularSource.lean) passed [CI 45473568466](https://github.com/FlareZ123/bb6/actions/runs/45473568466), after qualifying an ambiguous bound name. It combines Agent28's modular full-P emptiness coupling, Agent43's exact endpoint membership, and Agent50's source_width_iff and stronger source exclusion. A checkCert (r,k)=true and n=r+2^(k+1)*t, 14<=n and k+1<=n imply authentic critical-reset exclusion, with no extra numerical budget. The theorem applies to every index in the whole residue cylinder, including future large-index scans. This is a source bridge, not an exhaustive cylinder cover.
