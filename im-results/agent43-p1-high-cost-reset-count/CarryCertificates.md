# Full-P carry certificates: right-five and critical reset reachability

The right-five source wrappers for n=30 and n=350 are accepted by [pinned Lean CI 45424975061](https://github.com/FlareZ123/bb6/actions/runs/45424975061) at commit b318fa9199327067f7d2edcba04ed07eeefea243. The new stronger margin core and both numerical margin certificates compiled locally with Lean 4.36.0-rc2 and ordinary axioms. The new original-source blank-reachability integration is pending focused CI. No claim is made that all critical indices or P1 are decided.

## Strengthened certificate and exact source argument

Set Q=7*2^n-(n+3). The full-P carry starts at 1 and at layer j admits c/2 or (c+Q-j)/2 when integral. Every original OddCone endpoint transports to carry c=(d-1)/2 (Agent28's exact-block theorem, adapted directly to OddCone). If the layer K is empty and every earlier carry satisfies c≠2 and c+L+j≤Q+2, with L=2*(n+3*K+10)+6, then every genuine critical OddCone endpoint satisfies:

- m<K, by persistence of emptiness;
- d≠5, by exact endpoint membership;
- b/4≥n+3*K+10, by the original mass relation b+d+2*m+2*n+13=14*2^n.

[MarginCert.lean](MarginCert.lean) proves the computational certificate sound, including persistent emptiness and the last arithmetic implication. [MarginSource.lean](MarginSource.lean) generalizes Agent50's blank-reachability induction from early small-carry extinction to these three gate conditions, with no K≤n restriction. Large left counters rule out exceptional b=2; odd right-five exclusions rule out c=1 G-inputs; every even output lies strictly between adjacent powers 7*2^n and 14*2^n. Remaining odd outputs give genuine parents at strictly higher cost, so strong induction on K-m excludes every authentic reachable cone state. The original critical target reduction then excludes Reach 2 (14*2^n-2*n-10) for even n. The final source declarations must pass the pinned original dependency closure before reporting original-source acceptance.

## Finite results

| n | Empty K | Minimum left-margin bit length (experiment) | Layer attaining minimum | Kernel right-five and margin | Blank reset wrapper |
|---:|---:|---:|---:|---|---|
|30|82|19|38|accepted|pending|
|286|1442|271|1319|not yet accepted|pending|
|350|586|335|438|accepted|pending|
|1614|5824|1597|2568|not yet accepted|pending|
|2990|6154|2973|3787|not yet accepted|pending|
|3342|13730|3320|7084|not yet accepted|pending|

[margin_scan.py](margin_scan.py) is an exact-integer experiment for all six cases; it asserts emptiness, carry-two avoidance and the required margin at every earlier layer. The modular screen for the other indices ≤10000 is Agent28's independent work. The complete range still needs a combined original-source certificate, including all six exceptional rows.

[gen_margin_cert.py](gen_margin_cert.py) generates untrusted literal checkpoints and kernel-checked composition proofs. Use `python gen_margin_cert.py 350 586 16` from a temporary directory, then Lean with LEAN_PATH including this dossier. The locally compiled margin350 used the same checkpoint data and equivalent theorem calls with the literal requiredMargin argument rather than the helper definition. The generator's new helper definition is definitionally equal. The n286 full literal file (1.7 MB) hit a memory limit with default parallel elaboration; a serial run was stopped after 4m29s to preserve RAM for the stronger margin checks, not a mathematical counterexample. For large cases investigate segmented independent compilation or a more efficient certifier.

## Previous right-five-only certificate

[CarryCert.lean](CarryCert.lean), [gen_carry_cert.py](gen_carry_cert.py), [CarryCertSource.lean](CarryCertSource.lean). The source integration CI above accepted n30 and n350. These are retained for comparison and dependency history; the margin certificates strictly strengthen the finite arithmetic claim.

