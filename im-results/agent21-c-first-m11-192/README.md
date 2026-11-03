# Machine C first halting family: a mixed-192 all-time reverse invariant

Agent 21, 3 November 2026. **Rigorous local Lean 4.36.0-rc2 proof against an exact transcription of the unchanged `BB6CLine.nextC` definition.** The independent untouched-repository-source [manual CI run 41738935418](https://github.com/FlareZ123/bb6/actions/runs/41738935418) is dispatched; until its successful compilation is confirmed, the original-source verification boundary remains open. Machine C and BB(6) are still open.

## Mathematical claim

For the genuine blank-start accelerated Machine C source `BB6CLine.Reach`, started at `(5,0,1)`, the theorem is:

```lean
theorem B192.first_91_mod192_unreachable (k : Nat) (hk : k % 192 = 91) :
  ¬ BB6CLine.Reach (1,k,0)
```

The complete Lean file is archived as [FirstM11.lean.xz.b64](FirstM11.lean.xz.b64), with [reconstruct.py](reconstruct.py) decoding it atomically under lock and checking exact SHA256 `e12563a3f68b46167bd967df22afd5bc46c274652e37d7f17524ea2db154890b` (12,182 bytes). It is a fully quantified, finite-cutoff-free negative reachability claim.

The genuine Machine C *first* immediate-stopping family, previously source-certified by Agent15, has `a=1` and `k+3m+4=2^(2m+3)`. For any `m%64=11`, the right side modulo 192 is 128, `3m%192=33`, and therefore `k%192=91`. **Conditional on the original-source CI import and the established Agent15 source bridge**, every such candidate section-gateway lies in the unreachable cylinder. This is an entire infinite first-halting-index congruence class, unlike the earlier individual m=24 mod32 check, which was already covered by Agent3/Agent11. A separate source-composed halting-parameter theorem has not yet been compiled.

## Backward-closed core (all natural counters)

Define `bad(a,k,c)` via `w=k+c` when `c<2`, `d=(a-c)%96` (ordinary modular subtraction) and `t=(a+k)%192` when `c>=2`.

* Low phase: special `(a%192,w%192)=(1,91)`, or any of nine `(a%96,w%48)` pairs: `(12,32),(18,27),(33,17),(42,15),(44,18),(60,8),(66,3),(81,41),(90,39)`.
* High phase: `(d=5,t%96=43)`, or `(d=94,t=89)`, or sixteen `(d,t%48)` pairs: `(9,41),(11,38),(15,42),(16,43),(30,47),(39,6),(40,7),(41,11),(57,17),(59,14),(63,18),(64,19),(78,23),(87,30),(88,31),(92,32)`.

The local Lean proof establishes `bad(nextC(s)) → bad(s)` for **every** actual defined step, through all branches and small-counter cases, using `omega` in universally quantified lemmas. It proves `¬bad(5,0,1)`, full pointwise equality of its normalized `nextC` to original `BB6CLine.nextC`, and induction over genuine `Reach`. A separate 192/192/96 quotient experiment, inspecting 28,459,008 representatives, finds the proposed reverse ancestor component has precisely **13,010** abstract vertices, excluding the root (73 each at `c=0` and `c=1`, and 12,864 at `c>=2`). Those census numbers are **finite computational support**; the Lean all-natural theorem does not depend on their correctness.

## Verification and scope

Local Lean `#print axioms` for `backward`, `nextC_eq_source`, `blank_avoids_bad` and `first_91_mod192_unreachable` reports only `[propext, Classical.choice, Quot.sound]`, with no `sorry`, `admit`, `native_decide` or external axioms. Local `CLine` included the exact original transition and reachability definitions, but omitted unrelated original source lemmas. The [manual-only CI workflow](../../.github/workflows/agent21-first-m11-192.yml) reconstructs the SHA-checked complete proof and compiles it against the **full untouched checked-in** [CLine.lean](../agent11-c-line/CLine.lean). This separate check is essential before treating the theorem as source-certified.

Previous work to audit for novelty includes Agent3's low-gate grammar, Agent11's first-family arbitrary-depth exclusions, Agent15's M8/M16 filter, Agent4/Agent38's mixed96 reverse cores, and Agent4's concurrently explored mixed192 second-family cores. At the time of discovery, no specific older `m%64=11` or `(1,91,0)%192` exclusion was located, but independent review of implication/subsumption is pending. The target is blank-root-specific and strictly avoids claiming nonhalting of the entire Machine C or any BB(6) bound.

**Next:** verify original full-source CI; add the exact `m%64=11` corollary to Lean; independently compare the new exclusion to all earlier Machine C symbolic and quotient filters. Then pursue a new surviving first-family class rather than repeated residue arithmetic.
