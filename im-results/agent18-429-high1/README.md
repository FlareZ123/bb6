# Exact original-machine #429 high-one J branch (all natural parameters)

Status: source-exact Lean 4.36.0-rc2 verification: [source CI 42518401536](https://github.com/FlareZ123/bb6/actions/runs/42518401536) and [original physical CI 42518664104](https://github.com/FlareZ123/bb6/actions/runs/42518664104) SUCCESS; axioms audited, no `sorryAx`.

The original raw machine is `BB429PhysicalFrontier.target429`, with the canonical exact J tape `BB429JPhysical.jTape`. For every `u : Nat`, `BB429High1Physical.j_high1_to_junc_raw` in [High1Physical.lean](High1Physical.lean) proves

```lean
∃ c', BB6Coverage.run target429 (4*u*u+28*u+306)
    {state:=A,head:=0,tape:=jTape u (2*u+1)} = some c' ∧
  Represents (junc 11 0 (4*u+2)) c' ∧
  c'.head = 6-2*(u:Int)
```

The generic C/B sweep `j_c_sweep` accounts for `4*u*u+10*u+25` transitions. The new [High1Source.lean](High1Source.lean) theorem `high1_to_junc` accounts for the remaining `18*u+281` steps and exact signed head delta `5-4*u`. Its composition uses a seventeen-step E/1 entry, the even-parameter source E/1 revisit, a twenty-step C/1-E/1 preparation, an arbitrary-length E/1 sweep, and the previously certified `sourceScanE_finishC_even_after_junc0_delta`. The physical proof establishes the complete tape support after the C/B sweep and uses the existing physically sound zipper-interpreter bridge.

This closes the last missing near-boundary high-one J case, conditionally on a prepared J-family tape. It does not prove blank-origin J reachability or decide #429 or BB(6). See [.github/workflows/agent18-429-high1.yml](../../.github/workflows/agent18-429-high1.yml) for the original unmodified upstream compilation and axiom checks.
