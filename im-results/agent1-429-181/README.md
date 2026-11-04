# Agent 1: exact rooted 181 (mod 2048) exclusion for BB429

**Status 2026-11-04 23:56 UTC:** unchanged-repository-source Lean 4.36.0-rc2 proof passed [manual CI 41937453345](https://github.com/FlareZ123/bb6/actions/runs/41937453345). All printed final axioms are standard Lean logical axioms; no `sorry` is used.

For the original repository's exact `BB429.next` accelerator and its authentic blank-root seed `(0,0)`, the theorem `BB429No181mod2048.blank_halt_not_181_mod2048` proves:

```lean
∀ n a b : Nat,
  BB429.run n (0,0) = some (a,b) →
  b+1 = 2*a →
  a%2048 ≠ 181
```

The theorem excludes the **entire infinite** terminal ray `(a,b)=(2048*q+181,4096*q+361)` for all `q:Nat`. It does not assert that the actual blank-root run halts or does not halt.

## Proof mechanism

The source-checked `BB429NewResidue.odd_back` and `even_back` exhaust authentic inverse transitions in the relevant non-special odd and positive even sectors. Inverses from the proposed terminal ray force the following main spine, where each displayed pair abbreviates two affine functions of the same unrestricted `q`:

```
(2048q+181, 4096q+361)
→ (1024q+89, 6144q+542)
→ (512q+43, 7168q+631)
→ (256q+20, 7680q+674)
→ (2176q+185, 3840q+337)
→ (1088q+91, 6016q+522).
```

The second inverse branch at `(1024q+89,6144q+542)` would have parent `(2560q+218,3072q+273)`, contradicting the source-certified `BB429Mod8.Allowed` invariant. On the last spine node, its first parent `(544q+44,7104q+613)` violates `Allowed`; the other parent `(2592q+215,3008q+263)` has first counter 7 mod 8 and second counter 7 mod 8, contradicting `BB429RootMod16.rooted_not_7_7`. In all remaining spine steps the second inverse is arithmetically impossible. Thus the entire original-root terminal ray is unreachable.

Proof: [BB429No181mod2048.lean](BB429No181mod2048.lean). Exact dependency chain: repository `BB429Rank`, `BB429Mod8`, `BB429NewResidue`, Agent39's genuine-root `BB429RootEven8` and `BB429RootMod16`; no copied replacement for the original accelerator is used. Workflow: [.github/workflows/agent1-429-181-source.yml](../../.github/workflows/agent1-429-181-source.yml), dispatch-only.

## Relevance and limits

The root-sensitive exclusion falls in the previously surviving 53 mod64 source halting sector and is not counted among Agent1's earlier 1661/2048 and 893/2048 exclusions, Agent30's 38/1024 stage, or Agent39's new 1021(mod1024) family. Its external novelty has not been established. It is a necessary modular obstruction for one difficult machine, **not an independent whole-machine decision, a BB(6) upper bound, or the value of BB(6)**. Intermediate research therefore remains under `im-results/`.

An adjacent generated-proof pilot for 329 mod2048 is in [../agent1-429-2048](../agent1-429-2048). Review the full source-check CI before treating its status as proven. Further useful work should combine distinct surviving infinite-cylinder exclusions with an exact source bridge and seek a whole-root obstruction; avoid misrepresenting modular gate counts as solved machines.
