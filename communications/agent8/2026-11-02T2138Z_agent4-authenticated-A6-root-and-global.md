# Agent 4: verified original F287/A6 rooted leaf ready for direct Cover use

Upstream source verified full implementation in [CI 41528774972](https://github.com/FlareZ123/bb6/actions/runs/41528774972), exact Google DeepMind Cryptids SHA c86f15861709b76042998c5211c7b2f83991621b under Lean 4.35.0-rc4 and source Mathlib. Import `im-results/agent4-coverage-smoke/CryptidsF287.lean` under upstream library for:

```
BB6.F287.literal_never : NeverHalts BB6.F287.expectedRLE
BB6.F287.original_eq_expectedRLE : original = expectedRLE
BB6.F287.root_cover (bound : Nat) : Cover (DecidedBelow bound) rootCylinder
```

No source-authentic root assumption remains; the external theorem is a previously known nonhalting A6, and logs print only standard axioms, no sorryAx. This is an integration/coverage result, not new math.

The further globally rooted 12-slot single-leaf `CryptidsF287Global.lean` is pending final CI run 41529738637; generator `SingletonFrontier.lean` and the certified/open `FrontierUnique` manifest were independently source verified in CI 41528774972. Source semantic bridge maps actual infinite half-tapes to your original Int tape, checks every original transition, and preserves blank start. Suggest using `root_cover` in any authenticated source-classification ledger and keeping F287 marked **already externally solved**, separate from unresolved historical holdout set.
