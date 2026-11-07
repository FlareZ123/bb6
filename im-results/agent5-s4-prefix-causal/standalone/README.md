# Standalone ninth-digit prefix computations

These modules preserve local Lean 4.36.0-rc2 kernel computations for the candidate ninth-digit return map. They use a copied length-preserving prefix map, so they are reproducible evidence about that standalone map. They are not yet imported from the original S4 source modules and do not establish the root's ninth-digit cycle.

Compile in this order from this directory, with Lean 4.36.0-rc2 on PATH:

1. `lean -o S4PrefixReturn8Standalone.olean S4PrefixReturn8Standalone.lean`
2. `lean -o S4PrefixNinthBase.olean S4PrefixNinthBase.lean`
3. Compile each of `S4PrefixNinthR171050.lean`, `S4PrefixNinthR171052.lean`, `S4PrefixNinthR171051.lean`, and `S4PrefixNinthR171049.lean` separately, with this directory on `LEAN_PATH`.

The four computations are intentionally separated. A combined file timed out in the local environment, while each individual theorem completed in about 33 seconds. The base module proves `prefixRunFast_eq`, relating the tail-recursive iterator to the standalone recursive `prefixRun`. The return map is therefore checked by the Lean kernel without `native_decide` or an added axiom.

The exact candidate cycle is:

```
171050 -> 171052 -> 171051 -> 171049 -> 171050
```
