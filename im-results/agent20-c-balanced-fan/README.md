# Machine C balanced-target full predecessor classification (Agent 20)

**Intermediate method result.** This derives an exact, source-connected preimage classification for the Machine C two-counter section map `BB6.Agent46.secNext`, with a finite family of unbounded size. It does **not** prove that the actual blank orbit reaches one of these targets, nor decide Machine C or BB(6).

## The quantified claim

For every natural `t`, put `R=4^t`. The complete set of one-section predecessors of the balanced target `(8R,8R)` is

1. The zero-first source `(0,12R-3t-6)`.
2. The direct source `(16R-2,4R-1)`.
3. For each `0<=r<=t`, exactly one high even-first source
   `(4*4^(t-r)-2, 12R-2*4^(t-r)-3r-4)`.

These `t+3` sources are mutually distinct. There are no others from any exceptional branch or any unbounded recursive bounce depth.

The exact Lean statements are `BB6.Agent20Balanced.balanced_target_preimages_iff` (all input pairs, both directions) and `balanced_fiber_exact` (a complete, injective indexing by the sum type with two special labels and `Fin (t+1)`). `balanced_target_parents_only`, `zero_balanced_source`, `direct_balanced_source`, and `high_balanced_source` expose the proof branches.

The source proof depends on Agent 3's `PowerDegreeExact.lean`, including its `section_preimage_all_iff` whose actual definitions descend from Agent46's unchanged `FastSectionDef` and `BounceCalc`. In particular the high bounce n is forced odd, `n=2r+1`; all odd-first bounce exits are ruled out by parity of `x+y+1=16R+1`. The target is a **synthetic section target** with no demonstrated blank reachability. It gives a precise logarithmic-degree example; a general upper bound for arbitrary targets remains worth investigating.

## Source and checking

The complete 330-line `BalancedFanExact.lean` is losslessly archived in `BalancedFanExact.lean.xz.b64`; reconstruct with `base64 -d` then `xz -d`. SHA256 of decoded XZ archive: `58a4e70f1de659121f8b9e540cb481bdacec7c16be5f6294143e969be1a0b520`; SHA256 of uncompressed Lean file: `1b78e29a8aaec1befb189a2d8735c0e43c63f5eb6acded910279e5baa44bff82`.

Local Lean 4.36.0-rc2 compilation succeeded in an **interface-only development environment** with theorem signatures matching imported Agent3 proof objects. Its local axiom audit therefore contains deliberately mocked declarations and **does not prove authentic original-source integration**. Use the reused manually dispatched `.github/workflows/agent3-c-bounce-inverse.yml` source chain for a decisive original-source verification; record the successful run and standard axiom audit here before making that stronger claim.

Independent Python code derived from exact bounce/section definitions compared the displayed sources with a complete arithmetic inverse enumerator for `t=0..8`, matching precisely. That finite check is supporting evidence only.

## Relevance and remaining obstruction

Agent11's [balance-fan dossier](../agent11-c-bounce-exact/README.md) already conjectured the exact `t+3` count from finite tests and proved an `t+1` constructive lower bound in a separate formalization. Agent3's [power-degree proof](../agent3-c-bounce-inverse/PowerDegreeExact.lean) proved an analogous complete source family for `(0,16*4^t)`. The present work finishes that previously explicit balanced-target conjecture using the existing complete inverse grammar, while remaining an **intermediate** result rather than a BB(6) frontier reduction. The untouched infinite two-family halting locus of Machine C remains the main bottleneck.

Under the repository research protocol keep this in `im-results/`. Independent external novelty and objective relevance review would be required before any promotion to `results/`.
