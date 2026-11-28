# F321 parity-aware modulo-384 source-counter quotient

**Source-kernel theorem (28 November 2026; accepted in [CI 46124258798](https://github.com/FlareZ123/bb6/actions/runs/46124258798), standard axioms only):** The exact F321 source-counter map, started from the authentic seed `(1,1)`, can reach a halting gate `(d+1,d)` only if

```
d mod 384 ∈ {37,61,115,133,139,157,181,211,229,235,253,277,325,331,349}.
```

The complementary 369 residue classes are excluded **at every finite counter-map time**, without a lower-index cutoff. This is a pure source-counter claim, not an original six-state tape-machine decision or a BB(6) solution. Its prospective density `369/384=123/128` is stronger than the earlier `275/288` fixed-ray exclusion as a standalone infinite-progressions certificate, though neither decides the remaining gates.

## Sound abstraction

The authentic source rule has the five nonhalting branches High, Far, Equal, middle-even and middle-odd. After the unique initial Equal step `(1,1)→(6,1)`, project coordinates modulo 384. On each residue pair `(x,y)`, allow High `(x-y-2,2y+3)`, Far `(4x+6,y-3x)` without inequalities. Allow a middle output `(4x+6,2)` only when `x+y` is even, and `(4x+6,1)` only when `x+y` is odd. Allow Equal `(2x+4,1)` only when `x=y` modulo384. All arithmetic is reduced modulo384. The retained parity condition is sound because `(d-a) mod2=(d+a) mod2`; the corresponding F321 source middle rule uses exactly that parity. The dropped inequalities overapproximate the authentic transition graph.

An independent straightforward breadth-first fixed point produces **7,414** reachable residue pairs of `384²=147,456` after the initial step, and projects to precisely the **15** halting-gate residues displayed above. The `147,456`-bit certificate is encoded as a hexadecimal natural in `Mod384Graph.lean`, with universal closure, seed membership and terminal residue enumeration checked by `by decide +kernel`. `Mod384Source.lean` transports this certificate through the actual `BB6.Agent31F321Density.CounterMove` relation and derives an all-time source reachable-gate theorem. All of these graph and source-counter theorems passed the complete source CI on commit `12776a5a17f5eeeb832c85143f54f1bb2a878d7d`; `#print axioms terminal_mod384_candidates` lists only `[propext, Classical.choice, Quot.sound]`, without `sorryAx`.

## Reproduction and status

Run `node im-results/agent31-f321-mod384/verify.cjs` to independently rebuild the graph and compare the embedded exact mask. Manual GitHub workflow `.github/workflows/agent31-f321-affine-terminal.yml` with input `mod384_only=true` checks the graph and source theorem under Lean 4.36.0-rc2. The source relation is the previously compiled faithful counter map, distinct from the upstream DeepMind tape-machine bridge. See [the mathematical result](../../results/2026-11-28-f321-parity-aware-mod384-source-gate-exclusion-agent31.md) for the theorem, proof, acceptance log, and unresolved machine-level quantifier. No fake source-step bound, historical plain residue count, or conditional weighted Cover is claimed here.

**Next substantial edge:** if this source quotient is accepted, use the same sound parity-sensitive abstract transition rule to build a *parametric* finite quotient checker and consume a higher modulus without duplicating hundreds of thousands of unrelated theorem statements; in parallel search for a well-founded authentic inverse invariant that removes the remaining possible gates at all indices. Exploratory computations at moduli 1,536 and 6,144 still leave nonempty candidate sets; they are not currently proof certificates.
