# #429 29(mod32) final-burst feeder: high power minus linear, and inverse-tree obstruction

**Status (24 November 2026):** The accepted genuinely rooted, all-time Lean theorem excludes terminal burst lengths `18 ≤ n < 16255`, conditional on the exact branch-7 final-burst equation. A stronger finite-range extension to `n ≥ 128000127` is present in code but is **not compiler/source accepted**. The unbounded feeder decision remains open. The signed-inverse analysis below is about an algebraic model, not positive machine states or BB(6).

## Rooted theorem, not finite-orbit sampling

Use the unchanged local source-root accelerated map `BB429.run ... (0,0)`. At a branch-7 final-burst last-reset state satisfying

```
u=32q+29,     w=64q+55,     w+3=2u,
128q + 3n + 131 = 3*2^(n+2),  n>=18,
```

the exact power equation modulo `2^19` yields

```
n=127+128k,
q ≡ 4092-3k (mod 4096).
```

For `k<126` (equivalently `n<16255`), the all-parameter sound `BB429Kernel.cert` at depth17 is true for every one of the 126 affine cylinders

```
(A,a,B,b) = (131072, 32*(4092-3k)+29,
             262144, 64*(4092-3k)+55).
```

The finite certificate and its genuinely blank-root consequence, `BB429Branch29BurstFloor.rooted_branch29_final_burst_floor`, were compiled successfully (axioms only `propext`, `Classical.choice`, `Quot.sound`) in [CI 45121716046](https://github.com/FlareZ123/bb6/actions/runs/45121716046). Thus `n>=16255) for any possible actual source time and any `q`; this is a necessary terminal-gate bound, not a halt/nonhalt decision.

## Open uniform negative-dyadic reduction

Solving the same exact integer equation gives

```
n=127+128k,   c=3k+4,
q=3*2^(n-5)-c.    (k>=0, c>=4)
```

For every integer exponent `E<=n-5`, the genuine unknown `q` has exact dyadic residue `q ≡ -c (mod 2^E)`. Therefore the root can be ruled out for a particular `k`, without constructing huge `q`, whenever the existing source-sound affine kernel certifies

```
BB429Kernel.cert d
  ⟨32*2^E, 32*((-c) % 2^E)+29,
   64*2^E, 64*((-c) % 2^E)+55⟩ = true.
```

A uniform proof of suitable `d,E<=n-5` for every `k>=0` would exclude the entire branch-29 feeder. No such theorem has been established.

The [reproducer](negative_dyadic_scan.cjs) is a separate JavaScript BigInt translation of the six Bad leaves and F/S/E rules from Agent33's Lean-proved `BB429InverseKernel.lean`. At `E=64,d=100`, it tested `k=0,...,999999` and returned one million true certificates; at `E=28), three unknown indices in the first 100,000 were excluded at `E=48`. These are experiments, not a proof of the all-k claim, and there is no independent Lean verification of the million evaluations.

## Unaccepted adaptive prefix extension

`BB429Branch29Prefix.lean` contains a proposed adaptive dyadic cover `cover_one_million` for all `k<1000000), using `BB429Kernel.cert 64` and a finite prefix tree. `BB429Branch29Source.lean` contains a wrapper intended to derive `rooted_branch29_final_burst_ge128000127`. This is a **candidate theorem in source files only**:

- Local manual CI [45416601834](https://github.com/FlareZ123/bb6/actions/runs/45416601834) ended with a runner shutdown before compiling the Prefix module; no compiler diagnostic was observed.
- Original-source chain CI [45124760705](https://github.com/FlareZ123/bb6/actions/runs/45124760705) failed after about 57 minutes. Failed-job logs were unavailable (HTTP 404), so no Lean error was established.
- The exact source wrapper has not been successfully compiled. Do not cite `n>=128000127` as an accepted source theorem.

Do not repeat the unchanged expensive computation. If the finite bound is still strategically useful, split/refactor its certificate into independently checked batches and then compile the exact original-source closure.

## Limiting signed inverse tree and the special line

For an arbitrarily high power `2^E`, every bounded-depth inverse expression has a `2^E` coefficient and signed constant part `(a,b)). For the target `q=-c), that constant pair is

```
(a,b)=(29-32c,55-64c),      b=2a-3.
```

The signed algebraic inverse rules (when integral) are

```
F(a,b)=((a-3)/2, b+a)
S(a,b)=((4a+b-26)/4,(b+4)/2)
E(a,b)=((4a+b-14)/4,b/2).
```

The source-sound positive affine kernel additionally requires lower bounds, coefficient divisibility and positivity. Merely iterating these signed formulas is not a source-root proof.

There are infinite valid signed parity-word trajectories that dodge the six original residue-Bad leaves. For example, for `a≡5 (mod8)`,

```
(a,a+8) --F,S,F,E--> (a-8,a) = (a-8,(a-8)+8).
```

The negative signed ray `(-323,-315) -> (-331,-323) -> ...` continues after four-letter blocks forever. These are not genuine blank-reachable states: real counters are natural numbers and rank strictly increases on forward steps. They invalidate the overbroad strategy that all negative signed inverse paths terminate. The special line `b=2a-3`, `a=29-32c`, `c>=4` must instead be proved disjoint from every possible infinite signed inverse path and its ancestors.

The special `c=1` gives `(a,b)=(-3,-9)`, with an endless F spine; it lies outside the authentic feeder `c=3k+4>=4`. For fixed positive `c>1), the uninterrupted initial F spine stops after `5+v_2(c-1)` steps, but alternative S ancestors remain open. A first-spine argument is insufficient.

## New exact congruence reduction: even F-runs

[Agent 18's derivation](SIGNED_F_RUN_PARITY.md) proves directly from the compressed block rules:

- Every maximal F-run followed by another pair block has even length. Hence every F-run on a hypothetical infinite path is even, using Agent22's result that such a path must contain infinitely many F-blocks and paired blocks.
- If the previous pair type is (P\in\{E,S\}) and the next is (Q\in\{E,S\}), then the F-run length is (2\pmod4) when (P=Q), and (0\pmod4) when (P\ne Q). The initial state acts as a virtual previous S-pair.

This is an exact hand proof, not yet formalized in Lean. It narrows the mixed-path problem but does not eliminate the mixed recurrent SCC. The derivation was sent to Agent22 for review and possible integration.

## Highest-value next result

Formalize the even-F-run reduction and use it to constrain the mixed recurrent SCC. The objective remains a well-founded, parameter-sensitive inverse theorem for the special line, or a genuine blank-root history invariant separating it from the other signed surviving rays. Prioritize an all-`k` result over another fixed-modulus residue list.
