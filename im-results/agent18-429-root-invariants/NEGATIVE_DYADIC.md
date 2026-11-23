# #429 29(mod32) final-burst feeder: high power minus linear, and inverse-tree obstruction

**Status (23 November 2026):** A new genuinely rooted, all-time **Lean theorem** excludes terminal burst lengths `18 <= n < 16255` conditional on the exact branch-7 final-burst equation. The full original-source wrapper is staged separately. The **unbounded feeder decision remains open**. The exploratory signed-inverse statements below are not a theorem about positive machine states, nor about BB(6).

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

For `k<126` (equivalently `n<16255`), the all-parameter sound `BB429Kernel.cert` at depth17 is `true` for **every one of the 126** affine cylinders

```
(A,a,B,b) = (131072, 32*(4092-3k)+29,
             262144, 64*(4092-3k)+55).
```

The single finite certificate and its genuinely blank-root consequence, `BB429Branch29BurstFloor.rooted_branch29_final_burst_floor`, are in [BB429Branch29BurstFloor.lean](BB429Branch29BurstFloor.lean), compiled **successfully** (axioms only `propext`, `Classical.choice`, `Quot.sound`) in [local-source CI 45121716046](https://github.com/FlareZ123/bb6/actions/runs/45121716046). Thus `n>=16255`; this holds for **any** possible actual source time and any `q`, rather than a sampled orbit prefix. It is a necessary terminal-gate bound, not a halt/nonhalt decision.

## The open uniform negative-dyadic reduction

Solving the same exact integer equation gives

```
n=127+128k,   c=3k+4,
q=3*2^(n-5)-c.    (k>=0, c>=4)
```

For every integer exponent `E<=n-5`, the genuine unknown q has the exact dyadic residue

```
q ≡ -c (mod 2^E).
```

Consequently the root can be ruled out for any particular k **without constructing a huge `q`** whenever the existing source-sound affine kernel certifies

```
BB429Kernel.cert d
  ⟨32*2^E, 32*((-c) % 2^E)+29,
   64*2^E, 64*((-c) % 2^E)+55⟩ = true.
```

In theory, a **uniform proof** of existence of suitable `d,E<=n-5` for every `k>=0` would exclude this entire branch29 final-burst feeder, vastly stronger than ever-longer fixed-modulus residue filters. No such theorem has been established.

The [reproducer](negative_dyadic_scan.cjs) executes a *separate JavaScript BigInt translation* of the six `Bad` leaves and `F/S/E` from the previously Lean-proved `BB429InverseKernel.lean` (Agent 33), at constant `E=64`, `d=100`. Testing `k=0,...,999999` returned 1,000,000 `true` certificates and no unknown case. At `E=28`, in the first 100,000 k, the three unknown indices were `15382,65087,91006`; all were excluded at `E=48`. These are **experiments**, not a proof of the all-k claim, and there is no independent Lean verification of the million evaluations.

An independent signed-inverse prototype (not checked in as formal theorem) tested c from 1 through 1,000,000 at inverse depth100, finding only c=1 unclosed. The actual feeder requires c>=4. Nonetheless this sample is weak evidence for a universal conclusion; any proof must account for exceptional infinite signed inverse trajectories described next.

## What the limiting signed inverse tree actually says—and does not say

For an arbitrarily high power `2^E`, every bounded-depth inverse expression has a `2^E` coefficient and a signed constant part `(a,b)`. For the target q=-c, that constant pair is

```
(a,b)=(29-32c,55-64c),      b=2a-3.
```

The signed *algebraic* inverse rules (when integral) are

```
F(a,b)=((a-3)/2, b+a)
S(a,b)=((4a+b-26)/4,(b+4)/2)
E(a,b)=((4a+b-14)/4,b/2).
```

The source-sound **positive** affine kernel additionally requires appropriate lower bounds, coefficient divisibility and positivity; merely iterating these signed formulas is not a source-root proof. For a fixed finite inverse depth those guards can sometimes be justified by taking `E` sufficiently large relative to the negative constants, but no uniform bound across all k and depths is yet proved.

**Counterexample to indiscriminate signed inverse termination.** There exist infinite valid signed parity-word trajectories that dodge the six original residue-Bad leaves. The exact affine identity for any integer `a≡5 (mod8)` is

```
(a,a+8) --F,S,F,E--> (a-8,a) = (a-8,(a-8)+8).
```

For example, `(-323,-315) -> (-331,-323) -> ...` after four-letter blocks forever. Similarly:

```
(a,a+12) --F,E,F,S--> (a-8,a+4)       [a≡3 (mod8)],
(a,4a+18) --E,F,S,F--> (a-4,4a+2)     [a≡2 (mod4)],
(a,4a+14) --S,F,E,F--> (a-4,4a-2)     [suitable parity guards].
```

These are **signed** model paths extending toward negative infinity; they do not imply any genuine blank-reachable state (the real machine counters are Nat, and rank strictly increases on forward steps). They invalidate an overbroad proposed proof strategy that *all* negative signed pair inverse paths terminate. The exact special line `b=2a-3`, with `a=29-32c` and `c>=4`, must instead be proved disjoint from every possible infinite signed inverse path and its ancestors.

The special `c=1` gives `(a,b)=(-3,-9)`, with an endless F spine, since `F(-3,b)=(-3,b-3)`; this is outside the authentic feeder `c=3k+4>=4`. With fixed positive c>1, the uninterrupted initial F spine stops after `5+v_2(c-1)` steps (at which its first counter becomes even); alternative S ancestors remain open. In particular a mere first-spine argument is insufficient.

## Most valuable next result

Prove a nonperiodic, parameter-sensitive inverse theorem for the **special line**, ideally a well-founded induction on `c=3k+4` which accounts for all F/S/E forks (including cycles with drift). Alternatively derive a true blank-root history invariant that distinguishes it from the other signed surviving rays. Use the existing sound Boolean kernel to check finite proof obligations and original source bridge, but prioritize a theorem for **all k**, not another fixed-modulus residue list. Agent33, the affine inverse kernel's author, was contacted in `communications/agent33/` with the uniform reduction and cycle caveat.
