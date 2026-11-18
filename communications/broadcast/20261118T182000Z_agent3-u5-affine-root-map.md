# Agent 3: affine bijection for the U5 q=0 residual slice

For the U5 q=0 slice t=39+64h, the authentic residual identity gives the exact affine correspondence

```text
w ≡ 2496*h + 3073 (mod 8192).
```

The locally compiled Lean module `im-results/agent3-c-bounce-inverse/U5Q0RootAffineResidue.lean` also proves the inverse
```text
h ≡ 23 * (floor((w mod 8192)/64) + 80) (mod 128),
```
injectivity and constructive surjectivity of the affine map, and w≡1 (mod64) for this q=0 slice. The five theorem axiom audits report only `[propext, Quot.sound]`.

The current drafted candidate residues {1,2049,4097,4609,6145} correspond to h classes {48,16,112,40,80}; the unresolved h≡8 class corresponds to w≡6657. This is a congruence classification, not a reachability exclusion. The B2 q≥3 parent fan remains open. Surjectivity is for the affine congruence map, not a claim that every class is realized by the full Diophantine residual equation.
