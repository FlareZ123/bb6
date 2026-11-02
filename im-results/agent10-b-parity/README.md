# Machine B scalar parity coding: exact Lean proofs

Agent 10, 2026-11-02. This is **intermediate** research. Machine B's blank-entry halting criterion and exact BB(6) remain unresolved.

The underlying scalar map from Agent 18 is `G(z)=3*(z/2)+4+5*(z%2)`.

[Agent10BParity.lean](./Agent10BParity.lean) proves parity-sequence aperiodicity, independently duplicating an existing theorem in Agent 18's `BParity.lean`. **This is prior work**, with no novel mathematical claim.

[Agent10Shift.lean](./Agent10Shift.lean) proves the complete input-translation identity for all natural n,z,d:

```
iterG n (z+2^n*d)=iterG n z+3^n*d.
```

It proves that finite parity-prefix equality is exactly equivalence modulo 2^n, and a shift by 2^n flips the next bit. [Agent10FullShift.lean](./Agent10FullShift.lean) constructively proves every binary n-word is realized by an initial z less than 2^n. The n-bit parity map is consequently a bijection on residues modulo 2^n. These are familiar generalized Collatz coding phenomena; novelty has not been established.

The exact source chain passed [manual Lean CI 41518735155](https://github.com/FlareZ123/bb6/actions/runs/41518735155), including original unmodified Cryptids Machine B, Agent 18's original definitions, and [Agent10BSource.lean](./Agent10BSource.lean). All new printed final theorem axioms were [propext, Quot.sound], without sorryAx.

[Agent10Growth.lean](./Agent10Growth.lean) proves G(G(z))≥2z+10 and 10*2^(m/2)≤iterG m 0+10. [Agent10GrowthSource.lean](./Agent10GrowthSource.lean) transfers this to Agent 18's syntactically continued reset indices A(n), proving 10*2^(A(n)/2)≤A(n+1)+4, A(2)=227097, and 10*2^113548≤A(3)+4. Source-level CI for this last extension is pending verification.

The original-machine halt condition samples parity only at recursively defined indices A(n). Arbitrary-input coding and reset-index growth do not decide those particular sampled bits, so neither Machine B nor BB(6) is classified.
