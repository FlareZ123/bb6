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

## Source-certified reset-index and modular results

[Original-source CI 41521215695](https://github.com/FlareZ123/bb6/actions/runs/41521215695) passed the exact all-natural bound `10*2^(scalarA n/2) ≤ scalarA(n+1)+4`, the explicit `A2=227097` and `10*2^113548≤A3+4`, and `2*tower n≤scalarA(n+1)` where tower0=2 and tower(n+1)=2^(tower n). All are for the syntactically continued scalar sequence, without an assumption that every reset is physically reached.

[Original-source CI 41522205598](https://github.com/FlareZ123/bb6/actions/runs/41522205598) checked [Agent10ModSeven.lean](./Agent10ModSeven.lean), [Agent10SevenReset.lean](./Agent10SevenReset.lean), and [Agent10RootModSeven.lean](./Agent10RootModSeven.lean) against the unchanged Agent 18 and Cryptids sources. It proves:
- `(iterG n 0+1)%7=5^n%7`, using a parity-independent mod-seven conjugacy.
- `scalarA n%6∈{1,3}`, for all n.
- `IsHalt Source.target ↔ ∃ n, scalarA(n+1)%7∈{0,6}`, an exact original six-state halting iff that reformulates Agent18's sampled-parity gate. Machine B is still undecided; no sample can be assumed zero.

## Finite third-sample verification

The deterministic [generate_long_sample.py](./generate_long_sample.py) produces 23 Lean files `SamplePart0.lean` through `SamplePart22.lean` with 455 linked checkpoints, each verified by kernel `decide`. Every segment covers up to 20 blocks of 500 exact `G` iterations. The last block certifies `(iterG 227097 0)%2=1` under theorem `third_sample_odd`. All 23 segments **passed local Lean 4.36.0-rc2**, with printed axioms `[propext, Quot.sound]`, no sorry, and final source value matching an independently computed SHA256 fingerprint of the resulting integer: `cd40bdc88b3579c8de7a31d0c818ab5bfe74073909d9a7c0078d84875a48da07` (little-endian bytes). The [Agent10ThirdBridge.lean](./Agent10ThirdBridge.lean) connects the finite certificate to Agent18's exact original scalar `scalarA 2=227097`. A manual original-source CI build is in progress; do not claim source-level certification for this last bridge before the run succeeds.

This is a very long **finite** verification. It does not establish any all-time nonhalting claim and is not a BB(6) bound.
