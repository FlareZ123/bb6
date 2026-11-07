# Machine C: all-time reset-index exclusion at 184 modulo 1024

Agent 34, 2026-11-02. Status: **source-level Lean-kernel verified; genuine additional infinite residue class compared with the previously published modulo-1024 quotient census.** This theorem does not decide the Machine C holdout or BB(6).

## Statement and significance

The original six-state two-symbol Turing machine is `1RB1LC_1LC1RD_1LA0LB_0RB_1RE_1RF0RA_---0RC` (canonical compact notation without internal separators: `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`). Its published acceleration, independently connected to the original machine by Agent 21, begins at `(5,0,1)`.

The exact `BB6CLine.Reach` relation is inductively defined by the unmodified `BB6CLine.nextC` in `im-results/agent11-c-line/CLine.lean`.

**Proved for every natural number t:**

```lean
BB6.Agent34C.reset_mod1024_184_unreachable (t : Nat) :
  ¬ BB6CLine.Reach (2048*t+369,3072*t+556,0)
```

This universally excludes all reset gateways `(2j+1,3j+4,0)` with `j=1024t+184`. It is not a finite simulation or a bounded-time statement.

Agent 41's previous, independently double-computed modulus-1024 abstract reachability census in `im-results/agent41-c-quotient512/README.md` excludes 678/1024 reset indices but **does not exclude residue 184**; the earlier quotient leaves that entire residue family undecided. Thus this is an additional mathematically established infinite exclusion beyond the recorded finite-quotient findings.

## Complete symbolic predecessor method

An arbitrary reached hub `(A,2,C)` with `A>=5,C>=4` has one of exactly three possible predecessor classes, established in `Agent34CInverse.lean` from source-certified CBack and CHubSplit lemmas:

1. **Reset:** `C=2k`, with reached `(A+3,k,0)`.
2. **Even portal:** `k` even, `A=2k+2`, with reached `(0,k,C+3)`.
3. **Odd portal:** `k` odd, `A+2=2k+3`, with reached `(0,k,C+2)`.

Any reached zero-right `(a,k,0)` with `k>=7` entails reached hub `(a+k-5,2,k-2)`; any reached zero-left high `(0,k,c)` with `k>=3,c>=4` entails reached hub `(k-2,2,c+k-2)`. These two universally quantified rewinding rules are already proved against the original counter-map source.

The 19-node symbolic inverse tree in `CReset184.lean` exhausts every applicable predecessor branch. All branches terminate by one of two globally preserved arithmetic contradictions:

- **Odd reset hole:** For reachable `(a,k,0)` with odd `k>=5`, `(a+k)%4` must equal 0 or 3. Two terminal ancestors have `(a+k)%4=1`.
- **High zero-left invariant:** At reachable `(0,k,c)` with `c>=4`, either `(k+c)%2=0` or `k%4` is 0 or 1. The third terminal ancestor violates both alternatives.

There are no synthetic reachability assumptions, finite search cutoffs, induction hypotheses about the candidate class, or symbolic leaves omitted by the proof.

## Exact verification and reproducibility

Complete SHA-256-checked Lean sources are archived under [`im-results/agent34-c184/`](../agent34-c184/). The atomic reconstruction tool `reconstruct.py` verifies both source-file hashes and compressed-archive hash before extracting. The exact source digests are:

- `Agent34CInverse.lean`: `31086a2618a6674a018947fe63b3f1194232db15440b5804aaed1fe14cfaa9d1`.
- `CReset184.lean`: `8525710bcd08741dcc67c1e7e403a2432d0e4c9b3a3aaf254cb0f2e5fcb176ef`.
- `agent34-c184.tar.xz`: `84a19b58221f3a8afa04bf0cb226904f4a6d64c5ba0b67c275720d1240c98b6b`.

[Manual-only GitHub Actions workflow](../../.github/workflows/agent34-c184.yml) reconstructs the proof, compiles the **unmodified** original `CLine.lean`, `CReachBridge.lean`, `CRange.lean`, `CBack.lean`, and `CHubSplit.lean` modules, then the two new proof modules with Lean **4.36.0-rc2**.

**Complete successful CI [run 41414247446](https://github.com/FlareZ123/bb6/actions/runs/41414247446)**, at source commit `6d06f9a5e57b032ee72fa85f39879fde7d70fc1a`, finished with status success. Its final axiom audit reads `[propext, Classical.choice, Quot.sound]`, without `sorryAx`, and no mocks are included in CI.

The exact raw-machine/accelerator semantic equivalence was independently certified by Agent 21's [successful pinned upstream run 41389979481](https://github.com/FlareZ123/bb6/actions/runs/41389979481). This new result concerns an infinite subset of the necessary halting gateway candidates, leaving infinitely many others unresolved. No global Busy Beaver upper bound or exact BB(6) value follows.
