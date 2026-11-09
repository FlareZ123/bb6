# Source-certified sixth-versus-seventh Machine C return image

The original Machine C first-return map `BB6.Agent46.secNext` has a new explicit **strict sixth/seventh source image**:

```
V(u,v) = (641 + 1024*u, 574 + 1024*v),  u,v ≥ 0, (u+v)%4=0.
```

Every `V(u,v)` admits six genuine consecutive source returns into it, but **no seventh**, regardless of source. It never occurs in the true blank section from `(5,1)`, at any return time. The family has ambient state-lattice density `1/4194304` and is disjoint from Agent4's older explicit all-depth and strict I4/I5, I5/I6 bands. This improves the documented Agent4 union to `66305/4194304`; neither density measures the fraction of halting machines.

There is also an exact high stopping obstruction for `m>=7`, with the original stopping equation `k+j+3*m+5=2^(2*m+2)*(j+3)`, on the following four residue pairs `(j mod 2048, (j+3*m) mod 4096)`:

```
(319,3517), (831,445), (1343,1469), (1855,2493).
```

These four disjoint parameter classes occupy density `1/2097152` of all `(j,m)` pairs as an arithmetic lattice. Their net independence from the strongest integrated stopping sieve remains unproved.

## Formal artifacts

- [CSixSeventhArithmetic.lean](CSixSeventhArithmetic.lean): complete inverse grammar specializes to exactly three possible parents, with second-level branching handled exhaustively
- [CSixSeventhStrict.lean](CSixSeventhStrict.lean): six authentic incoming source edges, no seven
- [CSixSeventhRoot.lean](CSixSeventhRoot.lean): true blank-origin all-time nonreachability, using the actual first seven section returns
- [CSixSeventhGate.lean](CSixSeventhGate.lean): original narrower high-stop subfamily (also certified)
- [CSixSeventhGateWide.lean](CSixSeventhGateWide.lean): four congruence classes pulled back through the exact high stopping equation

All five were checked against **unmodified original Lean machine and inverse source** by [CI 42720140809](https://github.com/FlareZ123/bb6/actions/runs/42720140809), success, with no printed `sorryAx`. The earlier widened source-image proof alone passed [CI 42719852275](https://github.com/FlareZ123/bb6/actions/runs/42719852275). The workflow is `.github/workflows/agent4-c-three-ancestry.yml`, restored to **manual-only** after successful checking.

The complete theorem statement, inverse branch arithmetic and density synthesis are in [the academic result](../../results/2026-11-09-machine-c-sharp-sixth-seventh-image-agent4.md). The original Machine C blank-halting problem and BB(6) remain open.
