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

These four disjoint parameter classes occupy density `1/2097152` of all `(j,m)` pairs as an arithmetic lattice. Their independence from the source-certified ValSixFull+C58 all-depth stopping sieve and the later arbitrary-depth late three-cone gate is now established by a uniform modular comparison; the formal integration wrappers are drafted but still await their manual original-source CI run.

## Formal artifacts

- [CSixSeventhArithmetic.lean](CSixSeventhArithmetic.lean): complete inverse grammar specializes to exactly three possible parents, with second-level branching handled exhaustively
- [CSixSeventhStrict.lean](CSixSeventhStrict.lean): six authentic incoming source edges, no seven
- [CSixSeventhRoot.lean](CSixSeventhRoot.lean): true blank-origin all-time nonreachability, using the actual first seven section returns
- [CSixSeventhGate.lean](CSixSeventhGate.lean): original narrower high-stop subfamily (also certified)
- [CSixSeventhGateWide.lean](CSixSeventhGateWide.lean): four congruence classes pulled back through the exact high stopping equation
- [CSixSeventhC58.lean](CSixSeventhC58.lean): prior-sieve admission and strengthened exact C58 all-depth iff; pending original-source CI

All five were checked against **unmodified original Lean machine and inverse source** by [CI 42720140809](https://github.com/FlareZ123/bb6/actions/runs/42720140809), success, with no printed `sorryAx`. The earlier widened source-image proof alone passed [CI 42719852275](https://github.com/FlareZ123/bb6/actions/runs/42719852275). The workflow is `.github/workflows/agent4-c-three-ancestry.yml`, restored to **manual-only** after successful checking.


## Independence from the integrated C58 all-depth sieve

The four high-stop classes are exactly equivalent to the single diagonal

```
j % 512 = 319
(3*m) % 4096 = (j+2879) % 4096
m >= 7
```

Reducing the second congruence modulo 512 gives `3*m = 126 (mod 512)`, hence `m = 42 (mod 512)`. The resulting residues are

```
j mod 256,128,64,32,16,8,4 = 63,63,63,31,15,7,3
m mod 256,128,64,32,16,8,4 = 42,42,42,10,10,2,2
```

This residue vector misses every conjunct of the preceding ValSixFull+C58 all-depth sieve:

- The original joint high rectangles fail: `(j+3*m+7) % 16 = 4`, the other `j % 4 = 1` gate has the wrong residue, the `m % 4 = 0/1` gate has the wrong residue, and `(j+3*m+5) % 8 = 2`.
- The Agent19 odd-special cylinder can only be its `j % 8 = 7` branch, where `(j+3*m+15) % 64 = 12`, not zero. The other three branches have incompatible `j % 8`.
- The Agent29 additions require `j % 8 = 5`, `j % 32 = 17`, `j % 64 = 57`, or `m % 32 = 6`; none holds.
- The ValSix additions require `m % 8 = 4`, `j % 128 = 81`, or `j % 32 = 1`; none holds.
- Agent19's arbitrary dyadic-depth gate requires `m % 4 = (2*r+3) % 4`, and the late three-cone gate requires `m % 4 = (2*r+1) % 4`; both right sides are always odd while `m % 4 = 2`.
- The Agent19 four-link condition has `(j+3*m+19) % 64 = 16), not zero. The remaining ValSixFull rectangles likewise miss: `(j+3*m) % 128 = 61`, `j % 8 = 7`, and `m % 32 = 10`.
- For the affine right-four guard, the exact stopping equation gives `k % 4 = 2), while `(2*j+3) % 4 = 1`. Their sum is 3 modulo 4, so affine normalization does not fire and its right coordinate is not four.
- The C58 rectangle would require `(j+3*m+5) % 256 = 198`, but the diagonal gives 194.

Thus the family is not a re-description of a previously removed parameter class. The concrete progression `m=42, j=1343+4096*t` satisfies the diagonal for every `t : Nat`; it is an explicit infinite family admitted by the old all-depth predicate and rejected by the new source theorem.

[CSixSeventhC58.lean](CSixSeventhC58.lean) formalizes the residue derivation, admission by both the all-depth and late-fast predicates, and two strengthened exact halting iff statements. In particular, `prior_latefast_admits_six_seven_diagonal` proves that the diagonal also passes the executable arbitrary-depth late gate, while `blank_halts_iff_c58_late_fast_six_seven` adds it to the latest C58/late-fast exact criterion. The source exclusion itself was already certified in CI 42720140809; the new admission lemmas and integrated iff statements have been added to the manual-only [Agent 11 C58/late-depth workflow](../../.github/workflows/agent11-c-diagonal-late.yml), but **the integration has not yet been source-audited**. Keep this extension in `im-results/` until that check succeeds. The exact C58 low/high existential remains unbounded, and neither this family nor the integration resolves Machine C or BB(6).

The complete theorem statement, inverse branch arithmetic and density synthesis are in [the academic result](../../results/2026-11-09-machine-c-sharp-sixth-seventh-image-agent4.md). The original Machine C blank-halting problem and BB(6) remain open.
