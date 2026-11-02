# Agent 20: finite-quotient exclusions for BB(6) Machine C

**Status:** reproducible, computer-assisted mathematical evidence with an explicit simulation argument. This certificate has not yet been imported into Lean or independently reviewed. It does not decide Machine C, prove BB(6), or improve an accepted global bound.

Machine: `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. The exact published three-counter map is `im-results/agent11-c-line/CLine.lean`, with certified blank-entry `(5,0,1)`. Agent 21's CI run 41389979481 checks the map-to-original-machine bridge. Agent 11's all-time criterion says halting requires reachability of a reset gateway `(2j+1,3j+4,0)` for `j>=1` or a side gateway `(0,4n,24n+23)` for `n>=1`.

## New global candidate exclusions

The finite certificate excludes every reset gateway with `j>=4` and `j mod 64` in

```text
1,3,4,5,7,9,12,13,16,17,19,20,21,22,25,28,29,
33,35,36,37,39,41,44,45,48,49,51,52,53,54,57,58,59,60,61
```

It also excludes `j=1,3` individually. Relative to Agent 11's already proved `j mod 8 in {1,4,5}`, the **twelve additional infinite residue classes** are

```text
3,7,16,19,22,35,39,48,51,54,58,59 (mod 64).
```

It excludes every side gateway with `n>=2` and `n mod 64` in

```text
0,1,5,9,13,16,17,21,25,29,32,33,37,41,45,48,49,53,57,61
```

and the isolated `n=0,1` cases. In particular, the four **even** classes `n mod 64 in {0,16,32,48}` are excluded beyond the earlier odd-index parity barrier. Some overlap with other agents' recent work is possible. All remaining residue classes remain open.

## Exact finite abstraction and soundness argument

Set `B=8` and `M=64`. Define `q(x)=x` if `x<8`, otherwise `q(x)=8+((x-8) mod 64)`. Every natural counter is sent to an alphabet `Q={0,...,71}`, preserving all small values below eight and retaining residue modulo 64 for larger values. For a quotient coordinate `u`, use representatives `{u}` when `u<8`, and `{u,u+64}` otherwise.

Build an abstract directed graph on `Q³` by enumerating every Cartesian combination of coordinate representatives, applying the exact partial `nextC` counter map, and quotienting its defined successor. Thus each vertex has at most eight representative transitions.

**Simulation lemma:** every real counter transition `s -> t` induces an abstract edge `q(s) -> q(t)`. To verify, for any `x>=8` write `x=q(x)+64h`. Conditions in `nextC` only test small exact values `0,1,2,3` and parity of `k`; all these conditions agree for `x` and its representative. Output coordinates are unchanged, shifted by at most three, or obtained as `2k+d` for `-1<=d<=3`. If `h=0`, the representative `q(x)` gives the exact output. If `h>=1`, the representative `q(x)+64` has the same output quotient, since any shifted value remains at least eight and the difference is a multiple of 64. Doubled outputs also remain at least eight when their input `k>=8`; they differ by a multiple of 64. Coordinates below eight are reproduced exactly. Applying this argument independently to the three coordinates establishes the lemma for every branch. In the odd-`k` high-counter branch, `4*floor(k/2)+5=2k+3`, the identity used by the CJS program.

Consequently, the least forward-closed abstract set containing `q(5,0,1)` contains the quotient of **every** truly blank-reachable state, at arbitrary finite times. An abstract state *absent* from that closed set is rigorously blank-unreachable, conditional on the finite graph being computed correctly.

## Exhaustive certificate

Run `node c-quotient.cjs` using Node.js, with no external packages. It constructs the graph on **373,248** vertices, reaches **172,714** abstract vertices from the blank-entry quotient, traverses **1,182,347** abstract representative edges (duplicates included), and separately rechecks that the returned set is forward closed under every representative edge. It then checks every displayed excluded residue, plus small exceptions.

For reset targets `j>=4`, both nonzero coordinates are at least eight, so their quotients depend only on `j mod 64`. For side targets `n>=2`, the same holds. The exhaustive 64-residue check therefore establishes the entire stated infinite families via the simulation lemma, not via any finite stopping-time assumption.

**Limitations and next steps:** the arithmetic lemma and CJS verification have not been formalized inside Lean's kernel. A separately implemented finite certificate checker and formal source equality would provide stronger evidence. This remains an intermediate result under `im-results/`, and it leaves many possible gateway families unresolved. A global blank-reachability invariant or a stronger symbolic return-map theorem is still required to decide Machine C.
