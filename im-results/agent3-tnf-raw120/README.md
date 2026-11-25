# Raw120 E0=0RF: source-checked exhaustive cylinder and three new growth invariants

Raw120 parent: `1RB---_1RC---_0RD---_1LD1RE_---1LE_------`. First undefined row E0 at ordinary time 9. This dossier addresses its E0=0RF child only; other E0 choices remain open here.

## Exact child result

All 25^5 = 9,765,625 raw completions of that child are accounted for by the exact first-hole enumeration: 1563 splits, 26299 cycle leaves, 5858 last-hole leaves, 3793 initially open leaves. The open-list SHA256 is bda880d33c84532152766ab55afccf0744461e91eb337a3badecb8719f1a68dc. Of the 3793, 3761 have FAR witnesses (29 reusable DFAs), 27 have one-block growth proofs, one has a two-block growth proof, three have new parametric invariants, and one halts. The exact weighted threshold for this child is **14416**.

The late table `1RB1LF_1RC1RF_0RD1RB_1LD1RE_0RF1LE_---0LA` reaches its only hole F0 after 14415 ordinary transitions with zero initial delay. Thus a blanket 7014 weighted bound for raw120 is false. This is not a new BB(6) lower bound competitive with the champion. Use the mixed-bound roster composition at the final champion bound, rather than require each residual to have bound 7014.

## Source-linked verification

The existing manual target `weighted-tnf-raw120-rf` passed in [CI run 45520792124](https://github.com/FlareZ123/bb6/actions/runs/45520792124), on source commit `72d380da6ee9062827a0df0fb4d7840cea88bec3`. Its dedicated `raw120` job regenerated the RF tree, compiled the source-linked dependency closure, and finished successfully. The closure compiled 79 project modules, including `Raw120Late`, the 24 generated RF child modules, and `Raw120RFData`.

The generated final theorems are:

- `allRF`: every machine compatible with the E0=0RF child satisfies `WeightedBound 14416`.
- `exactRF`: for every `T`, all compatible machines satisfy `WeightedBound T` iff `14416 ≤ T`.

The job printed the axiom profiles of `c_root`, `allRF`, and `exactRF`; each used only `propext`, `Classical.choice`, and `Quot.sound`. The workflow also rejects `sorryAx` and `native_decide`, and that guard passed. This is original-source Lean acceptance of the complete E0=0RF child certificate, not merely a local preflight.

## Placement in the global residual frontier

The parent `p120` is canonical residual **84** (raw residual index **120**) in `im-results/agent13-roster-convergence/canonical-124.json`. Its exact address is B0=1RC, C0=0RD, D0=1LD, D1=1RE, E1=1LE, leaving E0 as the first hole. It is not among the 15 residuals removed by the accepted FiveHoleRoster and AllTwelveRoster cuts, so it remains one of the 109 obligations in `Combined109Roster.reducedRoster`.

The accepted `allRF` theorem covers only the E0=0RF child of this residual. It does **not** close the parent `p120`; the other E0 alternatives still require a complete sibling cover before residual 120 can be removed from the 109-way maximality obligation.

## Proof structure

- `Raw120Late.lean`: exact source-linked late query, attaining completion and lower bound.
- `Raw120Counter.lean`: leaf 1201, ternary counter with arbitrary right suffix, three-cell digit carry, positive growth recurrence for every length.
- `macro.py`, `M2140Invariant.inc`, `M2146Invariant.inc`: two nested sweep leaves, complete remainder-case coverage on alternating blocks and unary tails. The invariant allows a variable number of alternating blocks rather than a fixed period.
- `bank.txt`: compact reusable FAR candidate bank.
- `generate.py`: regenerate the pinned tree, use exact FAR masks and symbolic witnesses, and generate chunked Lean certificates with the original source checker. Its `Raw120RFData.lean` target expresses `allRF` and `exactRF`.

## Reproduce

From repository root: `python im-results/agent13-coverage/unpack.py`, then `python im-results/agent3-tnf-raw120/generate.py`, then `python tools/lean_compile_closure.py --workdir /tmp/a3-raw120 --jobs 4 im-results/agent3-tnf-raw120/rf/Raw120RFData.lean`.
