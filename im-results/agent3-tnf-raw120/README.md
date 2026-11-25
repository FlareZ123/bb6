# Raw120 E0=0RF: exhaustive candidate and three new growth invariants

Raw120 parent: `1RB---_1RC---_0RD---_1LD1RE_---1LE_------`. First undefined row E0 at ordinary time 9. This dossier addresses its E0=0RF child only; other E0 choices remain open here.

## Candidate result

All 25^5 = 9,765,625 raw completions of that child are accounted for by the exact first-hole enumeration: 1563 splits, 26299 cycle leaves, 5858 last-hole leaves, 3793 initially open leaves. The open-list SHA256 is bda880d33c84532152766ab55afccf0744461e91eb337a3badecb8719f1a68dc. Of the 3793, 3761 have FAR witnesses (29 reusable DFAs), 27 have one-block growth proofs, one has a two-block growth proof, three have new parametric invariants, and one halts. The proposed exact weighted threshold is **14416**.

The late table `1RB1LF_1RC1RF_0RD1RB_1LD1RE_0RF1LE_---0LA` reaches its only hole F0 after 14415 ordinary transitions with zero initial delay. Thus a blanket 7014 weighted bound for raw120 is false. This is not a new BB(6) lower bound competitive with the champion. Use the existing mixed-bound roster composition at the final champion bound, rather than require each residual to have bound 7014.

## Proof structure

- `Raw120Late.lean`: exact source-linked late query, attaining completion and lower bound.
- `Raw120Counter.lean`: leaf 1201, ternary counter with arbitrary right suffix, three-cell digit carry, positive growth recurrence for every length.
- `macro.py`, `M2140Invariant.inc`, `M2146Invariant.inc`: two nested sweep leaves, complete remainder-case coverage on alternating blocks and unary tails. The invariant allows a variable number of alternating blocks rather than a fixed period.
- `bank.txt`: compact reusable FAR candidate bank.
- `generate.py`: regenerate pinned tree, use exact FAR masks and symbolic witnesses, generate chunked Lean certificates with the original source checker. Its `Raw120RFData.lean` target expresses `allRF` and `exactRF`.

Local Lean 4.36.0-rc2 checked the late query and the three hard recurrence proofs against copied executable zipper definitions (standard axioms only). Direct local repository checkout failed DNS, so this is a preflight, not acceptance of the imported source theorem closure. The manual agent13-coverage workflow has targets weighted-tnf-raw120-late and weighted-tnf-raw120-rf. Full source-linked CI dispatched; acceptance pending. No global residual count reduction or exact BB(6) result is claimed.

## Reproduce

From repository root: `python im-results/agent13-coverage/unpack.py`, then `python im-results/agent3-tnf-raw120/generate.py`, then `python tools/lean_compile_closure.py --workdir /tmp/a3-raw120 --jobs 4 im-results/agent3-tnf-raw120/rf/Raw120RFData.lean`.
