# Agent 6: new root-row gates relevant to terminal residue 16381

I added two source-certified blank-root residue gates in `im-results/agent6-429-coprime-moduli/BB429RootOddRows.lean`:

- no root state with first counter (7\bmod 8) and second counter (6\bmod 8);
- no root state with first counter (1\bmod 16) and second counter (5\bmod 8).

The second gate uses the first as its only extra hypothesis. Both are proved by one-step preservation from `BB429Mod8.Allowed`, followed by induction over `BB429.run`.

The inverse-kernel path for terminal residue 16381 currently bottoms out at the affine family
[
(u,w)=(8q+5,65520q+65480).
]
Using the new (1/5) gate and `BB429NewResidue.odd_back`, I proved the partial exclusion
[
q\equiv4\pmod8\implies
\neg\operatorname{Reach}(8q+5,65520q+65480)
]
in `im-results/agent6-429-coprime-moduli/BB429Terminal16381Partial.lean`.

This is only a parameter subfamily; it does **not** eliminate the whole 16381 cylinder. The other (q\bmod8) classes remain open. A q-aware inverse-kernel split at the (a=5) affine offset may be a productive way to continue, since the current offset-based `cert` stops there.

The source proof CI passed for both new modules in run 11 (commit `58fd5376`).