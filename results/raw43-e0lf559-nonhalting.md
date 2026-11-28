# Structural nonhalting of the Raw43 B1LE/E0LF residual 559

## Theorem

Let (P_{559}) be the six-state, two-symbol partial machine

| State | Read 0 | Read 1 |
|---|---|---|
| A | 1RB | undefined |
| B | 1RC | 1LE |
| C | 0RD | 1RF |
| D | 1LD | 0RB |
| E | 0LF | 0LE |
| F | 1RA | 0RB |

The undefined transition is A1. **Every total machine compatible with (P_{559}) runs forever from the blank tape.** In particular, the missing A1 instruction cannot affect the blank-start orbit.

## Parametric orbit

Use the repository's nearest-cell-first zipper convention, where the left list begins with the scanned cell. Define the section family

[
F_n =
leftlangle
F,;
[0,1]mathbin{+!!+}(1,0,1)^{4n+2}
mathbin{+!!+}(0,1)^{2n+1}
mathbin{+!!+}[1,0,1,1,0,1],;
[]
ightangle .
]

The blank-start computation reaches (F_0) after exactly 170 steps. The imported phase lemmas establish three consecutive transfers with costs

[
88n+132,qquad 224n+276,qquad 136n+204.
]

Their composition gives the exact section return

[
operatorname{run}(P_{559},448n+612,F_n)=F_{n+1}.
]

Thus the time at which the orbit reaches (F_k) is

[
T(k)=170+sum_{n=0}^{k-1}(448n+612)
    =170+224k^2+388k.
]

The orbit therefore has infinitely many defined steps. Since it never queries A1, every compatible total completion follows this same orbit and cannot halt. The left zipper list has length (16n+16), so each section return extends the represented tape by 16 cells while the return cost grows linearly; the cumulative running time is consequently quadratic in the section index.

## Formal verification

- Phase transfers: [Raw43B1LEE0LFM559Final.lean](../im-results/agent9-raw43-e0lf559/Raw43B1LEE0LFM559Final.lean)
- Blank entry, composed growth and universal nonhalting: [Raw43B1LEE0LFM559Never.lean](../im-results/agent9-raw43-e0lf559/Raw43B1LEE0LFM559Never.lean)
- Sweep lemmas: [SweepPumping.lean](../im-results/agent31-three-hole-tnf/SweepPumping.lean)
- Phase source gate: GitHub Actions run [46161795914](https://github.com/FlareZ123/bb6/actions/runs/46161795914), artifact 15269587235
- Full recurrence source gate: GitHub Actions run [46161969966](https://github.com/FlareZ123/bb6/actions/runs/46161969966), artifact 15270127869

Lean 4.36.0-rc2 compiled the seven-module source closure. The axiom audit reports only `propext` and `Quot.sound` for the growth and nonhalting theorems; there is no `sorryAx`.

## Scope

This is a residual-level nonhalting theorem, not a completed Raw43 parent Cover and not a change to the global Canonical38 residual count. In the B1LE/E0LF candidate bank, this replaces the only external 9,922-state BiDFA certificate; after substitution, no numeric/external DFA entries remain in the spec (the remaining BiDFA certificates are inline). The full B1LE/E0LF child source-acceptance run is tracked separately (run 46162375708).
