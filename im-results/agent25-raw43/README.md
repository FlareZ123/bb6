# Raw43: canonical parent cut and five-hole child bounds

Parent: `1RB---_1RC---_0RD---_1LD0RB_------_------` (seven holes). First missing transition B1; E/F renaming preserves the parent and blank start.

## Source-accepted progress

| E1, with B1=0RE | Weighted bound | Side cycles | Last holes | Split nodes | Additional certificates | CI |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| 0LE | 75 | 5371 | 995 | 279 | 51 FAR + 1 growth | [45806858894](https://github.com/FlareZ123/bb6/actions/runs/45806858894) |
| 0RD | 49 | 2878 | 273 | 137 | 1 FAR | [45921443774](https://github.com/FlareZ123/bb6/actions/runs/45921443774) |
| 1RD | 1713 | 4203 | 641 | 212 | 25 FAR + 1 late last + 7 growth | [45922723471](https://github.com/FlareZ123/bb6/actions/runs/45922723471) |

Each child covers all 25^5 = 9,765,625 raw completions. WeightedBound includes first-one delay. Source theorem names respectively `BB6.Agent25Raw43.all43child`, `BB6.Agent25Raw43RD.all43child`, `BB6.Agent25Raw43RD1.all43child`.

`Raw43ParentCut.lean` gives a source-accepted conditional reduction of Raw43 to 21 canonical residuals instead of the 23 from the initial two-level cut. It absorbs 0LE and 0RD, not yet 1RD. See [45922648873](https://github.com/FlareZ123/bb6/actions/runs/45922648873), exact theorem `BB6.Agent25Raw43Parent.cover`. **Raw43 remains open**; this is not a canonical roster deletion.

## Universal growth

- 0LE M29: `1RB0RF_1RC0RE_0RD0RA_1LD0RB_1LF0LE_1LB---`. In left-includes-scanned zipper notation, S(n) = (A,[1,0,1],(01)^n 0). Entry S(1) after 16; S(n) → S(n+3) in 8n+28 steps.
- 1RD: `Raw43RD1Growth.lean` establishes shared E-state sweeps. `Raw43RD1Return.lean` resolves five variants of the C1 instruction; return from A([], (01)^m) to A([], (01)^f(m)) with f(m)=2m+3, 3 ceil(m/2)+3, or 3 floor(m/2)+3. `Raw43RD1M0.lean` gives linear alternating-block growth. `Raw43RD1M29.lean` proves a little-endian binary counter invariant covering both missing entries A1/C1.
- 0RD M0: `1RB0LF_1RC0RE_0RD---_1LD0RB_1RF0RD_1LA0RE`; one-state FAR orientation 0, delta [0,0], left masks [2,4,8,26,32,16,64], right masks [32,16,64,2,8,16,64], blank-zero closure mask 64.

## Active candidate siblings

| E1 | Weighted candidate bound | FAR | Other certificates / gaps |
| --- | ---: | ---: | --- |
| 0RE | 41 | 122 | complete candidate |
| 1RE | 128 | 177 | 2 growth drafts |
| 0RF | 144 | 138 | 5 unresolved |
| 1LB | 115 | 159 | 5 unresolved |

The exact open roster, split census and FAR candidates are in `spec_*.json`. `discover.js` uses 32-bit rolling hashes only for candidate selection and exact versioned-tape comparison; it is not a trusted proof checker. `generate.py` independently uses the C++ enumerator and emits Lean exact certificates. Existing workflow agent10-four-hole.yml supports raw43-child, raw43-0rd, raw43-1rd, raw43-parent-cut, and raw43-extra (raw43_extra_child=0re or 1re etc). Local shell and Python returned ClientError before execution; original-source CI is the compilation route. No unverified candidate is promoted to a certified bound.
