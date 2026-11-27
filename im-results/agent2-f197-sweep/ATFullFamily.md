# F197 complementary-AT family with arbitrary leading P counter

**Research status (27 Nov 2026, 23:27 UTC).** The statement below is an exact mathematical consequence of explicit local source-certified rules and their inductive composition. All local rules and the arbitrary-length carry transducer already passed Lean 4.36.0-rc2 CI [46081395759](https://github.com/FlareZ123/bb6/actions/runs/46081395759) and [46081264262](https://github.com/FlareZ123/bb6/actions/runs/46081264262). The first monolithic Lean certificate `ATCounter.lean` exceeded a ten-minute CI timeout **without diagnostic output**, so its full parametric composition is pending a smaller/profiler-assisted kernel check. Do not report `atp_full_family_closed` as kernel-accepted until it is. There is no global blank-orbit nonhalting proof.

## Exact two-parameter identity

At the B reset boundary use nearest-first left-run words and terminal right word `e`. Symbols:

- `A=10`, `T=1100`, `P=AAT` (8 bits), `J=100`, `C=110`, `u=1111000`, `s=11111000`, `d=11`, `e=1`.
- Choose any `n,q≥0`, nonempty data `c₀,...,c_q ∈ {A,T}`, and arbitrary left suffix `X` with first physical bit one.
- Define `Z=c₀(Tc₁)...(Tc_q)`, `H(A)=AT`, `H(T)=AAT`, `Φ=A H(c₀)...H(c_q)`, and `t=#{i:c_i=T}`.

Then the literal Raw132/F197 machine `1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF` has the exact, finite, nonhalting execution

```
B(P^n TAT Z AA X, e)  ->^(156 + 68(n+q) + 14t)  B(P^n AAAT Φ X, e).
```

The output left-prefix bit length exceeds the input by exactly **2** for all n,q,data. This extends [the kernel-accepted n=0 theorem](ATPairedTheorem.md) `atp_family`, whose exact bit-growth theorem is `atpBitGrowth` in `ATCostGrowth.lean`.

## Mathematical proof via independently checked source transducers

Write `Q₀=e` and `Q_{n+1}=u s^n d`. The core counter transport is the induction

```
B(P^n Y,e) ->^(36n) B(Y,Q_n)
```

for every run-aligned `Y`. Its single-block steps are `P/e→/ud` and `P/uR→/usR`, each **36 primitive transitions**; the latter is uniformly valid for run-aligned R. The underlying local source-to-source lemmas `atc_consume_e`, `atc_consume_u` were kernel accepted in `ATCarryCore.lean`.

The scanner/decoder `atp_staged_with` ([ATCarriedParser.lean](ATCarriedParser.lean)) has already been kernel accepted for every data list and **every** aligned right stack R:

```
B(TAT Z AA X,R) ->^(46+S+K) B(J Φ X,A C R)
```

where `S=39+8(q+1)+10t` and `K= -29 + 60(q+1)+4t` (the carried decoder consumes 31 fewer transitions than the n=0 end decoder). Equivalently `S+K=10+68(q+1)+14t`. The source-core rules comprise the 46-step TAT preconsume, the 8/18-step AT/TT scanners, 47/57-step AAA/TAA terminals, 60/64-step four-case decoder peel, and 32/36-step A/T terminal carry junction.

Next restore the right counter, by induction on n:

```
B(J Y,A C Q_n) ->^(31+32n) B(P^n AAAT Y,e).
```

For n=0 the source-certified `atc_counter_base` is the **31-step** `J/(ACe)→AAAT/e` rule. For n=k+1 the source-certified 36-step `J/(ACuR)→JAAAT/(AR)` removes the leading u, and the source-certified 32/27-step `J/(A s^k d)→P^(k+1)/e` decoder returns all counter blocks. Hence `36 + (32k+27)=31+32(k+1)`. The relevant local lemmas are `atc_counter_u`, `atc_counter_s`, and `atc_counter_d`, all kernel-accepted at the literal source.

Composing the three finite source runs yields

```
36n + (46+S+K) + (31+32n)
= 68n + 46 + S + (K+31)
= 68n + 46 + [39+8(q+1)+10t] + [3+60(q+1)+4t]
= 156 + 68(n+q) + 14t.
```

Every component returns `some` under Lean's literal `run`, so no intermediate halt is possible. For bit-length: the input is `8n + 10 + 6(q+1)+2t`; the output `8n+12+6(q+1)+2t`. Both are finite explicit prefix encodings with the suffix untouched. This is a strict +2 growth theorem.

## Reproducible source modules and current formal gap

The actual Lean theorem `atp_full_family_closed` and its helper inductions are in [ATCounter.lean](ATCounter.lean), currently awaiting a green resource-bounded check; `atp_full_family_bits` and formal bit-growth are in [ATFullGrowth.lean](ATFullGrowth.lean), also not yet checked. The core literal rules are in [ATCarryCore.lean](ATCarryCore.lean) and the recursive carry scanner in [ATCarriedParser.lean](ATCarriedParser.lean); both passed source-guarded Lean checks (only `propext`, `Quot.sound`; no `sorryAx`).

**Important distinction:** the source-certified local lemmas and `atp_staged_with` are proved, and the above paper induction is explicit; the full Lean composition has so far hit a *compiler runtime*, not an identified mathematical counterexample. Optimize the induction proof and recheck. Do not move this to `results/` or assert an unconditional F197 nonhalting theorem.

## Research frontier

Empirical first-330 genuine reset classification: 200 fit the established paired-AA grammar, six fit this complementary `P^n TAT Z AA` grammar, 124 require further cases, notably J/U/C markers and terminal patterns other than AA. The exact reset-growth grammar needed to conclude full blank-orbit nonhalting remains open; BB(6) itself remains unresolved.
