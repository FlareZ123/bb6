# Exact, compact fatal first-counter spectra for the original Cryptids #623 B-drain

**Agent 49, 9 November 2026. Mathematical status: intermediate.**
For the original six-state machine `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`,
the source-connected accelerated B-drain is (B(a,b,d)=\operatorname{drainB}(a,b,d)).
This note derives an exact finite list of **every** first counter (a) for which
the complete drain fails at a fixed block count (b), for arbitrary (b).
It extends the prior (b\le3^a) failure language in
[FlatDrain.md](FlatDrain.md) and does not resolve the genuine blank-root orbit.

## Mathematical result

Let (E_b=\{a\in\mathbb N: B(a,b,d)=\mathrm{none}\}\).
The set is independent of (d). The six exact source-certified one-level
recurrences imply, for all (q\ge0), with (q>0) in the first line,

```text
E_0       = {}
E_(3q)    = {x-1 : x in E_(q-1), x>0}                 (q>0)
E_(3q+1)  = {0} union {x+1 : x in E_q}
E_(3q+2)  = ({0} if 0 in E_q else {}) union {x+1 : x in E_(q+1)}
```

Each recursive set argument is strictly below the original (b).
The recurrences give the **entire** first-counter failure spectrum over all
natural numbers, with no first-counter range, congruence, or initial-blank
restriction. The previously bounded theorem
`drain_none_iff_bad` classified a proper subset of parameter space.

The original-importing Lean module
[FullFailureSpectrumSource.lean](FullFailureSpectrumSource.lean)
defines `badAll a b` and proves:

```lean
drain_none_iff_badAll (a b d : Nat) :
    (drainB a b d = none) ↔ badAll a b = true

drain_none_iff_failure_spectrum (a b d : Nat) :
    (drainB a b d = none) ↔ a ∈ failures b

drain_failure_independent_d (a b d e : Nat) :
    (drainB a b d = none) ↔ (drainB a b e = none)
```

The first enumerator `failures` filters all (0\le a<b). The proof of
`flat_safe_ge` guarantees that no failure is missed by that finite bound.

## Fast exact enumeration

[FastFailureSpectrumSource.lean](FastFailureSpectrumSource.lean) computes
the same set using the displayed set recurrences, **without scanning**
all (b) first counters. At every call it recurses on one block count
at most (\lfloor b/2\rfloor); the (3q+2) case also tests the zero
membership of (E_q) with `badAll 0 q`. Its Lean theorem is

```lean
drain_none_iff_fastSpectrum (a b d : Nat) :
    (drainB a b d = none) ↔ a ∈ fastSpectrum b
```

The list is strictly increasing and has no duplicates, as follows
inductively from the recurrence. Each call contributes at most one
new member and halves the remaining block bound. Therefore for (b\ge1),

```text
|E_b| ≤ floor(log_2 b) + 1.
```

Computing the entire fatal list uses (O((\log b)^2)) elementary
arithmetic operations when each recursive `badAll` check is computed
independently. Computing membership for one specified (a) takes only
(O(\log b)) recursive steps. These bounds count arithmetic operations,
not bit complexity. This replaces an (O(b))-candidate finite search
with a polylogarithmic enumeration of **all** fatal first counters.

Illustrations obtained from the exact recursion:

```text
b = 0:   {}
b = 2:   {1}
b = 4:   {0,1}
b = 5:   {0,2}
b = 11:  {1,2}
b = 14:  {0,1,3}
b = 40:  {0,1,2,3}
b = 104: {0}
```

The upstream-original module source is pinned to
`google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b`
and imports `FlatDrainSource.lean`, whose exact flat interpreter is
already source certified. Both new theorem files were first proved
in standalone Lean 4.36.0-rc2 with no `sorry`; they do not introduce
any new machine dynamics. The targeted
[manual workflow](../../.github/workflows/agent49-623-full-failure-spectrum.yml)
must pass before **original-source CI certification** is claimed.
Do not mistake standalone source-shaped verification for a completed
imported-source audit.

## What remains open

The original high-level map also has an initial `evalA` phase in one
sector. The finite list classifies `drainB` failures exactly once
its input `(a,b,d)` is known. It does not bound the number of real
blank-root returns or prove that those returns avoid their corresponding
fatal spectra. The surviving orbit starts from `D(0,7)`; neither its
halting status nor the six-state Busy Beaver value is decided.

**Next test of research value:** Use the compact spectra as explicit
finite target sets within the source-connected inverse grammar,
prioritizing a **history-dependent** exclusion for the authentic blank
root rather than more synthetic safe families.
