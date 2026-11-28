# Raw43 B1LE/E0LF residual 559: exact quadratic nonhalting recurrence

**Agent 9 with Agent 17 — 28 November 2026. Original-source Lean 4.36.0-rc2 accepted.**

## Result

Consider the six-state, two-symbol partial machine

```text
1RB---_1RC1LE_0RD1RF_1LD0RB_0LF0LE_1RA0RB
```

with only the (A1) transition unspecified.  For **every** total machine
compatible with this partial table, the blank-tape computation is infinite.
Thus the entire 25-completion one-hole cylinder is nonhalting.

The accepted Lean theorem is

```lean
BB6.Agent17Raw43B1LEE0LFM559.never
  (m : Machine) (hm : compatible table m) : NeverHalts m
```

This residual is local index **559** of the Raw43 (B1=1LE,E0=0LF) child.
It was previously represented there by a 9,922-state BiDFA certificate.  The
new proof replaces that finite-state leaf by an explicit parametric recurrence.

## Exact recurrence

In the source zipper representation define

```lean
family n =
  ⟨5,
    [false,true] ++ rep [true,false,true] (4*n+2) ++
      rep [false,true] (2*n+1) ++
      [true,false,true,true,false,true],
    []⟩
```

The authentic blank run enters `family 0` after exactly **170** primitive
transitions:

```lean
run0 table 170 ⟨0,[],[]⟩ = some (family 0)
```

For every natural (n),

```lean
run0 table (448*n+612) (family n) = some (family (n+1))
```

and (448n+612>0).  Consequently the (n)-th family checkpoint occurs at

[
t_n = 224n^2 + 388n + 170,
]

so the partial machine has defined execution prefixes of unbounded length
without ever querying the missing (A1) instruction.  The repository's
`never_of_growth` transport then gives `NeverHalts` for every total
completion.

## Sweep factorization

The recurrence is proved from exact local transition identities and generic
left/right block sweeps, with no finite-(n) induction hypothesis about the
machine orbit.  One section factors as

[
(88n+132) + (224n+276) + (136n+204) = 448n+612.
]

The three pieces are:

1. `family n -> p2raw n` in (88n+132) steps;
2. `p2raw n -> p4 n` in (224n+276) steps, itself split into two
   parametric sweep halves of (112n+100) and (112n+160) plus a
   16-step turnaround;
3. `p4 n -> family (n+1)` in (136n+204) steps.

All endpoint equalities, cyclic block rotations, and step-count arithmetic are
proved in Lean.  The exact phase source is
[`Raw43B1LEE0LFM559Final.lean`](../im-results/agent9-raw43-e0lf559/Raw43B1LEE0LFM559Final.lean);
the blank-entry and universal nonhalting wrapper is
[`Raw43B1LEE0LFM559Never.lean`](../im-results/agent9-raw43-e0lf559/Raw43B1LEE0LFM559Never.lean).

## Source acceptance

GitHub Actions run **46161969966** source-accepts the complete blank-start
theorem.  The retained artifact is **15270127869**,
`raw43-b1le-e0lf559-never-proof`, with ZIP SHA-256

```text
2ac145c8b10bab18504dab9c89cfee46db7acc49fa29d75e4fc3ae264ad6501f
```

The final axiom audit reports

```text
blank_entry : [propext]
growth      : [propext, Quot.sound]
never       : [propext, Quot.sound]
```

with no `sorryAx` or `native_decide`.  The phase-only gate also passed in
run **46161795914**.  Independently, Agent 34's alternative sweep
decomposition passed original-source CI in run **46159161148**, providing a
second formal check of the same recurrence structure.

## Role in the BB(6) upper-bound program

This theorem is a complete local nonhalting classification, not a complete
Raw43 parent Cover and not a universal BB(6) upper bound.  It directly removes
one of the expensive residual obligations in the retained Raw43 branch and is
now consumed by the Raw43 (B1=1LE,E0=0LF) child generator in place of the
9,922-state BiDFA leaf.  The remaining work is to source-accept that whole
child and then consume the enclosing Raw43 branches in the current global
roster.
