# Source-accepted weighted Cover for the Raw124 six-hole parent

The six-hole E1 parent

```text
1RB---_1RC---_0RD---_1LD1RE_---1LF_------
```

has a complete original-source weighted-TNF Cover at bound **4,136,175**.

## Theorem

In the repository's standard weighted-TNF semantics, every six-state, two-symbol machine compatible with the partial table above satisfies

```lean
BB6.Agent2Raw124ParentComplete.parent_cover :
  Cover (WeightedBound 4136175) BB6.Agent32Raw124ParentJoin.parent124
```

The theorem is source-accepted in Lean 4.36.0-rc2, [workflow run 45908591612](https://github.com/FlareZ123/bb6/actions/runs/45908591612), artifact **15159377345** (SHA-256 `9ec5b5b86fe4f78d636fd9a37891cabdd0017c04c8fc62f74f4ef6022ffcfa15`). Its transitive axiom profile is exactly `propext`, `Classical.choice`, and `Quot.sound`; the source-audit gate excludes `sorryAx` and `native_decide`.

## Proof decomposition

The parent is closed by a 24-way first-level partition. Twenty-two first-level children use their independently source-accepted original-source Covers. The other two are composed from separately accepted evidence:

- The F1=0RE child uses its accepted complete Cover at bound 2,473.
- The F1=0LF child is reduced by an exact nested cut to the sole residual F0=1RC cylinder
  ```text
  1RB---_1RC---_0RD---_1LD1RE_---1LF_1RC0LF
  ```
  The final child Cover is source-accepted at bound **108,667** in [run 45887306671](https://github.com/FlareZ123/bb6/actions/runs/45887306671), artifact **15150950633** (SHA-256 `11ced53194ddc805456c51e1c75e6c3cfe41757b49e01a3e6e7acd08f4b65775`). The exact F1=0LF parent cut is accepted in [run 45883981997](https://github.com/FlareZ123/bb6/actions/runs/45883981997).

The complete parent report records 24 covered first-level branches and no uncovered branch. The proof reuses the existing witness bank and source-audit partitions; no new discovery search is needed for this parent.

## Scope

This is a complete upper-bound Cover for the stated Raw124 parent cylinder. It is not a claim that 4,136,175 is the sharp maximum for that parent, and it does not determine BB(6).

The parent is being checked for unique membership in the **actual accepted Canonical58 roster** before any global roster subtraction is claimed. The earlier six-parent reconstruction that removed Raw59 and retained Raw118 was withdrawn. The current exact-membership consumer imports `Canonical58Raw113Graft.roster58` directly and is being source-audited in [run 45910336799](https://github.com/FlareZ123/bb6/actions/runs/45910336799). Until that consumer and its axiom gate pass, Canonical58 remains the accepted global interface and the Raw124 parent Cover remains a local result.
