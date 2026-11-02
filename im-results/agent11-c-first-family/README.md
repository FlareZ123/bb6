# Machine C: composition of exact inverse grammars and global quotient barriers

Agent 11, 2026-11-02. Intermediate research. **Machine C and BB(6) remain undecided.**

## New candidate: all-time low-gate exclusion for t ≡ 6 (mod 16)

`LowGate6.lean` combines Agent3's complete original-source inverse family `low_gate_all_parents_iff` with Agent15/43's global M8 quotient barrier `blank_no_m8_cylinder`, to prove:

```lean
∀ t : Nat, 1≤t → t%16=6 → ¬ BB6.Agent3.CReach 1 (16*t+4)
```

The inverse grammar says that any reachable (1,16t+4) has a parent (22u−3,32·4^r·u−11u−3−3r) with t=2·4^r·u and u>0. Since t%16=6, r=0 and u%8=3. The parent is therefore (22u−3,21u−3), in the **globally unreachable exact original-section cylinder** a%8=7, k%8=4. The contradiction holds at all times and uses all possible recursion depths, without any simulation cutoff. It is a new *composition* of previously separately proved source theorems; assess novelty against the current fast-changing research frontier before publication.

By Agent15's exact first-family halt equation k+3m+4=2^(2m+3), the new low-gate exclusion also eliminates every **m≡136 (mod256)**: it forces k≡100 (mod256) and k=16t+4 with t≡6 (mod16). This m-class lies inside the m%16=8 group passing Agent15's earlier `affineQuotientExcluded` filter (`FirstFamilyFilterLimit.lean`), and is a new candidate additional infinite parameter exclusion.

**Verification status:** Local proof typechecks in Lean 4.36.0-rc2 with signatures matching the original dependencies. Its repository `LowGate6.lean` imports the original source, without stubs or axioms. Authoritative integrated CI must compile the entire Agent3/Agent15 source chain and audit `#print axioms`. Until it succeeds this is a *candidate source composition*.

Dependencies:
- `im-results/agent3-c-bounce-inverse/EvenTargetOrbit.lean` and `FeederOrbitGeneric.lean`, source CI [41513332787](https://github.com/FlareZ123/bb6/actions/runs/41513332787).
- `im-results/agent15-c-halting/M8M16Composition.lean`, source-certified M8 quotient bridge to exact blank-section reachability (individual upstream `CSourceBridge8` and `Mod8SevenFour`).
- The existing manual `.github/workflows/agent15-c-halting.yml` is extended to compile the new composition with those original definitions.

## Earlier independent proof of an already-known class

`First24.lean` proves all first-family m≡24 (mod32) impossible by composing Agent15's unique affine predecessor and Agent38's odd-special global invariant. This was checked with the entire unmodified original-source chain and standard Lean axioms, CI [41518668629](https://github.com/FlareZ123/bb6/actions/runs/41518668629) at SHA `5241ec95b9babf6fe9cb17c06c0a59ae0c86ccca`. However, **Agent3 already proved the strictly stronger global `low_gate_odd_t_excluded` in `EvenTargetOrbit.lean` before this invocation**: every (1,32q+20) is unreachable, which covers the m24 class. Thus this earlier module is an independent verification/corollary and **must not be counted as a new mathematical exclusion**. Its full source CI audited standard axioms `[propext, Classical.choice, Quot.sound]`; no sorryAx.

The true blank-section reachability of all other halting input families is unresolved, and no new BB(6) bound or complete machine disposition is claimed.
