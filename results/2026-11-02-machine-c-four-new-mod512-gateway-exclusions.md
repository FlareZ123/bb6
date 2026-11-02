# Four new Machine C reset exclusions beyond the previously computed modulus-512 quotient

Agent 29, 2 November 2026. **New all-time mathematical exclusion classes, verified by the Lean kernel against the unmodified original local counter definitions.** The machine and BB(6) remain undecided.

## Theorem

Let `Reach` be `BB6CLine.Reach`, the exact accelerated blank-entry reachability predicate from `(5,0,1)` for the six-state two-symbol machine `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`.

The following four independent theorems hold simultaneously, universally for every natural parameter `t`:

```lean
BB6.Agent29CNew.reset_512_38_unreachable (t : Nat) :
    ¬Reach (1024*t+77,1536*t+118,0)

BB6.Agent29CNew.reset_512_130_unreachable (t : Nat) :
    ¬Reach (1024*t+261,1536*t+394,0)

BB6.Agent29CNew.reset_512_184_unreachable (t : Nat) :
    ¬Reach (1024*t+369,1536*t+556,0)

BB6.Agent29CNew.reset_512_271_unreachable (t : Nat) :
    ¬Reach (1024*t+543,1536*t+817,0)
```

In each case the target is the potential halting reset gateway `(2j+1,3j+4,0)` with `j=512t+r` and `r` respectively 38, 130, 184 or 271.

## Genuine advance over the existing finite quotient

Agent 41's [independently checked modulus-512 quotient census](../im-results/agent41-c-quotient512/README.md) excluded 327 of 512 reset indices by finite-graph overapproximation. None of these four residues appears in its cumulative 512 excluded set. Thus these source-certified proofs exclude **four previously surviving infinite families**.

The four newly excluded residue classes are independent mod 512; if combined with the existing 327 quotient-certified classes, the known abstract-or-symbolic necessary-gateway exclusion filter now covers at least **331 of 512 classes**. This combined numerical statement mixes Agent 41's double-checked C++ abstract closure (not itself kernel-certified) with our four Lean-theorem exclusions; the four new classes themselves are individually kernel-certified without any finite closure assumption.

These four classes cover five previously surviving classes mod 1024: `38,130,184,642,783`. The other three lifts `550,696,271` were already absent in Agent 41's modulus-1024 quotient.

## Mathematical proof

A complete three-case predecessor theorem `hub_cases` covers any blank-reached high-sector hub `(A,2,C)` with `A≥5,C≥4`. Its ancestors must include one of:

```text
even portal: (0,k,C+3), k even, A=2k+2;
odd portal:  (0,k,C+2), k odd, A+2=2k+3;
reset:       (A+3,k,0), C=2k.
```

The finite-tree arguments alternate this exhaustive split with exact backward contraction of zero-right reset states and of zero-left high-sector portals. Terminal nodes violate the global source-certified invariant for reached odd-right resets: if `Reach(A,K,0)`, `K≥5`, `K%2=1`, then `(A+K)%4 ∈ {0,3}`. Additional leaves are contradictory linear congruences or parity conditions. All branches are closed with Lean `omega` and actual reachability hypotheses. No unbounded search, oracle, fixed-depth overclaim or assumption of nonhalting is involved.

The four finite certificates contain respectively 24, 42, 20 and 29 symbolic reverse nodes. Every node and branch is represented by explicit Lean theorems.

## Independent source-level verification

The exact complete Lean source is [CNew.lean.xz.b64](../im-results/agent29-c-inverse/CNew.lean.xz.b64), reconstructed by [locked, atomic SHA-256 verifier](../im-results/agent29-c-inverse/reconstruct.py).

- Uncompressed source: **48,869 bytes**, SHA-256 `d615840ed77b8915adc9eceee042e144fa6a5be62dfc554f971ba95d59368e16`.
- Pinned version: Lean 4.36.0-rc2, independent Ubuntu CI [run 41410929224](https://github.com/FlareZ123/bb6/actions/runs/41410929224), repository commit `7741a5c601fd6fd0cbec43cb296d5787334e8a5f`.
- Manual-only workflow [.github/workflows/agent29-c-new-residues.yml](../.github/workflows/agent29-c-new-residues.yml) compiles the unmodified `CLine.lean`, `CReachBridge.lean`, `CRange.lean`, `CBack.lean`, and `CHubSplit.lean` before the new source. The four terminal theorem axiom audits each display **`[propext, Classical.choice, Quot.sound]`**, without `sorryAx`.
- Agent 21 separately source-certified the raw six-state TM to this acceleration in [run 41389979481](https://github.com/FlareZ123/bb6/actions/runs/41389979481).

These nonreachability theorems apply at every finite accelerated time from the authentic blank state. They exclude only four gateway classes; other Machine C reset and side gates remain open, as do all remaining BB(6) holdouts.
