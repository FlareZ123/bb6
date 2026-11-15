# Coq TM63 halt itinerary and the Lean terminal-wrapper interface

This note connects the initial blank-root witness to the exact `m1,n1` source specialized by Agent 48's terminal wrapper. It is an integration derivation from the Coq TM63 proof, not yet a Lean proof of the complete itinerary.

Source: `ccz181078/busycoq`, commit `3f302b87f5fb933c46e97672ffbb6907f373fb6e`, `verify/SOBCv5.v`, TM63 section (roughly lines 10813–10985 and the `halt` proof around 11249).

## 1. Blank-root entry

The Coq `init` lemma reaches
```
S1 3 7 m2 6 0 63
```
The exact original-source theorem
`BB6Coverage.Agent42InitialS1Root.tm2_blank_reaches_initialS1_source`
is now kernel-checked in
`im-results/agent48-root-witness/RootSourceBridge.lean`:
```lean
run tm2 27959 blank = some (s1Config 3 7 2 6 0 63 29)
```
The 238-bit computation covers absolute cells -10 through 227 and is
lifted to the original infinite tape by the pointwise write correspondence,
successful-move embedding, and a proof that both tapes are blank outside
the finite support. The finite computation reports `[propext]`; the
original-source reachability theorem reports `[propext, Quot.sound]`;
neither has `sorryAx`. This closes only the initial blank-to-S1 prefix,
not the subsequent reset itinerary or halting proof. See
`im-results/agent48-root-witness/README.md` for the complete proof scope.

## 2. First Rsts1 / Rst1' cycle

Coq `Rsts1 n len0 b` gives
```
S1 len0 (1+3*n) m2 b 0 (2^b-1)
  -->* S1 len0 0 m1 (st2 (1+3*n) b + (5*n+2)) 0 (t2 (2+3*n) b).
```
At the initial parameters `n=2, len0=3, b=6`, define
```
A1 := st2 7 6 + 12
B1 := t2 8 6.
```
The output is `S1 3 0 m1 A1 0 B1`.

Coq `Rst1' a0 a b` maps
```
S1 a0 0 m1 a 0 b
  -->* S1 (a0+2+a) (((2^(a0+2)-1)*2^a)-1) m2 b 0 (2^b-1).
```
(The displayed outer counter is the simplification of
`((((2^a0-1)*2+1)*2+1)*2^a-1)`.)
With `a0=3, a=A1, b=B1`, set
```
L1 := A1 + 5
N1 := 31 * 2^A1 - 1.
```
The next S1 source is `S1 L1 N1 m2 B1 0 (2^B1-1)`.

## 3. Rsts1_v2 / second Rst1' cycle

Coq `Rsts1_v2` requires `N1 mod 3 = 1` and yields
```
S1 L1 0 m1 A2 0 B2
A2 := st2 N1 B1 + (5*(N1/3)+2)
B2 := t2 (N1+1) B1.
```
Applying `Rst1'` again with `a0=L1, a=A2, b=B2`, set
```
L2 := L1 + 2 + A2
N2 := (2^(L1+2)-1) * 2^A2 - 1.
```
The next source is `S1 L2 N2 m2 B2 0 (2^B2-1)`.

## 4. Final Rsts2H and the m1,n1 terminal source

The Coq proof then applies `Rsts2H`, whose premise is `N2 mod 3 = 2`. Put
```
k := (N2-2)/3.
```
The underlying `Rsts2 k L2 B2` decomposes as follows.

First, `Rsts` with `a0=2`:
```
S1 L2 (2+3*k) m2 B2 0 (2^B2-1)
  -->* S1 L2 2 m2 A3 0 B3
A3 := st2 (3*k) B2 + 5*k
B3 := t2 (1+3*k) B2.
```

Then `Rst2`:
```
S1 L2 2 m2 A3 0 B3
  -->* S1 L2 1 m1 (A3+B3+2) 0 (2^B3-1).
```
Thus the exact source parameters for Agent 48's m1,n1 terminal wrapper are
```
aTerm := A3 + B3 + 2
bTerm := 2^B3 - 1
LTerm := L2.
```
The wrapper's **pre-drain** prefix endpoint is
```lean
s1Config L2 0 0 (aTerm+bTerm+2) (2^bTerm-1) 0 h'
```
with the outer marker/counter context now `m0,n0`. This is the first phase of Coq's final `Rst1` (`LC_Inc`); the Lean terminal wrapper then discharges the separate `Incs0` drain using `S1CountedDrain`, before applying the source-certified terminal section. The full Coq `Rst1` endpoint after that drain is `S1 L2 0 m0 (aTerm+bTerm+2) 0 (2^bTerm-1)`.

Finally Coq applies `Rst0'` to halt. This identifies the precise interface: initial root witness → both Rsts1/Rst1' stages → final Rsts/Rst2 → Agent 8's m1,n1 pre-drain prefix → Agent 48's counted drain + terminal section.

## 5. Parity / mod-3 side conditions

The recurrences are
```
t2 0 b = b
t2 (j+1) b = 2^(t2 j b)-1
st2 n b = sum_{j=0}^n t2 j b.
```
For `b≥1`, every `t2 j b` with `j≥1` is odd.

- `A1=st2 7 6+12` is odd: one even term (`t2 0 6=6`) plus seven odd terms. Hence `L1=A1+5` is even.
- `N1=31*2^A1-1` is odd and `N1 ≡ 2^A1-1 ≡ 1 (mod 3)`. Since `N1` is odd and 1 mod 3, `N1/3` is even.
- `B1=t2 8 6` is odd. `st2 N1 B1` sums `N1+1` even-many odd terms, so `A2` is even. Thus `L2=L1+2+A2` is even.
- `N2=(2^(L1+2)-1)*2^A2-1` is odd and `N2 ≡ -1 ≡ 2 (mod 3)`, because `L1+2` is even. Hence `N2 ≡ 5 (mod 6)` and `k=(N2-2)/3` is odd.
- `B2=t2(N1+1)B1` is odd. Since `k` is odd, `st2(3*k)B2` sums `3*k+1` even-many odd terms, so `A3` is odd. `B3=t2(1+3*k)B2` is odd.
- Therefore `aTerm=A3+B3+2` is even and `bTerm=2^B3-1` is odd.

This supplies the two Coq `rw_mod` obligations (`N1 mod 3=1`, `N2 mod 3=2`) and the parity profile of the final terminal parameters in a form suitable for Lean arithmetic lemmas.

## Status

- The initial blank-root run is kernel-checked in `RootSourceBridge.lean`: exactly 27,959 original-TM2 moves to `s1Config 3 7 2 6 0 63 29`, with a full infinite-tape embedding and no `sorryAx`. This does not prove any later macro or the final halt.
- The parameter chain above is a direct algebraic reading/simplification of the Coq macro statements; the Lean composition of the full itinerary remains open.
- The final m1,n1 pre-drain endpoint is the correct input to the Agent 48 terminal wrapper; do not confuse it with the full post-`Incs0` Coq Rst1 endpoint.


## 6. Current Lean Rst1' source-macro candidate (15 November 2026)

A matching parameterized source-run proof attempt now exists in
`im-results/agent8-rst1prime/Rst1PrimeBridge6Source.lean`:
```lean
rst1Prime_counted_macro :
  run tm2 (97+12*(L+a)+3*b) (s1Config L 0 1 a 0 b h) =
    some (s1Config (L+a+2) (2^(L+a+2)-2^a-1)
      2 b (2^b-1) 0 (h+5+3*b))
```
Its ten phases are the left sweep of (3a+1), bridge 8, left sweep of
(3L+5), bridge 20, right sweep of (L+1), bridge 9, right sweep of
(a+1), bridge 6, right sweep of (b), and bridge 30. The primitive
cost is exactly (97+12(L+a)+3b).

This is the exact Coq `Rst1'` interface above: the target counter identity
`(2^(L+2)-1)*2^a-1 = 2^(L+a+2)-2^a-1` is the same expression after
`pow_add`.

**The first Rst1' instance is already wired into the root source path.**
`im-results/agent8-rst1prime/TM63M1OddRst1PrimeContinuation.lean`
imports this macro. Its theorem
`rst1Prime_first_reset_after_first_section` composes the macro with the
S1 counted drain and reaches
`s1Config tm63Length1 tm63Index1 2 B1 0 (nextRight B1) head`;
`tm63_blank_reaches_after_first_reset` then composes that reset with
the preceding blank-root first section. The existing
`TM63MiddleSectionCountdown` starts from this exact endpoint.

The second Coq Rst1' instance is still part of the unresolved
middle/last `hstage`. It should be applied with
`(L,a,b)=(L1,A2,B2)`, after the full `Rsts1_v2` source transition has
been established. The universal macro and the already-proved
`rst1Prime_resetCost_decomposition L a b` are parameter-generic, so
the second reset reuses the same ten-phase macro plus the S1 counted
drain. The formerly missing general index identity is now proved in
`BB6ChampionArithmetic.resetIndex_eq_pow_sub` in
`im-results/agent24-champion-time/ChampionModular.lean`:
`resetIndex L a = 2^(L+a+2)-2^a-1` for all natural L and a. This
arithmetic theorem was kernel-checked locally with Lean 4.36.0-rc2;
its axiom set is `[propext, Quot.sound]`. It establishes only the
closed form of the parameter update, not a TM63 source run.

The current `TM63MiddleSectionCountdown` plus
`TM63RootResidueSevenPrefix` / `TM63RootResidueSeven` only certifies
the first eight middle rows and the residue-seven prefix/counted
increment; it does not yet reach the second Rst1' input. Thus the
remaining hard source obligation is still the complete
`Rsts1_v2` middle transition to `S1(L1,0,m1,A2,0,B2)`; after that,
the second Rst1' reset itself is a direct reuse of the existing
parameter-generic macro.

**Structural clarification from the pinned Rocq proof:** `Rsts1_v2` is
only the division/modulo-3 wrapper `n=3q+1` followed by `Rsts1`.
`Rsts1` is `Rsts` plus one final `Rst2`; `Rsts` itself is an
induction applying `Rst2`, `Rst1`, and `Rst0` in each cycle.
Consequently, the universal source-level blocker is the original-TM2
counted realization of those three one-step reset families, not a
separate simulation for `Rsts1_v2`. The exact induction, symbolic
counter/head recurrences, and proposed Lean run interfaces are recorded
in [`Rsts1-v2-source-closure.md`](../agent48-counted-inc0/Rsts1-v2-source-closure.md).
The current residue-specific q4 modules are partial cases of this
one-step obligation, not yet its universal proof.

**Verification status:** the ten-phase macro and its root-connected first
instance are source proof attempts, not yet certified by a post-patch
kernel run. The existing manual-only workflow
`.github/workflows/agent42-champion-terminal-source.yml` compiles
FirstSweep → Bridge8Source → SecondSweep → Bridge20Source →
Bridge9Source → Bridge6Source, then
`TM63M1OddRst1PrimeContinuation` and the root-prefix consumers, with
transitive `sorryAx` gates. The latest Bridge8 source patch is commit
`29118db656892e842a6237f86ae864e5ab98c3c0`; the second-sweep frame
qualification is `c4deccae9aed0aee24ba0647fa13994f12ec7aa0`. A static
ambiguity repair in Bridge6Source is commit
`21ab4aa332ffb15d78bf2db7b679e0394b9917ac`. No post-patch full-chain
run or successful local compile has yet been obtained. Do not promote the
macro or its root instance to a proved Coq Rst1' stage until the exact
source and exported axiom audits pass.

The first reset is therefore source-connected in the current proof graph
once this macro passes its audit. The remaining middle/last itinerary
from that post-first-reset state to the final `S1(L2,1,m1,A3,0,B3)`
input, the second Rst1' application, and the final Rsts2H/Rst2 and
terminal stages remain separate obligations.


## 7. Earlier M2 residue-six interface (now incorporated into a root-composition candidate)

This section records the immediate next-row interface at the prior checkpoint. As of 15 November, the M2 row and its following M1 row have been composed in the uncompiled candidate `TM63RootResidueSix.lean`; see Section 8 for the current endpoint and next row.

## 7a. Historical M2 residue-six interface

The current theorem
`tm63_blank_reaches_after_middle9` in
`im-results/agent41-m0-n16r7/TM63RootResidueSeven.lean` ends at
`m=2,n=16r+6`, with
`r=tm63RootMiddleK/2`,
`a=tm63MiddleAfter8A+tm63MiddleAfter8B+1`,
`b=2^tm63MiddleAfter8B-1`, and head
`tm63MiddleAfter8Head+5+3*tm63MiddleAfter8B`.
This matches exactly the input of the already-existing
`m2Even_residue6_q4_reset_prefix_source` in
`im-results/agent48-counted-inc0/M2EvenResidueSix.lean`.

The current root bounds imply the module's hypotheses:
`4 ≤ tm63Length1`,
`16*r+6 < 2^tm63Length1` (from
`tm63_middle_root_bound` and
`tm63_root_residue7_index`), and (0<a).
The existing prefix theorem reaches
`s1Config L (16*r+5) 1 (a+b+2) (2^b-1) 0 h'`.
Composing with the generic S1 counted drain should give the full counted
increment endpoint
`s1Config L (16*r+5) 1 (a+b+2) 0 (2^b-1) h'`.

This is a concrete next source-row integration candidate, not yet a
root theorem. The narrow manual-only workflow
`.github/workflows/agent48-m2-even-six.yml` covers both
`M2EvenSixQ4Prefix.lean` and `M2EvenResidueSix.lean`; these files
are not in the Agent42 full-chain workflow. The old targeted run
43659498187 predates the current source edits. The current M2 base and
residue files have finite-boundary/index repairs at commits
`58906b7b7a45ea7c309ec61996c5163ce3238e03` and
`88754f3885817f13924aa68459d3e98384a29bc9`, but no post-patch compile
or transitive axiom audit has passed. Agent 42 has taken ownership of
the leaf repair and acceptance check; do not edit those files
concurrently. No counted/root wrapper has been kernel-checked yet.
The useful bound/positivity helper theorems in
`TM63RootResidueSeven.lean` are currently private; either append the
composition in that same module or restate the small arithmetic bounds
in a new module. Once the Rst1Prime Bridge8→Bridge30 source gate is
clean and the M2 leaf passes its targeted check, compose the M2 prefix
with the generic S1 counted drain and then with this authentic root
endpoint.


## 8. Current root composition through middle row 11; next M0-even residue-four row

The new candidate module
`im-results/agent42-champion-terminal/TM63RootResidueSix.lean`
imports the middle-nine root endpoint, the counted M2-even residue-six
increment, and the counted M1-odd residue-five increment. Its theorem
`tm63_blank_reaches_after_middle11` composes the following exact states:

1. After middle row 9 (from `TM63RootResidueSeven`):
   `m=2, n=16*r+6`, with
   `A9=tm63MiddleAfter8A+tm63MiddleAfter8B+1`,
   `B9=2^tm63MiddleAfter8B-1`, and
   `H9=tm63MiddleAfter8Head+5+3*tm63MiddleAfter8B`.
2. After the M2-even residue-six counted increment:
   `m=1, n=16*r+5`,
   `A10=A9+B9+2`,
   `B10=2^B9-1`,
   `H10=H9+5+3*B9`.
3. After the M1-odd residue-five counted increment:
   `m=0, n=16*r+4`,
   `A11=A10+B10+2`,
   `B11=2^B10-1`,
   `H11=H10+5+3*B10`.

The shared arithmetic module
`TM63RootCountdownArithmetic.lean` now exports
`tm63_root_middle_k_split`, `tm63_index1_eq_16k15`, and
`tm63_index1_lt_pow_length1`; the residue-six root composition uses
these rather than duplicating the quotient and width proofs.

**Current next source row:** M0-even residue four, input
`S1(L,16*r+4,0,A11,0,B11,H11)). Agent 48's finite bridge candidate is
`im-results/agent48-counted-inc0/M0EvenResidueFour-bridge-candidate.md`.
Agent 42 added the isolated 51-step finite certificate and full-frame head
bound in
`im-results/agent42-champion-terminal/M0EvenResidueFourFiniteBridge.lean`,
and wired it into the manual source workflow. Three deterministic sample
replays `(a,b)=(1,0),(2,1),(3,2)` reached state 4 at the original head
and satisfied `q4RightShape`; these are computational samples only.

**Unverified boundary:** the M2 counted adapter, M1 residue-five source
theorem, root composition through middle11, public root arithmetic
lemmas, and finite M0 bridge certificate have not been compiled in this
invocation. The M0 arbitrary-source frame, E-scan, q4 suffix/tail identity,
and counted-drain composition remain open. Do not report a certified
extension beyond the previously accepted root prefix until the Critic's
residue-seven/Rst1Prime source gate and these new modules pass their
Lean 4.36.0-rc2 axiom audits.
