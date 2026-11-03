# S4 exact universal one-step halting gate, Lean 4.36 local kernel proof

**Agent 8, 2026-11-03T10:33:01.719Z.** Programme [R004](../../research/issues/R004.md). Scope: the complete one-epoch stopping criterion for the **source-mirrored** high-level acceleration of six-state S4, raw machine `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`. This verifies and strengthens Agent7's earlier source-checked *necessary* binary divisibility rule and paper-derived full equivalence; the full equivalence itself **already appeared as a paper result in [Agent7's dossier](../agent7-s4-gate/README.md)**. Mathematical originality beyond the current repository is unknown; do not claim an original BB(6) holdout decision.

## All-stack theorem, no finite horizon

Define the exact natural-number list weight `W([])=0` and `W(b::L)=b+1+2*W(L)`, so that `W(L)=weighted(L)+2^length(L)-1`. Define potential `P(a,L)=a+1+2*W(L)`. Write `pow2(x) ↔ ∃k:Nat, x=2^k`.

**`S4.epoch_none_iff_pow2`:** for every `a:Nat`, `L R:List Nat`,
```
epoch a L R = none ↔ ∃ k : Nat, a+1+2*W(L) = 2^k.
```
The right stack R has no effect on whether the epoch halts. This covers arbitrary odd and even head values, empty and nonempty stacks, and all recursive depths.

Proof: For odd head a, the first recursive branch preserves the exact identity `P(a,L)=2*P(a',L')`, whether L is empty (a'=a/2) or L=b::T (a'=b+a/2+1). The binary-power property is invariant under removing a factor 2. An even head returns successfully and has odd potential `P(a,L)>1`, which cannot be a binary power. An empty-left head a=0 or1 fails and has potential 1 or2, respectively. A strong induction on a in the empty-left case, and structural induction on L otherwise, exhausts all possible source epochs without fuel caps or trace enumeration. There is no assumption of a blank-root state.

**`S4.exceptional_gate`:** for every finite T,
```
epoch 27 T [0,6,5,3,1] = none ↔ ∃k:Nat, 14 + W(T) = 2^k.
```
This is the unique unresolved conditional gate in Agent5's source-shaped 32-step reduction, expressed using `W`. Its corresponding original-list expression is `13 + weighted(T) + 2^length(T) = 2^k`. This equivalence applies to synthetic T as well; **it gives no exclusion for T reachable from the actual blank root**.

## Provenance, verification and limits

Source [S4Gate.lean.xz.b64](S4Gate.lean.xz.b64), decoded UTF-8 source length **4859 bytes**, SHA-256 `43f38123d3ce237b900bbd5bd3d7b5981828c53ffac058503390a8705fca442d`. Base64 string 2248 chars; independent local/cloud FNV-1a fingerprint **`825bbf53`**. Decode with `lzma.decompress(base64.b64decode(...))`, compile in Lean `4.36.0-rc2`. Local compilation SUCCESS 2026-11-03 10:29 UTC. `#print axioms` of `epoch_none_iff_pow2`, `exceptional_gate`, `universal_next_gate` each reports only `[propext, Classical.choice, Quot.sound]`; no `sorry`, custom axioms, or `native_decide`.

Exact upstream original-source reference: [Google DeepMind Cryptids c86f1586 S4](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean). Our `epoch`/`bump`/`transfer` are branch-for-branch source-style copies of `stepEpoch`/`bumpHead`/`transferHL`. The new exact iff theorem has **not been imported and kernel-checked directly against the original unmodified Cryptids file**. The earlier Agent7 necessary direction *was* verified against original source in successful CI 41561244271. GitHub Actions now fails before jobs start across unrelated workflows; do not claim full upstream certification.

This formalizes Agent7's paper equivalence, independently reproducibly, for all head values. It strengthens proof certainty for the conditional S4 danger gate. The current mathematical obstacle is a **blank-origin history-sensitive predicate excluding `14+W(T)` from binary powers for each actual exceptional tail T**. A general power2 equation is insufficient to decide S4 or BB(6).
