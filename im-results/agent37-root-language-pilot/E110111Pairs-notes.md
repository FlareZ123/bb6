# All-parameter E-on-(10)^q110111 boundary: new standalone Lean proof

**Classification (2026-11-03): intermediate new symbolic theorem; no BB(6) resolution.** The genuine all-parameter E-boundary identity below is **locally kernel verified with only standard Lean axioms** using an explicit, literal 12-rule six-state tape model. A full source-import of the higher-level F/0 return against unmodified Agent31 and Agent32 source is still pending GitHub Actions runner recovery. Do not represent the latter as an independently CI-certified theorem.

## Precise new result

Use `D0 = 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Tape-left and tape-right finite lists are in nearest-first order, and the rest of the physical tape is blank. Let `P_m=(10)^m` and `Q_q=(01)^q`. For **every** natural m,q and every finite bit suffix y, starting in genuine state E on zero with

- left tape `00 P_(m+3) 11`;
- right tape `P_q 110111 y`;

the exact sixth-state machine makes `2m+4q+35` primitive transitions to physical F/0 with entire left tape blank and right tape

```text
1^(2m+3) 110 1^(2q+6) 01010 y.
```

This is `BB6.Agent37E110111.eLong_run` in the independent standalone Lean source `E110111Standalone.lean`, reconstructed from [E110111Standalone.tar.xz.b64](./E110111Standalone.tar.xz.b64) using [unpack_standalone.py](./unpack_standalone.py). Its restored SHA256 is `599df59ff3054172e49447d2e3836b2439239c2e62778110f1976ec84d7d0c29`, and source helper `E110111StandaloneBase.lean` SHA256 `72a3c807e13a1112f9ad1f27723202a3bfafc4ca09cefacaf3ace5f1386aecf3`. Archived xz-tar compressed bytes SHA256 `090f6e069fe70903f07f438f4e64571b35e8d60c5d99d3686d363f92303d0d72`.

The local **complete actual literal-table** Lean 4.36.0-rc2 kernel compilation succeeded with `#print axioms eLong_run` reporting exactly `[propext, Quot.sound]`; no `sorry`, `admit`, `native_decide` or nonstandard postulates. All five reused helper lemmas (`run_add`, `scan_run`, `cWalk_run`, `cBase`, `sweepD_run`) are locally reproved from the explicit source table in the standalone archive, likewise with standard axioms only. The standalone checker imports the existing literal original-machine definitions from [BoundaryWitness.lean](./BoundaryWitness.lean), which specifies all 12 transition entries, finite tape zipper and halt semantics. The proof does not depend on the original-source CI runner.

## Transparent derivation and stronger candidate F/0 macro

1. The E boundary takes exactly `2q+4` transitions to the A-on-zero scanned state with left tape `(01)^(q+1) P_(m+3) 11` and right `110111 y`. The local `eLong_two`, `scan_run`, `eLong_scan` prove this for all parameters.
2. A **universally quantified 20-step turnaround**, independent of *every* left tape L and right tail y, maps A/0 with right `110111 y` to C/1 with unchanged left L and right `101010 y`. The standalone `a110111_turn20` is proven by direct symbolic reduction of the literal six-state step function, with `#print axioms` only `[propext]`.
3. The existing structural C-on-one reverse sweep is reproved independently and consumes `(01)^(q+1)` in exactly `2(q+1)` transitions, producing `1^(2q+2)` immediately right of head.
4. Four C turn steps (`cBase`) plus two B/0 transitions (`sweepB_two`) enter a D/0 stack sweep whose right packet is exactly `110 1^(2q+6) 01010 y`. The D sweep (`sweepD_run`) consumes the `m` alternating pairs in `2m+3` transitions, yielding the promised physical F/0 endpoint.
5. Durations sum to `(2q+4)+20+2(q+1)+4+2+(2m+3)=2m+4q+35`. There is no finite sampling in the proof.

**Corollary candidate against original upstream modules:** composing the pre-existing Agent31 original-source `prefix_E` with this theorem yields, for all k,q,y, the full F0-to-F0 endpoint

```text
I_(3k+4)(0 (10)^q 110111 y)
  --[12k² + 49k + 68 + 4q raw steps]-->
I_(8k+5)(0 1^(2q+6) 01010 y).
```

The exact unmodified-source composition is checked in [E110111Pairs.lean](./E110111Pairs.lean) as a proof script, with one source-import syntax correction, but cannot yet be claimed as a fully rebuilt original-source theorem. This module typechecked locally against a source-signature-compatible shim; the shim treated the formerly certified `prefix_E` as an **explicitly flagged external theorem assumption**, though all E boundary sweep lemmas were reproved locally in the standalone source with no assumptions. The raw E-boundary lemma is therefore stronger in verification status than the F-entry composition, and these statuses must remain separate. The parameter q=0 specializes to Agent32's pre-existing `ETripleZero.lean` result, while q>0 is the new generalization in this repository, subject to upstream prior-art search.

## Independent raw numerical checks and use

An independently coded physical sparse-tape raw interpreter tested 2,160 parameter instances k=0..29, q=0..17, four deterministic arbitrary right-tail samples per parameter, checking exact primitive time and entire physical right tape after trimming terminal implicit zeros. All comparisons agreed. This numerical experiment corroborates the all-parameter kernel theorem and is not its proof.

The general q≥1 rule appears at a previously unsupported conditional F-section reached from synthetic unary length 68 in our conservative source macro interpreter after 53 section transitions: `I_N(0(10)^4 110111111)`. The four *authentic* blank-origin unary seeds (5,9,15,39) are separate questions; none has been proved to enter this particular cylinder. A pure symbolic E-family extension does **not** prove a blank-origin invariant, a rooted machine decision or an improved BB(6) bound.

## Reproduce

With the uploaded Lean 4.36.0-rc2 on PATH, execute the restore script `unpack_standalone.py` (requires `filelock`), then from this directory kernel-compile `BoundaryWitness.lean`, `E110111StandaloneBase.lean`, `E110111Standalone.lean` in order with `LEAN_PATH=.`. In the third source, inspect the printed axiom report. For original-source checking, compile `E110111Pairs.lean` after the exact original `Boundary`, `CryptidSix`, and `CryptidPairs` source files with their preexisting SHA-pinned recovery scripts; **that full build has not yet completed in actual CI**.
