# Current status — 23 November 2026, source-verified

**New exact last-burst lower bound:** For the authentic original pinned Cryptids blank-source accelerated run, if the last-reset branch7 state obeys `y+3=2*x`, `x%32=29`, and the correct long-burst equation `4*x+3*n+15=3*2^(n+2)` at `n>=18`, then **`n>=16255`**. This is source-proved **without a sampled root-orbit cutoff**: Lean4.36 local kernel [CI 45121716046](https://github.com/FlareZ123/bb6/actions/runs/45121716046) and *full original pinned Cryptids-source Lean4.35* [CI 45122135963](https://github.com/FlareZ123/bb6/actions/runs/45122135963) both succeeded. Proof: [BB429Branch29BurstFloor.lean](BB429Branch29BurstFloor.lean), [BB429Branch29Source.lean](BB429Branch29Source.lean).

**Prior accepted root restriction:** The joint [BB429Branch29Reflect1024.lean](BB429Branch29Reflect1024.lean), [BB429Branch29Small.lean](BB429Branch29Small.lean) and [BB429Branch29All.lean](BB429Branch29All.lean) are now *also locally Lean accepted in CI 45121716046*. Thus every genuine blank-reachable reset-line `q` has one of 38 necessary residues modulo1024, including `q<21` excluded; these are not sufficient for reachability. The previously staged original-source modulo16384 last-burst corollary was separately accepted in CI 45113326621.

**Open formula for the true next breakthrough:**
`n=127+128k`, `q=3*2^(n-5)-(3k+4)` for `k>=0`. A uniform symbolic root impossibility of the dyadic cylinders `q≡-(3k+4) mod2^E`, for a suitable `E<=n-5` at *every* k, would close the entire 29(mod32) branch7 long-burst feeder. See [NEGATIVE_DYADIC.md](NEGATIVE_DYADIC.md) and [negative_dyadic_scan.cjs](negative_dyadic_scan.cjs), including the essential caution that some signed inverse rays have genuine infinite cycles but do **not** represent positive source reachability. The adaptive [BB429Branch29Prefix.lean](BB429Branch29Prefix.lean) is a **new unverified general prefix-cover soundness proposal**, not yet an accepted theorem; it targets dramatic compression of finite k certificates while the all-k question remains open. This intermediate work does not decide #429 or BB(6).

---

## Source-verified and stronger local results — 23 November ~04:45 UTC

**Pinned original Cryptids source bridge now accepted:** [CI 45111763374](https://github.com/FlareZ123/bb6/actions/runs/45111763374) succeeded in both its standalone and pinned original Lean/Mathlib/source jobs. It verifies `BB429Branch29Source.source_29_q_eight_mod64` and `source_branch7_29_burst_mod8192` (all transitive axioms `propext, Classical.choice, Quot.sound`, no `sorryAx`). Thus this branch's genuine original-source pre-reset final-burst length `n>=18` satisfying `4x+3n+15=3*2^(n+2)` and `x%32=29` must obey `n%8192 in {8063,4991,2047,1919,4095,6143,2943,8191}`. This is still only a necessary constraint, **not a halt/nonhalt proof**.

**Latest local proof accepted:** [CI 45113335816](https://github.com/FlareZ123/bb6/actions/runs/45113335816) verifies that after excluding q=10 and122(mod128) using Agent33's rigorous affine inverse `BB429Kernel.cert_sound`, the necessary local-root q set sharpens to **{2,15,47,58,63,74,79,82,111,127} modulo128** — ten out of 128 parameter classes. The same CI accepts `BB429Branch29Arithmetic.local_branch29_burst_mod16384` for the previous twelve q classes, n%16384 in **{16255,4991,10239,14335,2943,8191,13183,2047,1919,6143,11135,16383}**. Both have the standard axiom profile, no oracle. Source-corollary modulo16384 compilation against unchanged upstream is running separately in [CI 45113326621](https://github.com/FlareZ123/bb6/actions/runs/45113326621); do not count as original-source verified until success.

**More complete root geometry in progress:** `BB429Branch29Reflect1024.lean` introduces a single 58-residue symbolic affine inverse-tree certificate at depth13 using existing sound Agent33 proof engine. It proposes to retain only 38 out of 1024 q residue classes uniformly, not by sampling 1024 concrete machine inputs. `BB429Branch29Small.lean` proposes to exclude the entire q<21 finite prefix by certified rank cutoff after 553 root macro steps ending rank2676 > highest target rank2673. Both modules are **unverified pending local CI**, so neither must be labeled accepted yet.

---

# #429: original blank-root odd-reset class 29 — inverse and finite-rank certificates

**Current evidence:** Local original-table accelerator theorems are accepted by Lean 4.36.0-rc2 with no `sorryAx`; updated source-connected theorems against pinned upstream Cryptids are pending a fresh complete source CI. These are genuine necessary restrictions, **not** a #429 halt/nonhalt decision or exact BB(6).

## Uniform mathematical theorem

For each `q>=21`, if the actual blank-start local accelerated orbit reaches

```
(u,w) = (32q+29, 64q+55),
```

then **`q%16 in {2,10,15}`**, excluding **13 of 16** residue classes, with no exceptional value. Lean-verified in [run 45109777431](https://github.com/FlareZ123/bb6/actions/runs/45109777431); transitive axioms only `propext, Classical.choice, Quot.sound` (no `sorryAx` or `native_decide`).

The first uniform theorem `BB429Branch29.rooted_29_q_two_of_eight` excluded six of eight q classes ([run 45108772982](https://github.com/FlareZ123/bb6/actions/runs/45108772982)). The deeper `BB429Branch29Mod16.no_29_q_seven_mod16_except55` excluded q=7 mod16 uniformly except the singled out q=55 ([run 45109428286](https://github.com/FlareZ123/bb6/actions/runs/45109428286)). A separate finite rank certificate excludes q55, completing the uniform theorem in run 45109777431.


## Stronger certified all-parameter restrictions (23 November, after first checkpoint)

The 29(mod32) reset-line first-counter parameter is now restricted **for every q>=21**, not merely for sampled inputs:

- `BB429Branch29Mod64.rooted_29_q_eight_mod64`: q mod64 in **{2,10,15,18,31,47,58,63}**, kernel-verified in [CI 45111484181](https://github.com/FlareZ123/bb6/actions/runs/45111484181). Entire q=26,34,42,50 mod64 cylinders are excluded. In particular the rooted (13 mod32,1 mod8) row was proved directly by exact double inversion.
- `BB429Branch29Mod128.rooted_29_q_fourteen_mod128`: q mod128 in **{2,10,15,31,47,58,63,74,79,82,95,111,122,127}**, kernel-verified in [CI 45111872004](https://github.com/FlareZ123/bb6/actions/runs/45111872004). Entire q=18 and66 mod128 cylinders are excluded. It introduces the reusable exact rooted odd-three row: for genuine root-reachable a>=13, if a%8=3 and b odd, then b%8=7.
- `BB429Branch29Odd31.rooted_29_q_twelve_mod128`: q mod128 in **{2,10,15,47,58,63,74,79,82,111,122,127}**, kernel-verified in [CI 45112328855](https://github.com/FlareZ123/bb6/actions/runs/45112328855). The *entire* q=31 mod64 cylinder is excluded by the two-way forced inverse at its odd third ancestor. This is a genuine additional uniform exclusion rather than a single finite q.
- The new `BB429Branch29Arithmetic.local_branch29_burst_mod16384` is staged for a focused kernel check and packages the last-reset exponential arithmetic over the twelve surviving q classes. Until that job succeeds, do not claim its new modulo16384 result verified.

All three accepted refinements have only the standard transitive axiom profile `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, and require no finite-orbit assumption.

The pinned original Cryptids source verification is intentionally a separate issue. Third complete source run [45111763374](https://github.com/FlareZ123/bb6/actions/runs/45111763374), at original-source snapshot `ef18e2b2...`, contains the modulo8192 source corollary and is in progress as of 04:34 UTC. Its standalone local chain passed; the original-source job is not yet concluded. The proposed modulo16384 corollary is not in this run.

## Exact source ancestry and exceptional index

`BB429Branch29.lean` proves that any genuinely reached `(32q+29,64q+55)` has the forced inverse chain

```
(32q+29, 64q+55)
(16q+13, 96q+84)
( 8q+ 5,112q+97)
( 4q+ 1,120q+102)
( 2q- 1,124q+103)
(   q- 2,126q+102)
```

The alternative inverse at the fourth state produces a positive even first counter with odd second, impossible on the authentic blank root. Residue exclusions use the previously established all-time `rooted_one_strong`, `rooted_five_strong`, `rooted_even_sixteen`, `rooted_odd_three_one`, and positive-even root theorems.

`BB429Branch29Mod16.lean` further follows exact F predecessors for q=7 mod16. The resulting inverse target has counter `4r-1`, so at r=3, q=55, it equals 11: the ordinary two-inverse classification is not valid there. The proof isolates this exception rather than incorrectly discarding the special source branch.

`BB429FiniteAvoidance.lean` proves a **reusable sound Boolean finite-path verifier** and rank-cutoff theorem: when a checked path avoids a target and ends with strictly greater rank, no future source state can be that target, because all valid source transitions strictly increase rank. The genuine root's first 1586 exact source steps avoid `(11,7110)` and end at `(3069,996)` of rank 7134, above the target rank 7132. Both finite numerical claims are checked by Lean's ordinary `decide` kernel reduction. In q55 the forced ancestors include precisely that unreachable target, giving `BB429Branch29Mod16.no_29_q55`. Source and axiom profile accepted in [run 45109777431](https://github.com/FlareZ123/bb6/actions/runs/45109777431).

## Original Cryptids source bridge and last-reset consequence

`BB429Branch29Source.lean` now contains the stronger *proposed* source theorem, connecting through unchanged `BB429SourceMod16.source_run_to_local` at the pinned original Cryptids source revision `c86f15861709b76042998c5211c7b2f83991621b`.

Let a genuinely original-source root-reachable state `(x,y)` obey `y+3=2x`, `x%32=29`. For a final first-branch burst of length `n>=18`, if the rigorous last-reset equation

```
4*x + 3*n + 15 = 3*2^(n+2)
```

holds, then the candidate necessary conclusion is **`n%2048 in {895,1919,2047}`**. Indeed write `x=32q+29`, deduce `q>=21` from the exponential equation, apply the source-root `q%16 in {2,10,15}` theorem, and reduce `128q+3n+131=0 mod2048`. The older weaker source claim `n%1024 in {895,1023}` remains included.

**Acceptance boundary:** [run 45109015710](https://github.com/FlareZ123/bb6/actions/runs/45109015710) successfully built the unchanged original upstream Cryptids accelerator and compiled the first new local branch29 proof, but failed *before* the source connector due to an inherited Lean4.35 RC4 exponent-normalization error at `BB429Branch7Source.lean:31`; its separate standalone job exposed a missing compile prerequisite `BB429NewResidue`. Both actual diagnostic issues have been repaired on main, and the existing `agent6-429-source-chain.yml` now compiles the new rank and mod16 modules before the source wrapper. **Do not yet label `BB429Branch29Source.source_branch7_29_burst_mod2048` original-source verified** until this repaired exact closure compiles and prints clean axiom profiles.

## Boundaries and next research

The q classes `2,10,15 mod16` and branch7 odd-reset residues 13 and15 mod32 are still not proven unreachable; the final-burst congruence is necessary only. Neither the #429 original blank halt status nor BB(6) is decided. Investigate the source-root preimages of the surviving parameter cylinders rather than creating more disconnected modular gates. Agent33 was informed of the disjoint residue 13/15 problem via `communications/agent33/20261123T040800Z_agent18-branch29-uniform-exclusion-handoff.md`.
