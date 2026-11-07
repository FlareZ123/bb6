# D Cryptid E,p=2 reset: complete k≡2(mod 3) two-return reentry

**Agent 31, 7 November 2026. Status: new source-derived all-parameter mathematical composition, with its finite tape-word/cost identities kernel-checked locally in Lean 4.36.0-rc2 and 192 independent exact primitive-machine regressions. A single imported theorem over the unchanged original-source Lean machine has not yet passed CI.** The input configurations are synthetic F/0 sections. They are not known to arise on the actual blank orbit. This is intermediate mathematical research; it establishes neither D-machine nonhalting nor BB(6) maximality.

## Exact quantified claim and scope

The original six-state D table is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Write `I_a(Y)` for state F scanning blank with physically blank left tape and right tape `1^a Y 0^infinity`, `P_q=(01)^q`, `L(a,r,b)=I_a(P_r 1^b)`, and the packet `M(a,q,p;Y)=I_a(P_q 0 1^p Y)`. Physical equality ignores a finite number of explicit trailing blank zero symbols.

For all natural `t,u` and each `j∈{0,1,2}`, set `k=3t+2`, `q=3u+j`. There is a two-designated-return path from `M(9t+10,q,2;0 1^6)` to the following regular sections, with the exact total **defined primitive transition** counts:

| `j` | Output after the second F/0 return | Total primitive steps |
| --- | --- | --- |
| 0 | `L(64t+16u+76,2,2)` | `876t²+384tu+2219t+48u²+506u+1430` |
| 1 | `L(64t+16u+75,4,0)` | `876t²+384tu+2219t+48u²+506u+1464` |
| 2 | `L(64t+16u+97,0,0)` (pure unary) | `876t²+384tu+2603t+48u²+602u+2010` |

The second row's literal source endpoint ends in `(01)^4 0`. Its last zero is an unobserved blank, giving the physically equivalent `L(a,4,0)`. The third row's final A-code theorem requires appending an explicit blank zero to the input; the original tape already contains that same implicit blank.

These are mathematical identities composed from already certified original-source macros, but their *combined* Lean original-machine import is pending. The finite regression independently confirms, for its checked sample, that the two designated endpoints are the **first two physical F/0 returns**. The general source macro theorem stated above is about designated endpoints; claiming universal strict first-return minimality additionally requires composing the source strict-first-return lemmas.

## Reduction to three already source-proved exits

[Agent 2's exact source E,p=2 reset](../agent2-packet-shift/PacketP2ResetSource.lean), successful [CI 42332391372](https://github.com/FlareZ123/bb6/actions/runs/42332391372), says for all k,q:

```
M(3k+4,q,2;0 1^6)
  --[12k²+49k+68+4q]-->
M(8k+5,0,2q+6;(01)^3 11).
```

For `k=3t+2`, the reset unary prefix is `8k+5=3(8t+6)+3`. Thus the next original-source section is A with index `k_A=8t+6`, and its word after the initial zero is `1^(2q+6) (01)^3 11`. This right word has exactly three suffix forms:

- **`q=3u`:** `(111)^(2u+2) 0 1010111`, so apply [Agent35's arbitrary-code A-to-F-on-zero theorem](../agent35-cryptid-code/ABridgeCode.lean) with `2u+2` triple tokens and terminal zero. The final untouched seven-bit suffix is `1010111`; its initial one is absorbed into the unary prefix and leaves `(01)^2 11`. This yields the first row.
- **`q=3u+1`:** `(111)^(2u+2) 1101010111`. Apply [Agent26's exact A 1101010111 terminal after arbitrary code](../agent26-cryptid-e-gate/A1101010111Code.lean), original-source [CI 41871559177](https://github.com/FlareZ123/bb6/actions/runs/41871559177), to reach `I_(64t+16u+75)((01)^4 0)`. This yields the second row by physical trailing-zero equivalence.
- **`q=3u+2`:** `(111)^(2u+3) (10)^3 111`. Apply Agent35's general A code with `2u+3` triple tokens and four further tokens `[10,10,10,111]`. The final zero is implicit on the actual tape, so use [original-source physical padding bisimulation](../agent32-cryptid-padding/BoundaryPadding.lean), `source_init_pad` and `source_chain`, for an end-to-end source proof. This yields the third row.

No residual complicated packet tail survives any of these three A exits. Consequently, the **entire infinite k≡2(mod 3) branch of the specific fixed-tail E,p=2 reset** is theoretically routed to regular `L` after one further original-machine F/0 endpoint, regardless of the size of `t,u`. This narrows the previously documented k≡1,2 outstanding branches of [Agent2's packet dossier](../agent2-packet-shift/README.md) to primarily k≡1, subject to imported source proof and the changed-tail recurrences.

## Verification and reproducibility

The new [P2K2Shapes.lean](P2K2Shapes.lean) restates the exact original `CryptidA.wordCode`, `wordInc`, and `wordCost` definitions as independent local functions, and proves the three suffix decomposition identities and all three displayed polynomial cost identities **for every natural t,u**. Lean 4.36.0-rc2 locally compiled all six declarations with standard axioms `[propext, Quot.sound]`; there is no `sorry`, `native_decide`, or invented machine theorem. This is a **standalone algebra/tape proof**, pending correspondence to the original modules.

The standalone [check_p2_k2.py](check_p2_k2.py) uses the 11 defined entries of the original machine table and a sparse two-way tape. It checks **192** starts (`t,u∈[0,7]`, three residues), finding two physical F/0 returns, verifying each return's complete right tape and exact elapsed steps, with **192/192 matches** and no timeout (maximum two-event runtime 88,537 transitions). It uses Python's standard library only; exact primitive-step regressions are additional finite evidence, not a proof of the unbounded claim.

**Trust boundary:** the currently available repo imports already establish the E reset and the A exits independently under the unchanged D source. The deterministic algebraic composition is reproducible in this note. The source *integration theorem* should use those unchanged imports, `run_add`, the exact word identities, and the padding bisimulation; do not cite the composite as original-source-kernel-verified until the complete imported module compiles. External novelty relative to existing Cryptids research remains unreviewed.

## Remaining mathematical obstacle

This is a class of deliberately prepared F/0 tape inputs. Its closure shows nothing about whether the actual blank machine reaches such packets or whether a later regular return can enter a fatal F/1 gateway. The k≡1 reset (leading to a second E packet with altered tail) remains structurally hard, as does every all-time authentic blank-root invariant. These are higher-value next targets than extending bounded numerical orbit traces.
