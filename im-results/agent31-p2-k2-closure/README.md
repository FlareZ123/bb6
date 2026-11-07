# D Cryptid E,p=2 reset: source-derived reentry for seven of nine index residues

**Agent 31, 7 November 2026. Status: two new source-derived all-parameter composition sectors, with word/cost identities locally Lean-kernel checked in 4.36.0-rc2 and 237 independent primitive-machine regressions, in addition to Agent2's earlier source-certified k≡0 sector.** Imported all-original-source composition modules have been prepared and syntax-checked against signature-matching axiom stubs, but have **not** passed unchanged-source CI. The underlying E, B and A component macros have separate unchanged-source Lean certificates. All inputs are synthetic F/0 sections; this intermediate research establishes neither authentic blank-orbit behavior nor BB(6).

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

## Additional k≡1 (mod 9) three-return sector, all q

A second, disjoint unbounded residue class now closes. Let the original exceptional-reset index be `k=9s+1` and `q=3u+j`, with arbitrary `s,u≥0` and `j=0,1,2`. Set the same initial `M(3k+4,q,2;0 1^6)=M(27s+7,q,2;0 1^6)`. Its first E,p=2 return enters `M(72s+13,0,2q+6;(01)^3 11)`. Because `72s+13=3(24s+3)+4` and `2q+6≥3`, the already certified [Agent31 source `e_packet`](../agent31-d-exceptional/PacketSource.lean) gives the **second** return:

```
M(72s+13,0,2q+6;(01)^3 11)
  --[12(24s+3)²+49(24s+3)+58]-->
M(192s+33,2,2q+3;(01)^3 11).
```

Now `192s+33=3(64s+10)+3`, so the third return enters the A-coded grammar. The initial two `(01)` pairs supply two `10` code tokens. The `2q+3` unary run then splits according to `q mod 3`. For every natural `s,u`, the outputs and total times from the **original** exceptional input through the three designated F/0 endpoints are:

| `j` | Regular physical output after third return | Total defined primitive transitions |
| --- | --- | --- |
| 0 | `L(512s+16u+104,2,2)` | `57036s²+3072su+23593s+48u²+674u+2503` |
| 1 | `L(512s+16u+103,4,0)` | `57036s²+3072su+23593s+48u²+674u+2537` |
| 2 | `L(512s+16u+125,0,0)` | `57036s²+3072su+26665s+48u²+770u+3251` |

The code/token suffixes are as follows: `j=0` consumes `[10,10]`, then `(111)^(2u+1)`, followed by `0 1010111`; `j=1` consumes the same tokens followed by the Agent26 `1101010111` A terminal; `j=2` consumes `[10,10]`, then `(111)^(2u+2)`, then `[10,10,10,111]`, and uses an **implicit physically blank** final zero. The last zero for the `j=1` A result is also physically implicit. These are exact source-derived compositions with the requisite physical-tape equivalence in the third branch.

[P2K1Mod9Shapes.lean](P2K1Mod9Shapes.lean) verifies **all nine** universally quantified word, total-time and output-count identities, with Lean's axiom audit `[propext, Quot.sound]`. An original-source [three-return composition candidate](P2K1Mod9Source.lean) imports the already checked source E/A modules and [P2K2Source](P2K2Source.lean). It compiled locally only with interface-matching stub source axioms; **a real source CI run remains mandatory**. Independently, [check_p2_k1mod9.py](check_p2_k1mod9.py) compares the original 11-rule Turing machine's three **first physical F/0 returns**, complete right tapes and exact elapsed steps for `s=0..2,u=0..4,j=0..2`: **45/45 starts, 135/135 return events**, at most **313,149** primitive steps.

## Combined arithmetic coverage

Agent2's genuine original-source [`e_two_k0_regular`](../agent2-packet-shift/PacketP2ResetSource.lean) already handles **all q** for `k≡0 mod 3` in two F/0 endpoints. The two new source-derived compositions handle **all q** for `k≡2 mod 3` (two endpoints, above) and **all q** for `k≡1 mod 9` (three endpoints). These three disjoint families cover **seven of nine congruence classes of k modulo 9**. The residual `k≡4,7 mod 9` classes enter nontrivial E/B chains, with the altered marker and possible repeated exceptional E boundaries. No uniform descent theorem for those cases is established here. No conclusion about actual-blank-root reachability follows from this arithmetic coverage.

## Verification and reproducibility

The new [P2K2Shapes.lean](P2K2Shapes.lean) restates the exact original `CryptidA.wordCode`, `wordInc`, and `wordCost` definitions as independent local functions, and proves the three suffix decomposition identities and all three displayed polynomial cost identities **for every natural t,u**. Lean 4.36.0-rc2 locally compiled all six declarations with standard axioms `[propext, Quot.sound]`; there is no `sorry`, `native_decide`, or invented machine theorem. This is a **standalone algebra/tape proof**, pending correspondence to the original modules.

The standalone [check_p2_k2.py](check_p2_k2.py) uses the 11 defined entries of the original machine table and a sparse two-way tape. It checks **192** starts (`t,u∈[0,7]`, three residues), finding two physical F/0 returns, verifying each return's complete right tape and exact elapsed steps, with **192/192 matches** and no timeout (maximum two-event runtime 88,537 transitions). It uses Python's standard library only; exact primitive-step regressions are additional finite evidence, not a proof of the unbounded claim.

**Trust boundary:** the currently available repo imports already establish the E reset and the A exits independently under the unchanged D source. The deterministic algebraic composition is reproducible in this note. The source *integration theorem* should use those unchanged imports, `run_add`, the exact word identities, and the padding bisimulation; do not cite the composite as original-source-kernel-verified until the complete imported module compiles. External novelty relative to existing Cryptids research remains unreviewed.

## Remaining mathematical obstacle

This is a family of deliberately prepared F/0 inputs. Its source-derived classification does not show whether the actual blank orbit reaches any such packet or whether later regular returns encounter the forbidden F/1 gateway. Remaining k≡4,7 modulo 9 reset families and any authentic blank-root all-time invariant are priority problems. Imported, unchanged-source CI checking of both new composite modules remains a prerequisite to upgrading their proof status.
