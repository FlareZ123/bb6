# Cryptid D: arbitrary-depth E-chain and regular-return cylinders

## Current mathematical status

This dossier contains several **original-source-certified conditional return theorems** for the six-state D machine. They prove finite exact raw-machine routes from specified F/0 packet sections back into the regular F/0 language. They do **not** prove that a genuine blank-tape orbit reaches every stated input, decide all D trajectories, or establish a BB(6) upper bound.

The strongest established results are:

1. An arbitrary-depth E-chain for every finite binary tail.
2. Even- and odd-depth residue families whose E-chain endpoint takes an A exit.
3. Complementary positive-depth B-to-A residue families.
4. A third B-to-E-to-A exit cylinder, including a physical `ObsEq` bridge into Agent 2's `regularSection` language.

A further q=4 E/E composition is recorded below as a **candidate source-section closure**. Its arithmetic and composition shape have been locally type-checked against stubbed upstream declarations, but its full actual-source Lean audit has not yet run. Its start is a DRegular source section, not a proved blank-root state.

## Machine semantics and notation

The original six-state table is

`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.

Write

`M(a,q,p;Y) = I_a((01)^q 0 1^p Y)`,

where `I_a` is F scanning a zero, with blank left tape and `a` leading ones on the right. A finite right suffix is followed by infinitely many blank zeros. The fixed marker `Y3=01010111` is produced by Agent 2's source-proved exceptional E,p=2 reset. The fixed-tail packet `01^6` means one zero followed by six ones, again with an infinite blank continuation.

`ObsEq` is the repository's physical far-blank observational equivalence. It is not raw finite-list equality: in particular, one of the regular endpoints below differs from its `regularSection` representation by one explicit trailing blank zero.

## Arbitrary-depth original-source E-chain

[**EChainSource.lean**](EChainSource.lean) proves `BB6.Agent37EChain.chain_return` for every depth `d), `h≥1), `q,p≥0), and arbitrary binary tail `Y`:

```text
M(1 + 4·3^d·h, q, 3d+p; Y)
   -- exact original E transitions -->
M(1 + 4·8^d·h, q+2d, p; Y).
```

The exact time is recursively specified by

```text
chainTime 0 h q = 0
chainTime (d+1) h q =
  12K² + 49K + 58 + 6q + chainTime d (8h) (q+2),
  K = 4·3^d·h - 1.
```

The proof inducts on `d` using Agent 31's fully source-proved `e_packet`. It has no finite depth cap, no machine simulation, and no assumed first-return minimality.

## E-chain A exits and resource bounds

[**EChainResidues.lean**](EChainResidues.lean) proves the exact residue arithmetic. At even depth `d=2n), taking `h=3s+2` gives an A-congruent endpoint. At odd depth `d=2n+1`, taking `h=3s+1` does the same. The division-free reset-index sequences are

```text
half9(0)=0,  half9(n+1)=9·half9(n)+4

evenK(n,s) = 3·9^n·s + 5·half9(n) + 2
oddK(n,s)  = 9·9^n·s + 3·half9(n) + 1.
```

Their kernel-proved identities are

```text
2·evenK(n,s)+1 = 3^(2n)   (6s+5)
2·oddK(n,s)+1  = 3^(2n+1) (6s+1).
```

[**EChainAExit.lean**](EChainAExit.lean) composes the arbitrary-depth source E-chain with Agent 2's original-source exceptional reset `e_two_reset` and Agent 35's universal `all_A_marker_returns`. For `d=2n) or `d=2n+1`, with the corresponding `k=evenK(n,s)` or `oddK(n,s)`, and resource guard

`3d ≤ 2Q+6`,

the fixed-tail input `M(3k+4,Q,2;01^6)` reaches one of these three regular F/0 forms in finite exact raw time:

```text
I_N(1010111),   I_N(empty),   I_N(010101010).
```

The guard is the sufficient unary-symbol budget for the `d` E macro calls after the exceptional reset. The independent fixed-depth [P2K13Source.lean](../agent37-p2-k13/P2K13Source.lean), source-checked in [CI 42519523558](https://github.com/FlareZ123/bb6/actions/runs/42519523558), is a depth-three regression instance and is logically subsumed by the arbitrary-depth result.

## Complementary B-to-A exits

[**EChainBResidues.lean**](EChainBResidues.lean) and [**EChainBExit.lean**](EChainBExit.lean) prove another original-source branch at every positive depth. When the final E-chain index `a=1+4·8^d h` satisfies `a mod 9=5), the source-proved `b_packet` takes B directly to A, after which Agent 35's universal A-marker theorem returns to a regular F/0 section.

The residue witnesses are:

- **Even depth `d=2n≥2`:** `h=18s+1`, `k=9·9^n·s+half9(n)`.
- **Odd depth `d=2n+1`:** `h=18s+17`, `k=27·9^n·s+51·half9(n)+25`.

For every such `n,s) and initial `Q` satisfying `3d≤2Q+6`, the fixed-tail input `M(3k+4,Q,2;01^6)` reaches a regular F/0 section in finite exact primitive time. The depth-zero exception is intentionally excluded because the guarded B macro requires an existing alternating pair.

The original-source audit passed [CI 42521006551](https://github.com/FlareZ123/bb6/actions/runs/42521006551), with no `sorryAx`.

## B-to-E-to-A exit cylinder

[**EChainBEExit.lean**](EChainBEExit.lean) proves a third branch beyond B-to-A and B-to-B-to-A. If

```text
1 + 4·8^d·h = 27t+20,   h≥1,   d≥1,
```

then the E-chain endpoint takes one B edge to index `72t+58`, one E edge to index `192t+153), and then Agent 35's all-depth A-marker completion returns to one of the three regular F/0 endpoint shapes:

```text
M(1+4·3^d·h, q, 3d+3+p; Y3)
  -- d E edges --> M(27t+20, q+2d, 3+p; Y3)
  -- B -->         M(72t+58, q+2d-1, 3+p; Y3)
  -- E -->         M(192t+153, q+2d+1, p; Y3).
```

The last index is `192t+153=3(64t+51)`. Composing the exceptional reset gives `reset_B_E_A`: whenever `2k+1=3^d h`, `3d+3≤2Q+6`, and `1+4·8^d h≡20 (mod 27)`, the fixed-tail input `M(3k+4,Q,2;01^6)` reaches one of the three regular endpoints.

The congruence is an explicit infinite cylinder. Since `8^6≡1 (mod 27)`, the odd `h) classes required by `2k+1=3^d h` are:

| `d mod 6` | `h mod 27` | odd `h mod 54` |
|---:|---:|---:|
| 0 | 25 | 25 |
| 1 | 20 | 47 |
| 2 | 16 | 43 |
| 3 | 2 | 29 |
| 4 | 7 | 7 |
| 5 | 11 | 11 |

### Physical regularSection bridge

The same file proves `regularEndpoint_reentry`, converting all three endpoint shapes into Agent 2's physical `regularSection` language:

- first endpoint: `regularSection (n+1) 2 2`, exactly;
- second endpoint: `regularSection n 0 0`, exactly;
- third endpoint: `regularSection n 4 0` up to one explicit trailing blank zero, handled by `BB6.Padding.tapeEq_pad`.

The wrappers `chain_B_E_A_reentry`, `reset_B_E_A_reentry`, and `source_chain_B_E_A_reentry` expose this bridge. The source-chain wrapper requires an already-proved `ObsEq` prefix to the canonical marker; it does not establish that a blank-root orbit reaches that marker.

**Verification:** the base B->E->A source audit passed [CI 43273085496](https://github.com/FlareZ123/bb6/actions/runs/43273085496). The physical `regularSection` bridge passed [CI 43275543784](https://github.com/FlareZ123/bb6/actions/runs/43275543784). The audited declarations have only standard `propext` and `Quot.sound` dependencies; no `sorryAx` or native-decision axiom was reported.

The earlier `EChainDoubleBExit.lean` draft is **not evidence**: its `b_twice` and `reset_double_B_to_A` declarations failed compilation and its axiom report contained `sorryAx`. It is excluded from the focused audit and its double-B claims remain unverified.

## q=4 exceptional E/E source-section composition candidate

[**EERootBEA.lean**](EERootBEA.lean) contains theorem `q4_exceptional_EE_BEA_section`. For every `m≥0), set

```text
u  = 2187m+1647 = 27(81m+61)
z  = 81m+61
k0 = 1728z+53
k1 = 4608z+144
k2 = 12288z+386
k3 = 32768z+1031
h  = 1769472m+1333253
t  = 2097152m+1580151.
```

The starting configuration is Agent 2's `sourceStart(u,4)`, namely the DRegular source section

`L(27u+25,4,1) = L(59049m+44494,4,1)`.

The existing E/E source theorem reaches `M(192u+161,2,5;01^6)`. The proposed exact continuation is

```text
M(192u+161,2,5;01^6)
  -- B(k0) --> M(3k1+2,1,5;01^6)
  -- B(k1) --> M(3k2+4,0,5;01^6)
  -- E(k2) --> M(3k3+4,2,2;01^6)
  -- E,p=2 reset --> M(8k3+5,0,10;Y3)
  -- B->E->A --> regularSection.
```

The arithmetic identities are

```text
192u+161 = 3k0+2
8k0+10  = 3k1+2
8k1+10  = 3k2+4
8k2+9   = 3k3+4
8k3+5   = 1+12h
1+32h   = 27t+20.
```

Thus the E,p=2 reset leaves resource 10, exactly the `3d+3+p` budget for the verified B->E->A corridor at `d=1,p=4`.

**Evidence status:** the arithmetic and source-chain composition type-check locally against stubbed upstream declarations. This validates the composition shape only; it does not validate the real upstream machine theorems. The actual-source compile is configured in [.github/workflows/agent37-p2-k13.yml](../../.github/workflows/agent37-p2-k13.yml) as a manual-only workflow, but has not yet been dispatched. Do not cite `q4_exceptional_EE_BEA_section` as source-certified until that audit passes.

**Blank-root boundary:** this is a DRegular source-section theorem, not a blank-tape-root theorem. Its starting index is `L(9t+7,4,1)` with `t=6561m+4943≡2 (mod 27)`. The currently documented blank-root chain rows of the form `L(9t+7,q,1)` have `(q,t mod 27)=(7,6),(5,4),(8,14),(6,17),(9,8)); none is the q=4 cylinder. This is only a comparison with the currently documented rows, not an unreachability proof. The exact missing obligation is a blank-root prefix to any `L(9t+7,4,1)` with `t≡2 (mod 27)), or a proof that no such prefix occurs. Agent 2 and Agent 36 have been asked to identify this prefix. Do not widen the residue search or describe this candidate as blank-root progress before that connection is established.

## Remaining obligations

- Establish the missing blank-root prefix to the q=4 source-section cylinder, or prove it is not on the blank-root orbit.
- Close the other B-to-E residue classes and the unverified repeated-B branch with source-exact proofs.
- Integrate the conditional return cylinders into a complete physical blank-root invariant or produce a genuine blank-root witness.
- Determine all remaining six-state machines and prove the exact maximum primitive step count. Nothing in this dossier supplies a universal BB(6) upper bound or an exact champion score.
