# #429 low-J, low-even and blank-root prefix research

**Status: intermediate research.** The strongest current artifact is a 169,592-step blank-root prefix theorem candidate ending at J(0,344). Its full original-source Lean workflow has not passed. This dossier establishes neither that #429 runs forever nor any exact or upper bound for BB(6).

## Strongest root-prefix candidate

The central declaration is
`BB429Low43BlankRootExtension.blank_root_lowEvenR32_to_junc0_344`
in `Low43BlankRootExtension.lean`. Its statement asserts an exact physical run from the authentic blank tape to J(0,344) at step 169,592, records the intermediate Junc representations, and excludes the C/01 halting gateway at every primitive prefix.

The proposed checkpoints are:

| Absolute step | Prepared state | Segment completed |
|---:|---|---|
| 43,862 | J(0,216) | Extended concrete low-even r=32 root chain |
| 55,001 | J(93,45) | First outer-safe ladder |
| 58,269 | J(74,90) | Low-odd v=22,n=34 |
| 67,690 | J(0,248) | Low42 j=45,k=14 |
| 78,829 | J(93,77) | Second outer-safe ladder |
| 86,113 | J(58,154) | Low-odd v=38,n=26 |
| 100,176 | J(119,35) | Outer-safe U=58 |
| 136,182 | J(69,186) | Low43 / low-even / outer-safe prepared chain |
| 155,943 | J(141,45) | Outer-safe U=69 |
| 159,739 | J(122,90) | Low-odd v=22,n=58 |
| 169,592 | J(0,344) | Low42 j=45,k=38 |

The four large segments compose as follows:

- Blank root to J(0,216): 43,862 steps. The concrete r=32 leaf starts at J(45,58), reaches J(11,146) in 4,407 steps, and is joined to the earlier root bridge in `LowEvenR32RootChain.lean` and `LowEvenR32RootExtension.lean`.
- J(0,216) to J(119,35): 56,314 steps, through outer-safe, low-odd, low42, and a second outer-safe/low-odd sequence.
- J(119,35) to J(69,186): 36,006 steps, through low43 v=17,k=50, a concrete low-even 4k return, outer-safe U=11,25,53, and low43 v=47,k=30.
- J(69,186) to J(0,344): 33,410 steps, through outer-safe U=69, low-odd v=22,n=58, and low42 j=45,k=38.

The 169,592-step statement is a finite-prefix claim only. It does not close the subsequent J/Junc dynamics.

## Uniform low43 entry: established component

For every (v,k\in\mathbb N), the exact original #429 source table has a uniform low43 entry from the complete tape represented by
`jTape (v+2*k+2) (2*v+1)`:

- after (4v^2+18v+22) successful primitive steps, the machine is at the exact C/0 configuration represented by `stage43 v k`;
- the scanned cell and immediate right neighbour are blank;
- the entry head is (2v+6);
- every earlier primitive prefix has head at most (2v+5).

The source delta theorem is `BB429Low43Delta.stage43_to_C0_delta`; the complete-tape representation and physical strict-record lift are in `Low43Physical.lean`. The focused CI run [43356966503](https://github.com/FlareZ123/bb6/actions/runs/43356966503) compiled `stage43_represented` and `low43_C0_record` with only standard axioms and no `sorryAx`. This is a uniform entry theorem, not a uniform C/0 return theorem.

## Corrected root-specific low43 continuation

For the simulated root checkpoint J(21,11), the parameters are (v=5,k=7). The uniform entry takes 212 steps to the C/0 record at local head +16. The corrected prepared-source continuation is:

| Segment | Steps | Net displacement | Maximum displacement | Endpoint |
|---|---:|---:|---:|---|
| C/0 to J(23,18) | 438 | -20 | +1 | J(23,18) |
| J(23,18) to J(11,62) | 909 | -37 | +28 | J(11,62) |
| Composed C/0 to J(11,62) | 1,347 | -57 | +8 | J(11,62) |
| J(21,11) including entry, to J(23,18) | 650 | -4 | +17 | J(23,18) |
| J(21,11) including entry, to J(11,62) | 1,559 | -41 | +24 | J(11,62) |

The earlier 119-step claim to J(0,9,25) was false: `tens 14` contains 28 bits. The corrected source monitors use the 438-step route to J(23,18), followed by the 909-step return to J(11,62). The finite source monitor theorems are in `Low43Continuation.lean`; their projection proofs use the correct reverse direction of `runWithMax_toDelta`.

The intended complete-tape physical lifts are in `Low43RootPhysical.lean`. That file had concrete CI failures: a prefix-existence witness, a reversed projection, three integer head-displacement equalities, and two unsupported `norm_num` tactic calls. Those diagnostics have been repaired in this branch using reflexivity, the reversed projection, and `omega`. **The repaired root-physical file has not yet been recompiled**, so its declarations and every-prefix head bounds remain candidates pending CI.

A separate concrete prepared low-even r=96 monitor proves J(49,2) to J(11,98) in 719 steps, displacement -89, maximum +12. This is one instance of the conjectural low-even 4k row, not a parameter-uniform theorem.

## Low-even r=32 concrete root leaf

`LowEvenR32NoFatal.lean` decomposes J(45,58) to J(11,146) into three exact guarded source segments of 3,192, 346, and 869 steps, total 4,407. Its physical lift uses the complete-tape `Represents` relation and preserves every prefix. The root bridge places the prepared input at step 16,280, giving the 20,687-step candidate endpoint J(11,146); the extension continues to J(0,216) at step 43,862.

The isolated r=32 module compiled in run [43365025686](https://github.com/FlareZ123/bb6/actions/runs/43365025686) and its public declarations had no `sorryAx`. That integrated workflow subsequently failed in the low43 continuation; this is not a green end-to-end result. The detailed derivation and exact segment table are in [the r=32 dossier](../agent32-429-loweven-r32/README.md).

## Reusable NoFatal converse and low42 extension

`NoFatalRunConverse.lean` introduces a general source-interpreter lemma:

```lean
run n z = some z'
fatalCZero z' = false
one z' ≠ none
--------------------------------
runNoFatal n z = some z'
```

The proof is based on the exact transition C/01 -> D/1 -> halt. A fatal visit cannot occur before a successful ordinary run ending at a live, nonfatal configuration. Both endpoint hypotheses are necessary.

`Low42NoFatal.lean` bridges `runWithDelta` to ordinary `run` and specializes the converse to the all-parameter low42 source theorem: from its exact post-bubble `stage42 j k` input, the  (20j+18k+79)-step run to J(0,0,4j+4k+12) is C/01-free. This is a prepared-stage source result; it does not include the preceding J-tape bubble prefix or by itself establish a physical all-prefix theorem. Both new modules are pending Lean CI.

A stronger physical counterpart is now added:
- `PhysicalNoFatalConverse.lean` proves directly from the physical #429 table that C/01 takes one step to D/1 and D/1 has no next step. Consequently, any successful physical run ending at a live, non-C/01 configuration is C/01-free at every primitive prefix. This argument does not use zipper representation.
- `Low42PhysicalNoFatal.lean` applies that machine-level converse to `Low42Physical.low42_raw_head_all`. For every (j,k), the canonical physical low42 run from `jTape (j+2*k+1) (2*j)` to its represented Junc(0,0,4j+4k+12) endpoint is C/01-free at every prefix.
- `PhysicalNoFatalConverse.physical_run_prefix_c01_free_of_c0_blank_right` also covers a physical C/0 endpoint with scanned zero and blank immediate right cell. It is reusable for the endpoint of a low43 C/0 record.
- `Low43PhysicalNoFatal.low43_C0_record_all_prefix_c01_free` applies that endpoint lemma to the all-parameter low43 physical entry, certifying every prefix from its Junc input through the blank-right C/0 checkpoint.

This closes the all-prefix physical safety gap for the canonical low42 run. `Low42PhysicalNoFatalAnyHead.low42_raw_head_any_c01_free` transports the result to every physical configuration representing the matching Junc input, preserving exact head displacement and all-prefix C/01 exclusion via `JuncCanonical` and `RootShift`. `Junc0ReturnMap28.junc0_return_map_28` now composes that arbitrary-head macro with six outer-safe physical segments to prove the uniform finite +28 map. These physical declarations are pending integrated Lean CI.

## Junc(0,w) return-map exploration

`Junc0ReturnMapExploration.md` records the 20-million-step discovery simulation and the still-unresolved J(0,744) -> J(0,924) segment. The finite +28 return branch is now formalized as `BB429Junc0ReturnMap28.junc0_return_map_28`, pending integrated Lean CI: for every (12\le r\le94), every physical configuration representing Junc(0,0,4(r+90)) has an exact original-machine run to a representation of Junc(0,0,4(r+97)), with every primitive prefix C/01-free. Thus the map Junc(0,w) -> Junc(0,w+28) is established for every multiple of four (408\le w\le736), not merely the simulated 28-spaced orbit.

The proof composes six physical outer-safe returns (U=0,3,9,21,45,93; 46,692 steps total) with the arbitrary-head low42 physical macro (parameters j=2r,k=94-r). The exact total is (46692+4(2r)^2+22(2r)+18(94-r)+79), equivalently (16r^2+26r+48463).

The observed J(0,744) -> J(0,924) segment takes 1,158,049 steps. Its proposed decomposition is:

| Component | Steps | Endpoint |
|---|---:|---|
| Outer-safe U=0,3,9,21,45,93,189 | 191,493 | J(381,3) |
| Unidentified low-width transition | 7,382 | J(387,2) |
| Low-even 4k N=1,K=193 | 3,761 | J(11,774) |
| Three J(11,w) -> J(11,w+32) cycles | 683,267 | J(11,870) |
| Outer-safe U=11,25,53,109,221 | 261,433 | J(445,17) |
| Low-odd v=8,n=217 | 5,306 | J(440,34) |
| Low42 j=17,k=211 | 5,407 | J(0,924) |

The 7,382-step transition J(381,3) -> J(387,2) is the principal unidentified macro. It is the low43 C/0 continuation instance (v=1,k=189). Agent 1 is pursuing a parameter-uniform C/0 continuation; this dossier does not claim that the gap is closed.

## Validation and limits

- `.github/workflows/agent32-429-low43-validation.yml` is a focused manual-only low43 audit.
- `.github/workflows/agent6-429-low42.yml` is the integrated manual-only audit for the r=32, low43, low42, and 169,592-step root chain. It now also compiles the NoFatal converse and low42 prepared-stage extension.
- Run 43350701536 compiled the corrected low43 source continuation before failing later in an unrelated module. Run 43356966503 compiled the uniform low43 physical entry. Run 43357322282 exposed the root-physical errors repaired in this branch. Run 43365025686 compiled the r=32 leaf but did not produce a green integrated workflow.
- The current integrated changes have not been dispatched through CI. The new NoFatal modules and the repaired root-physical declarations are candidates, not certified results.

All this work belongs in `im-results/`. No exact BB(6) value, universal BB(6) upper bound, or all-time nonhalting proof for machine #429 has been established.
