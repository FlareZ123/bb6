# Raw39 1LE F1 siblings: exact four-mode gap/stack reduction

**Status:** locally kernel-checked complete nonhalting theorem for 5777, 5779, 5787 on exact original-semantics artifact-linked dependencies. Their every compatible completion is nonhalting. Fresh source-CI acceptance and parent assembly remain pending. Unlike the earlier sampled run grammar, the reduction includes arbitrary untouched left and right tails, actual blank entry, and all-time positive primitive-cost transport.

## Literal tables and boundary

The three tables share `1RB1LE_1RC0LE_0RD---_1LD0RA_0LB0RF_1RE` with F1 respectively `0RC,0RE,1RC`. C1 remains undefined. At time 170 the F0 section has left zipper list 00 (current included), right gap list [1,5,1], encoded by gap(g)=0^g11. P takes 70 steps and changes [1,5]W to [3,1,2]W. Q preparation takes 63 steps and enters A scan on W with stack base 11100111110011. Thus time 303 is the authentic abstract initial configuration (A, empty stack, [1]).

## Exact reduction

A configuration is (mode, stack of frames with top first, gap word); the gap alphabet is {1,2,3,5}. A and F scan the first bit of the encoded word (or blank zero when empty); H is an F1 boundary after consuming two adjacent gap ones; B unwinds the stack. The fixed stack prefixes for A/F/H (excluding the current cell) are respectively 00, 01000, 0101000. Let x denote the unmodified word suffix, S the stack, and a–f the six frame types.

| Mode/input | Successor |
| --- | --- |
| A / 3x | A, aS, x |
| A / 1x | F, S, x |
| A / 5x | B, S, 111x |
| A / empty | B, S, 11 |
| F / 2x | A, bS, x |
| F / 1x | H, S, x |
| F / 5x | B, S, 312x |
| F / empty | B, S, 31 |
| H / 1x | A, cS, x |
| H / 2x | A, dS, x |
| H / 3x | F, eS, x |
| H / 5x | A, fS, x |
| H / empty | B, S, 3111 |

The B rules act on g x with g=1 or 3 and h=g+2 (the c/e rules allow any gap); their outputs are:
- aS -> B,S,1 h x;
- bS -> B,S,3 h x;
- cS -> A,bS,g x (this rescan is the essential previously missing mechanism);
- dS -> B,S,3 1 h x;
- eS -> B,S,3 1 g x;
- fS -> B,S,3 1 1 h x;
- empty stack -> A,empty,h x, including the next P and Q setup (171 primitive steps).

Every listed transition has a positive exact primitive cost for each variant. The frames are bit words, with c,d,e,f variant-specific. All details are in the formal modules. The partial abstract system deliberately has no A/2, F/3, or unsupported B rule: the grammar below proves these are avoided on the authentic orbit. The gap system is independent of the F1 variant, though primitive costs differ.

## Proof and reproduction

Packed JSON [Raw391LEGapSystem.json.xz.b64](Raw391LEGapSystem.json.xz.b64) contains two UTF-8 Lean sources. Extract with:
```python
import json, lzma, base64
from pathlib import Path
data=json.loads(lzma.decompress(base64.b64decode(Path("Raw391LEGapSystem.json.xz.b64").read_text())))
for name,source in data.items():
    Path(name).write_text(source)
```
Source SHA256:
- Raw391LEGapMacros.lean: bb37b243540b04fee8959850e8fc3b005aec670c768864268e3e10b934fe371a
- Raw391LEGapSystem.lean: 3e4e6420568daf8e65f784742b29d3a1797aa3e82efea21517bf063de79536a7

Local Lean 4.36.0-rc2 (compiler SHA256 matches artifact manifest) compiled both modules against source-accepted Raw39 artifact 15036330602 (run 45639153728). The reachable SweepPumping/Frontier/RootShift/SparseZipper/Symmetry source and object pairs match the artifact manifest; SweepPumping source SHA256 346daa8772700ee235c8342a1128153c43317dd1724e8f95b5e004e50fbd732f. Compile in that artifact directory with LEAN_PATH pointing to it, Macros first then System. This is a locally checked original-source artifact link, not a fresh CI acceptance or a complete machine verdict.

`BB6.Agent11Raw39Gap.step_sound`, `start_sound` and `never_of_invariant` have axioms [propext, Quot.sound]. The last theorem proves NeverHalts for every compatible total completion of each table if an invariant I contains initial and every I configuration has a Step successor in I. No sorryAx or native_decide. The source-certified macro system removes the need to model the three raw tables independently.

## Closed inductive grammar (2026-11-27)

Let f be the next A/empty-stack section word (a normalized B return has its first gap increased by two). Define G by the seven terminal words 1, 51, 111, 55111, 115111, 5111, 11111; prefix 3; and the eight prefixes below applied to arbitrary G suffixes.

| Input | Next section |
| --- | --- |
| 3x | 3 f(x) |
| 1135x | 51312x |
| 51312x | 3 111312x |
| 111312x | 5512 f(x) |
| 5512x | 3 11512x |
| 11512x | 5115 f(x) |
| 5115x | 3 11115x |
| 11115x | 535 f(x) |
| 535x | 3 1135x |

The terminal transitions are 1 -> 51 -> 3111; 111 -> 55111 -> 3115111; 115111 -> 51155111 (= 5115·5111); 5111 -> 311111; 11111 -> 5355111 (= 535·5111). Every rule returns in finitely many positive-cost primitive steps and preserves G. The two nested rescans reduce to f on the proper grammatical suffix, so ordinary structural induction suffices; no assumption that arbitrary words return is used.

`Raw391LEGapGrammar.lean` (packed separately as [Raw391LEGapGrammar.lean.xz.b64](Raw391LEGapGrammar.lean.xz.b64), SHA256 627855a60e4c2f7df514aacd99a90365997e771c6f3c950d9da5f6be55676de0) defines `Path`, `Eval` with arbitrary preserved frame stack, `Good`, and `good_eval`. The key nested rescan lemmas are `ev111312` and `ev11115`. `good_eval` is axiom-free. `never` has only propext and Quot.sound. The three sources compile Macros -> System -> Grammar in Lean 4.36.0-rc2 with the exact dependencies above. The earlier bounded failed experiments are not needed for the proof.

The proof is a literal-table nonhalting result; source CI and the full normalized 1LE child audit are separate acceptance obligations. Only leaf 180 remains discovery-open in 1LE.

## Earlier experiments and falsifiers

The original [gaplist_orbit.py](gaplist_orbit.py) remains useful for finite comparisons of the three variants. The previously proposed alternating X/Y gap-run grammar is too broad: prepared tail [2,1] reaches C1 (5777, at Q step 65), and [3,1,3,1] returns a zero gap. Bounded local-window and raw FAR/SMT attempts did not close the three tables (sizes 1–7 unsuccessful, 8 timed out), nor did they close the separate residual 180. These failures do not prove impossibility of a stronger regular or context-free invariant.
