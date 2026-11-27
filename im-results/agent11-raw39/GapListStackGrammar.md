# Raw39 1LE F1 siblings: exact four-mode gap/stack reduction

**Status:** locally kernel-checked exact original-semantics macro transport and conditional nonhalting interface for 5777, 5779, 5787. No complete inductive invariant, leaf decision or parent Cover yet. Unlike the earlier sampled run grammar, the reduction includes arbitrary untouched left and right tails, actual blank entry, and all-time positive primitive-cost transport.

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

Every listed transition has a positive exact primitive cost for each variant. The frames are bit words, with c,d,e,f variant-specific. All details are in the formal modules. The partial abstract system deliberately has no A/2, F/3, or unsupported B rule: proving these are avoided on the authentic orbit is the open obligation. The gap system is independent of the F1 variant, though primitive costs differ.

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

## Next proof obligation

Construct an all-time invariant of the four-mode reduction, for example via a finite automaton on each stack and an inductive relation on their states, or a recursive typed gap language. A3 pushes a; B/a unwinding prepends 1 and increases the first gap by 2; the resulting section map obeys f(3x)=3f(x), f(5x)=311x, f(12x)=5f(x), f(115x)=511f(x) whenever the recursive subrun returns. The c rescan means a simple single-pass transducer is insufficient. These equations are paper consequences of the checked primitive rules, not separately formalized totality statements.

## Earlier experiments and falsifiers

The original [gaplist_orbit.py](gaplist_orbit.py) remains useful for finite comparisons of the three variants. The previously proposed alternating X/Y gap-run grammar is too broad: prepared tail [2,1] reaches C1 (5777, at Q step 65), and [3,1,3,1] returns a zero gap. Bounded local-window and raw FAR/SMT attempts did not close the three tables (sizes 1–7 unsuccessful, 8 timed out), nor did they close the separate residual 180. These failures do not prove impossibility of a stronger regular or context-free invariant.
