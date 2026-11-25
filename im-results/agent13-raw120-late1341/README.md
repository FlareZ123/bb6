# Raw120 E0=1LB index 1341: exact late halt

**Status: exact weighted threshold kernel-checked locally using original-source coverage artifacts; fresh repository-source CI in progress.** Two independent primitive simulators and the packed-stack generator agree that the partial table

`1RB---_1RC0LF_0RD0RF_1LD1RE_1LB1LE_0RA0LE`

(the exact index 1341 of the pinned 4351-leaf 1LB roster) first queries A1 after **224705** live steps. Head = 147; visited interval [-382,151]; 521 ones. The sole halt completion thus has 224706 primitive steps from canonical blank A. F0=0RA adds exactly one possible zero-write initial step; the complete incoming-delay list is [0,1]. The exact weighted threshold for the entire 25-completion cylinder is **224707**. The other 24 completions have no halt transitions at all.

This supersedes the provisional 3793 sibling bound and removes the need for a nonhalting certificate for index 1341. It does not by itself close the whole 1LB sibling, raw120, or BB(6).

## Exact accelerated proof

Encode the current cell and cells to its left as the low-order bits of L, and cells strictly to its right as the low-order bits of R. PackedZipper.lean proves read agreement with the exact sparse zipper, including unknown/halting transitions and implicit zeroes.

The 18-step sweep in state A has the universally quantified exact equation
`runP table 18 ⟨0,8*L,16*R+13⟩ = some ⟨0,32*L+24,4*R+1⟩`.
Here L and R are arbitrary natural-number tails. With W(b,n,x) = b^n (x+1) - 1, the iterated form is
`runP table (18*n) ⟨0,8*L,4*W(4,n,R)+1⟩ = some ⟨0,8*W(4,n,L),4*R+1⟩`.
The E1 leftward sweep independently gives
`runP table n ⟨4,W(2,n,L),R⟩ = some ⟨4,L,W(2,n,R)⟩`.

Late1341Macro.lean, Late1341Repeat.lean and Late1341Action.lean prove these equations and the cost-preserving action-list checker. generate_fast.py emits 116 independently checked shards. The exact trace consists of 1,050 repeated 18-step actions (174,960 primitive transitions), 1,253 E1 actions (22,280 transitions), and 2,304 ordinary runs (27,465 transitions). All 116 shards and the final joined `fastQuery` compiled locally in Lean 4.36.0-rc2 against the copied exact computational interface, with the standard axioms [propext, Classical.choice, Quot.sound]. A subsequent local run used the original-source compiled coverage/zipper dependencies from successful raw60 artifact 14996790073. PackedZipper, equivalent local macro/base sources, the repeat and action modules, all 116 shards, the joined trace and Raw120Late1341 compiled. The final `lateChecked`, `exact_halt`, `bound`, and `exact_weighted` all have only [propext, Classical.choice, Quot.sound]. The local macro proof and minimal generated base were mathematically equivalent variants, so fresh exact repository-source CI remains necessary for repository acceptance.

The primitive generate.py path remains a fallback. It emits the same exact table and a 225-segment replay. Raw120Late1341.lean consumes the `query` theorem through the existing ZipThreeHoleAudit and proves `lateChecked B hB`, `exact_halt`, `bound` and `exact_weighted`. The accelerated generator preserves the same interface; no trusted Python arithmetic is needed for any accepted theorem.

Reproduce from the repository root:
```sh
python im-results/agent13-coverage/unpack.py
python im-results/agent13-raw120-late1341/generate.py
python im-results/agent13-raw120-late1341/generate_fast.py
python tools/lean_compile_closure.py --workdir /tmp/a13-late1341 --jobs 3 im-results/agent13-raw120-late1341/Raw120Late1341.lean
```

For ingestion, render the exact leaf as `.last 224705 (0,true)` and use `lateChecked B hB` instead of reducing the entire primitive trace a second time. If nested inside a checked subtree, expose it as its own child and compose with the split checker. Preserve all other sibling obligations. No change to the accepted canonical roster is claimed.

The complete 1LB ingestion is implemented in `../agent3-tnf-raw120/generate_sibling.py` at commit 14d793565f2add1afbad5c0c68b22cf2d10a5a36. Manual source run [45687881460](https://github.com/FlareZ123/bb6/actions/runs/45687881460) checks both the exact repository trace and the generated sibling tree; pending, not a claimed sibling cover.

## Parent consumption

`Raw120ParentComposition.lean` checks the exact four-row refinement from the 1LB child to leaf 1341. The theorem `parent_lower` now proves that any weighted upper bound for the full raw120 parent is at least 224707. `parent_cover` discharges ten translated-cycle branches and the immediate-halt branch and takes exactly fourteen remaining child covers. `cover_from_ten` additionally takes the four previously accepted child theorems at their actual thresholds (0RF 14416, 0RB 223, 0RC 716, 1RB 749), leaving exactly ten explicit ordinary children, mass 10×25^5 = 97,656,250. `exact_if_children` proves the parent weighted maximum is exactly 224707 conditional on all fourteen covers at that threshold. All these theorems and both mass/count identities kernel-checked locally using the original compiled coverage dependencies and original Raw120Late/Raw120EasyCycles definitions; only standard axioms. This is a conditional composition, not a claim that the remaining children are closed. No new workflow is needed: include this module in the next relevant parent/1LB source closure.
