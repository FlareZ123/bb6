# Raw120 E0=1LB index 1341: late halt rather than nonhalting

**Status: exact computational first-hole query, original-source proof candidate.** Two independently implemented primitive simulations and the packed-stack generator agree that the partial table

`1RB---_1RC0LF_0RD0RF_1LD1RE_1LB1LE_0RA0LE`

(the exact index 1341 of the pinned 4351-leaf 1LB roster) first queries A1 after 224705 live steps. Head = 147; visited interval [-382,151]; 521 ones. The sole halt completion thus has 224706 primitive steps from canonical blank A. F0=0RA adds exactly one possible zero-write initial step; the complete incoming-delay list is [0,1]. The exact proposed weighted threshold for the entire 25-completion cylinder is **224707**. The other 24 completions have no halt transitions at all.

This corrects the earlier provisional 3793 sibling bound and removes the need for a nonhalting certificate for index 1341. It does not close the full 1LB sibling until every other leaf is accepted, nor raw120 or BB(6).

## Proof route

- PackedZipper.lean proves that binary natural-number stacks preserve the exact sparse zipper's reads (including failure and implicit zeroes). Local Lean 4.36.0-rc2 checked the same definitions and theorem against a copied exact computational zipper interface: standard axioms [propext, Quot.sound]. No source transfer is claimed from that local preflight alone.
- generate.py emits 225 independently checked segments grouped into 15 proof modules. All checkpoints are supplied by the untrusted Python generator; Lean checks each with ordinary decide, then joins their exact lengths. The generator also independently replays the original primitive tape using a set of ones. The base module and a shorter 9000-step local packed trace passed; a full local replay hit the execution limit. The 15-shard approach enables parallel source acceptance.
- Raw120Late1341.lean consumes the packed query through the unchanged ZipThreeHoleAudit, computes the exact delay list, and proposes `lateChecked B hB`, `exact_halt`, and `exact_weighted`. These remain pending original-source compilation.

Reproduce from the repository root:
```sh
python im-results/agent13-coverage/unpack.py
python im-results/agent13-raw120-late1341/generate.py
python tools/lean_compile_closure.py --workdir /tmp/a13-late1341 --jobs 3 im-results/agent13-raw120-late1341/Raw120Late1341.lean
```

For ingestion, render the exact leaf as `.last 224705 (0,true)` and use `lateChecked B hB` instead of reducing the entire primitive trace a second time. If the leaf is nested inside a checked subtree, expose it as its own child and compose with the existing split checker. Preserve all other sibling obligations. No change to the accepted canonical roster is claimed.
