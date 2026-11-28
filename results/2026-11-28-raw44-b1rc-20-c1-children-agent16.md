# Raw44 B1=0RC: source-accepted C1=0LE and C1=0LF weighted Covers

**Status:** original-source Lean 4.36.0-rc2 compilation and the repository axiom audit passed in [GitHub Actions run 46167386448](https://github.com/FlareZ123/bb6/actions/runs/46167386448). The 45 residual nonhalting certificates independently passed in [run 46166705089](https://github.com/FlareZ123/bb6/actions/runs/46166705089).

## Theorem

Let P_E and P_F be the following five-hole partial transition tables, in the repository's standard six-state, two-symbol encoding:

- P_E = 1RB---_1RC0RC_0RD0LE_1LD1LB_------_------
- P_F = 1RB---_1RC0RC_0RD0LF_1LD1LB_------_------

Then the source-checked Lean theorems establish:

    ∀ M, compatible P_E M → WeightedBound 373 M
    ∀ M, compatible P_F M → WeightedBound 373 M

Here WeightedBound B M is the repository predicate

    ∀ k d, HaltsAfter M k → d ∈ delays (zeroNext M) 0 → d + k + 1 ≤ B.

Both parents fix the initial transition A0=1RB, which writes one. Thus the zero-prefix delay is trivial in these children; the theorem supplies a uniform bound of 373 in the formal weighted convention, including the halt query.

## Proof construction

### C1=0LE: finite partition plus 45 nonhalting residuals

The C1=0LE child contains exactly 25^5 = 9,765,625 complete machines. The deterministic discovery partition has:

| Leaf class | Count of complete machines |
| --- | ---: |
| First-query halts | 761,725 |
| Translated-cycle closures | 8,685,175 |
| Sparse n-gram closures | 160,225 |
| Last-hole certificates | 139,375 |
| Residual hard tables | 19,125 |
| **Total** | **9,765,625** |

The search tree has 33,721 nodes, 1,405 recursive splits, 5,575 last-hole leaves, 25,927 translated-cycle leaves and 769 n-gram leaves. Its maximum first-query time is 367, giving the weighted threshold 367+6=373.

The residual mass consists of 40 one-hole tables (1,000 completions), four two-hole tables (2,500 completions) and one three-hole table (15,625 completions). Agent48's generic AutoPump search found a pumping certificate for every one of the 45 tables. The generated certificates were converted to the Agent46AutoPump kernel format by im-results/agent16-raw44/prepare_0le_autopump.py and checked with the original Lean kernel. All 45 check_never theorems and the axiom audit passed in run 46166705089. The builder fixes the JSONL certificate stream by SHA256 a264eb5744ebc6abc59d2013b3cc962e04cce3de99451fa11e6b8538dfdce611.

The finite split/cycle/n-gram tree, the 45 residual proofs and the generated parent Cover were then compiled together. This establishes the P_E theorem above.

### C1=0LF: state-renaming transport

P_F is the image of P_E under the state permutation swapping E and F and fixing the root state A. im-results/agent16-raw44/Raw44C1LEFESymmetry.lean proves the exact partial-table equality with renamePartial and applies weighted_cover_transport from im-results/agent16-weighted-symmetry/WeightedSymmetry.lean. The same threshold 373 therefore holds for every completion of P_F. This is a theorem-level symmetry transfer, not a second empirical search.

The complete generated source closure and the E/F transfer theorem passed original-source compilation and the repository axiom audit in run 46167386448.

## Reproduction

From the repository root:

    node im-results/agent16-raw44/discover.cjs '{"second":"0LE"}'
    python im-results/agent16-raw44/prepare_0le_autopump.py
    python im-results/agent19-raw40-cut/emit_autopump.py im-results/agent16-raw44/0LE-autopump-certs.jsonl BB6.Agent16Raw44.C1LE > im-results/agent16-raw44/Raw44C1LEAutoPump.lean
    node im-results/agent16-raw44/generate_cut.cjs im-results/agent16-raw44/generated-c1le 128 0LE

The CI target raw44-cut-0le-assembled then compiles im-results/agent16-raw44/Raw44C1LEFESymmetry.lean, which imports the generated Raw44CutAssembled module and checks the transported P_F theorem as part of the same source closure.

Relevant proof infrastructure:
- im-results/agent16-raw44/generate_cut.cjs
- im-results/agent16-raw44/prepare_0le_autopump.py
- im-results/agent16-raw44/Raw44C1LEFESymmetry.lean
- im-results/agent46-raw13-cut/Agent46AutoPump.lean
- im-results/agent16-weighted-symmetry/WeightedSymmetry.lean
- im-results/agent13-weighted-first-one/SparseBlankDelay.lean (definition of WeightedBound)

## Effect on the Raw44 B1=0RC frontier

The two new children each cover 25^5 = 9,765,625 machines. Combined, they add 19,531,250 source-classified machines to the previous 18/25 frontier. The updated B1=0RC subspace now has 20 of 25 C1 actions source-certified:

- Seven complete five-hole Covers: C1=0LA (126), 0LE (373), 0LF (373), 0RA (375), 0RE (211), 0RF (211), and 1RA (211).
- Thirteen additional source-certified translated-cycle nonhalting children.

These disjoint branches classify 195,312,500 of the 244,140,625 complete machines in the B1=0RC subspace, exactly 80%. Five C1 actions in this subspace remain open, as do the other B1 branches and the full Raw44 parent.

**This is a local weighted-cover result, not a solution of BB(6). The exact value of BB(6) remains unknown.**

See also the earlier [18/25 Raw44 frontier](2026-11-28-raw44-b1rc-18-c1-children-agent16-agent8.md) and the [thirteen nonhalting children](2026-11-28-raw44-b1rc-thirteen-nonhalting-children-agent8.md).
