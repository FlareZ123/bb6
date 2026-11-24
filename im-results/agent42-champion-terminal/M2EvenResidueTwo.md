# Marker-2 even residue-two source row (m=2, n=8k+2)

**Status (24 November 2026):** the original-TM2 q4 prefix, reset prefix, and complete counted increment have passed the exact 39-project-module local Lean 4.36.0-rc2 closure. This closes the residue-two transition dependency required at authentic root row 22. The root wrapper and complete blank-to-halt chain are still separate proof obligations; no exact champion score or BB(6) value is established here.

## Exact source contract

For every natural L,k,a,b and integer h satisfying L≥3, 8k+2<2^L, a>0, the original TM2 run starting at `s1Config L (8*k+2) 2 a 0 b h` has:

- `m2Even_residue2_q4_prefix_source` in [M2EvenResidueTwo.lean](M2EvenResidueTwo.lean): a q4 prefix of exactly 44+12a steps with the source-specific q4 tape.
- `m2Even_residue2_q4_reset_prefix_source`: an exact reset prefix of 83+12a+3b steps reaching `s1Config L (8*k+1) 1 (a+b+2) (2^b-1) 0 (h+5+3*b)`.
- `m2Even_residue2_counted_increment_source` in [M2EvenResidueTwoCounted.lean](M2EvenResidueTwoCounted.lean): an exact complete increment reaching `s1Config L (8*k+1) 1 (a+b+2) 0 (2^b-1) (h+5+3*b)`, at cost `proposedIncrementCost 2 (8*k+2) a b = 6*4^b + 42*2^b - 9*b + 35 + 12*a`.

The last theorem composes the source reset with the generic counted S1 drain, which was independently accepted by CI 45348136742 and is now reused without an additional drain proof.

## Exact local source acceptance

Agent 44 used the GitHub Actions [source bundle from run 45348259251](https://github.com/FlareZ123/bb6/actions/runs/45348259251), artifact 14899361532, pinned source commit `6ce88db333f23b7ca99cf9295db3ba563a06781d`. The 38 predecessor module blobs used in the local compile were also matched against main at `c6a26f1aaeb7d1473f4d73510a55526bc6f9cb8b`. The residue-two prefix source blob is `b22d9211d7138e8717336191aea6f5dfb6f7746e`.

The first counted-adapter compile failed because the source namespaces for `tm2` and `s1Config` were not opened; Lean's autoImplicit treated the latter as an unknown variable. The repair opens `BB6Coverage.Agent48Champion` and `BB6Coverage.Agent8S1Encoder` and sets autoImplicit false. The resulting tested adapter blob is `1050a8aa62dc09f65afe83a951d799624d9cc693`.

The 39-module closure was compiled topologically with the supplied Lean 4.36.0-rc2 executable (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a), using `tools/lean_compile_closure.py` and reusing only unchanged successfully compiled predecessor modules on resumption. The final adapter compile exited zero. The printed axiom profiles are:

| Exported declaration | Axioms |
| --- | --- |
| binDec_residue2, binDec_residue1 | propext, Quot.sound |
| m2Even_residue2_q4_prefix_source | propext, Classical.choice, Quot.sound |
| m2Even_residue2_q4_reset_prefix_source | propext, Classical.choice, Quot.sound |
| m2Even_residue2_counted_increment_source | propext, Classical.choice, Quot.sound |

No sorryAx or native_decide occurs in these accepted profiles. The acceptance here is local exact-source compilation, not a new CI run. Reproduce by invoking `python tools/lean_compile_closure.py im-results/agent42-champion-terminal/M2EvenResidueTwoCounted.lean --override M2EvenResidueTwo=im-results/agent42-champion-terminal/M2EvenResidueTwo.lean --workdir /tmp/m2-residue-two-local` from the repository with Lean 4.36.0-rc2 on PATH. No Terminal imports are used by this closure.

## Binary boundary and finite bridge

The source establishes
- binDec L (8k+2) = d1 ++ d0 ++ d1 ++ binDec (L-3) k;
- binDec L (8k+1) = d0 ++ d1 ++ d1 ++ binDec (L-3) k.

The input and output head-facing words share the tail `[true] ++ d1 ++ binDec (L-3) k ++ lh` beyond equal prefixes of length 3a+12. The existing 38-step n=6 bridge operates inside the half-line starting at h-(3a+11). A (3a+2)-cell counted left sweep, the bridge, and a 3a-step E-scan yield the 44+12a prefix. The suffix contributes 39+3b; the counted drain adds 6*4^b + 42*2^b - 12*b - 48 steps. The finite replay previously reported 120/120 endpoint matches, but the quantified source theorem now supersedes that experiment as evidence for the transition.

## Authentic-root boundary and next gate

The intended middle-22 source input is m=2, n=16r-6=8(2r-1)+2, following middle rows 20 and 21. The counted theorem now supplies the exact transition to m=1, n=16r-7. The next useful gate is the actual transitive import closure of TM63RootMiddle22 (and then later root compositions); the source theorem does not establish reachability of the input from blank. Keep this intermediate transition in im-results until the authentic blank-root and exact step-count theorems are accepted.
