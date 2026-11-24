# Machine C root32: simultaneous full three-residual affine-cone closure

**Status:** the original nine-cylinder proof is source-accepted in CI [45358255752](https://github.com/FlareZ123/bb6/actions/runs/45358255752), 60 project modules, standard axioms only (certificate list has no axioms). The new arbitrary-precision extension below awaits a targeted source build. No whole-machine or BB(6) decision.

## Exact target and mechanism

The existing [corrected source reduction](../agent3-c-bounce-inverse/B2Q0FourStepPath.md) has three alternatives, D0E(t), L(t), P7E1E(t), after a blank-reachable high-stop target T(u)=(1048576u+70538,3) with u=1802+6720t. The third branch cannot be dropped. The new [Root32ConeClosure.lean](Root32ConeClosure.lean) imports the genuine Root32HighStopP7 source reduction and [Agent13's sound all-parent affine cone checker](../agent13-residual-frontier/AffineConeKernel.lean). Each ray t=b+m*s is checked on all three residuals at once, using the complete original section-parent equations and odd-right forbidden-image leaves. Successful finite proof trees exclude every natural s and every machine time; fuel 24 bounds proof-tree depth only. No prior handwritten A4 or D0E/L branch proof is assumed.

The exact root hypotheses are r%64=32, E=201+3360*(6657+8192*r), and 18018+211*u+22155*r=20*2^(E-13). The source root32 index map gives (t+j)%8192=3780 with r=32+64*j. The wrapper proves the resulting original root predicate via modular cancellation.

| t residue | t modulus | r residue | r modulus |
|---:|---:|---:|---:|
| 1 | 16 | 224 | 1024 |
| 47 | 2048 | 107872 | 131072 |
| 559 | 8192 | 206176 | 524288 |
| 31 | 256 | 10592 | 16384 |
| 7183 | 8192 | 306528 | 524288 |
| 2575 | 8192 | 77152 | 524288 |
| 159 | 1024 | 35168 | 65536 |
| 719 | 8192 | 195936 | 524288 |
| 7839 | 8192 | 264544 | 524288 |

The nine disjoint cylinders are a simultaneous three-branch closure, including four full prior parameter families (t=1 mod16, 31 mod256, 159 mod1024, 7839 mod8192) and refinements of t=47 mod256, 15 mod512 and 719 mod1024. The older withdrawn two-branch arguments are not used. This union is 561 classes modulo 8192 in j; that is parameter coverage, not a fraction of machines settled. Remaining root32 classes include t=79 mod512, 1167 mod4096 and the other partial-family residues. Do not infer a whole high-stop or whole-machine decision.

## Acceptance boundary

The local toolchain was reconstructed successfully (Lean 4.36.0-rc2, b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). The actual executable definitions of Agent13's checker were copied verbatim to a local module, and the new wrapper was compiled against abstract interfaces with the exact signatures of the imported source facts. In that preflight, certificates_checked had **no axioms**, and the full wrapper compiled against those explicitly assumed interfaces. This does not yet certify source imports or their transitive axioms. Local git ls-remote failed with Could not resolve host: github.com; the source archive was unavailable through the download path. The exact original source checkout cannot be built locally in this environment. A focused source-closure acceptance check on the existing manual Agent3 workflow is the next step. No new workflow and no broad or per-commit dispatch.

Exported source statements to audit: run_cone_excluded, three_excluded_sound, certificates_checked, root32_no_highstop_of_t, root32_no_highstop. The last is the actual high-stop exclusion under the original exact root equation.

## Arbitrary-precision root-index bridge (24 November, current incarnation)

The exact normalized equation implies 17300+22155(t+j) ≡ 0 mod 2^p for every p≤E−17. Since 22155 is odd, the solution in t modulo 2^p is unique. [Root32Precision.lean](Root32Precision.lean) computes it via one binary lift at a time, and proves correctness and periodicity for all p,j,t in local Lean 4.36.0-rc2, with standard axioms only. The proof does not construct the enormous root exponent or enumerate all residues. The added source wrapper `root32_no_highstop_at_precision` takes any p and proof-tree fuel f with `precisionExcluded f p (r/64)=true`, covering all three corrected residuals on the root cylinder. This replaces fixed-modulus certificate-list construction by a general executable criterion. It is pending original-source compilation; the standalone arithmetic proof is already compiled locally.

Two new witness cylinders at p=16 are t=49743 mod65536 (a refinement of t=79 mod512) and t=58511 mod65536 (a refinement of t=1167 mod4096); their root indices are j=60533 or 51765 mod65536, i.e. r=3874144 or 3312992 mod4194304. A local Python implementation of the unchanged checker closes all three residuals in each case at fuel 13; the new source uses fuel 24 and kernel `by decide`. This is a new target exclusion conditional on source acceptance, not a claim that other lifts of either formerly unresolved class are excluded.

Local exact repository checkout remains blocked by DNS for github.com; no new workflow. The existing focused root32_cone_only action is the acceptance gate for the changed source.
