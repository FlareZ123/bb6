# Canonical raw40 and exact RDLC cylinder score

This checkpoint uses original canonical77 artifact 14997966221 (CI run 45554648116) and Lean 4.36.0-rc2. Kernel proofs use only propext, Classical.choice, Quot.sound. No CI run is claimed for these new files.

CanonicalPartial.lean proves quotient-aware partial audit soundness with least fresh successor, using tnf_branch_frontier and the original checked leaves. Raw40CanonicalCut.lean reduces the 303 raw residuals from the earlier cut to 189 canonical representatives and grafts them into the accepted 77 roster (265 entries). The generic quotient-to-quotient graft does not need to compose state permutations.

Raw40RDLCRefine.lean proves the exact weighted maximum 106 for 1RB0RD_1RC0LC_0RD---_1LD1LA_------_------ (5 holes, 9,765,625 raw completions). The exhaustive first-hole audit has 675 splits, 11,848 cycle leaves, 3,600 last-hole leaves, 78 FAR leaves; 1-to-5-state FAR certificates. A fully specified compatible machine halts after 105 ordinary moves with delay 0. The theorem rdlc_exact_weighted proves the bound and its optimality; rdlc_roster_sound consumes it, leaving 188 canonical raw40 representatives and a 264-entry global conditional frontier. This is not an exact result for BB(6) overall.

## Reproduce

Compile the earlier Raw40Pump, Raw40MorePumps, Raw40Partial, Raw40Graft in order using the coherent canonical77 olean directory. With this directory as working directory and LEAN_PATH including it and the dependency directory:

```
g++ -O3 -std=c++20 enumerate.cpp -o enumerate
mkdir -p RDLC/shards
(cd RDLC && ../enumerate 1RB0RD_1RC0LC_0RD---_1LD1LA_------_------)
cp RDLC-far5.txt RDLC/far5.txt
python3 certify_shards.py RDLC RDLC/shards 1RB0RD_1RC0LC_0RD---_1LD1LA_------_------ 106 Raw40RDLC
lean -o CanonicalPartial.olean CanonicalPartial.lean
lean -o Raw40CanonicalCut.olean Raw40CanonicalCut.lean
export LEAN_PATH="$LEAN_PATH:$PWD/RDLC/shards"
(cd RDLC/shards && lean -o Raw40RDLCBase.olean Raw40RDLCBase.lean && for f in Raw40RDLCKid*.lean; do lean -o "${f%.lean}.olean" "$f" || exit 1; done && lean -o Raw40RDLCAll.olean Raw40RDLCAll.lean)
lean -o Raw40RDLCRefine.olean Raw40RDLCRefine.lean
```

farbank.cpp reproduces the FAR discovery if desired: compile C++20, pipe numbered underscore-free open.txt rows into farbank 5. Candidate generator is untrusted: Lean independently validates every proof obligation, including the numeric weighted halt score. Do not use candidate enumeration output as a certified result for other cylinders.

The seven source blob SHAs in this commit match the local compiled/generated inputs. Generated Lean sources are reproducible from these inputs; they are not committed as redundant bulk files.
