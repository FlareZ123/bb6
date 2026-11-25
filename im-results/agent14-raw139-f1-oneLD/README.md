# Raw139 F/1 = 1LD: complete original-semantics weighted closure

Parent codes: `[7,24,11,24,14,21,3,16,12,11,24,14]`. **WeightedBound 264**. Final theorem: `BB6.Agent14F1OneLD.all_completions_weighted`, for every compatible completion of the parent. Locally kernel-checked with the original compiled dependency closure from the successful neighboring sibling CI artifact, not the provisional copied model. No open leaf in this cylinder. This is not a claim of BB(6) exactness.

## Constructive partition

At scan bound 600, FAR size 3: 13 split nodes, 170 cycle leaves, 53 last-hole leaves, 45 FAR leaves, 32 inductive growth leaves; 300 terminal leaves total. Max query 258 yields bound 264. All 32 growth and nonhalting theorems checked against the original source semantics. 31 use the existing Agent48 emitter; H25 (table `[7,11,11,24,14,21,3,16,12,11,3,14]`) uses a genuinely nested binary-carry suffix. Blank entry 73, full phase cost 40n+83+coreCost(digitAt n), and increment of the growing prefix by four ones. The carry proof recurses under high digits with arbitrary left exterior. The final parent checker is composed from individually proved leaf decisions and 13 exhaustive 24-way branch proofs; no giant monolithic decide is required.

## Accepted kernel check and reproducibility

Original dependency artifact: Agent48 successful [run 45611897213](https://github.com/FlareZ123/bb6/actions/runs/45611897213), artifact 15021380200, source commit c512623e68b633e28fc140370abee778cfaf0939. ZIP SHA-256 910e843066c3bbf1ddb21d2b798c850cb671e66b743f4c91d750c6be723bc570; all 57 .olean hashes matched manifest. Lean binary SHA-256 db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00 (4.36.0-rc2) matches upstream manifest. The three new source modules were compiled locally in order Carry, Hard, Cover with LEAN_PATH pointing to the original artifact build directory and local output. Final output:

```
'BB6.Agent14F1OneLD.checked' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent14F1OneLD.all_completions_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The 32 growth/never pairs and carry theorem all depend only on propext and Quot.sound. All three .olean outputs generated successfully. The source hashes are pinned in reproduce.sh. Full clean reproduction: `bash im-results/agent14-raw139-f1-oneLD/reproduce.sh` with Lean 4.36.0-rc2 and Python 3. Independent full CI for this sibling has not been dispatched (no workflow dispatch connector in this invocation); the local kernel check used the accepted original-source artifact. This covers the exact parent cylinder and may be integrated into a roster once the appropriate canonical graft verifies its correspondence.
