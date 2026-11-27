# Raw56 E1=1RE — complete original-source sibling Cover

Parent partial table: `1RB---_1RC---_0RD---_1LD1LE_---1RE_------`.

## Accepted theorem and scope

**All compatible quotient completions of this exact E1=1RE sibling have weighted step bound 10,000.** The original-source Lean 4.36.0-rc2 acceptance run [46061898661](https://github.com/FlareZ123/bb6/actions/runs/46061898661), pinned to `c874776d819728050ba1c6eddb44237b358c387d`, completed all seven disjoint proof shards and the final consumer. The exported artifact is [15230025742](https://github.com/FlareZ123/bb6/actions/runs/46061898661/artifacts/15230025742), SHA-256 `efcfbc539c2beed16f8f551de54784d5eaa1be80bd7bf3485bd66c6d576be3c3`, 389,449,958 bytes. It contains the new objects and the final axiom log; the exact accepted base artifact 15160313745 remains a separate dependency.

- `BB6.Agent4Raw56REParent.all_quotient`: unconditional weighted bound 10000 for the exact quotient-compatible E1=1RE table.
- `BB6.Agent4Raw56REParent.all`: corresponding raw-compatible bound.
- `BB6.Agent4Raw56REParent.rootSound18Closed`: removes E1=1RE from the accepted 19-way root list at common bound 10000.
- The final source acceptance explicitly requires the standard axiom gate for `all_quotient` and `rootSound18Closed`; no unapproved axioms are accepted.

The first undefined E0 query occurs at step 10. Thirteen moves close by translated cycles; the other eleven are all covered by source-checked exact child proofs. RELA and RERB have weighted bound 7014; the remaining nine have bound 10000. The 291 holdouts after FAR5 were handled by 278 ordinary ngram/RLE, six transferred periodic-block/lag-XOR, four late first-query witnesses (1527, 1583, 4072, 7854 moves), and three universal growth proofs: RE0LF M269 (left binary counter), RE1LB M500 (right binary counter with accumulating 110 blocks), RE1RF M491 (five-phase periodic return adding four eight-cell blocks). Together with the original canonical split this gives the full sibling theorem, without any finite-time nonhalting assumption.

This is a local Raw56 sibling closure. The independently accepted E1=0RC sibling must be consumed by exact roster membership for a joint root reduction. No complete Raw56 parent Cover or global BB(6) roster removal follows yet.

A large literal automaton previously exceeded a local 4 GiB limit. Quotienting inverse stack states by their reachable-configuration profiles compressed the largest witnesses from 9672 to 204 and 7006 to 214 configurations; the original Lean checker certifies the compressed relation. The acceptance run used this exact repaired source rather than weakening the checker.

## Reproduce

Download artifact 15160313745 from the accepted workflow and unpack it to a directory containing manifest.json and the 747 checked modules. ZIP SHA256:
`6513147b3929ab6b707225b6592a882025e234d498ed8baca40216489b469b3d`.
Lean executable SHA256:
`db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00`.

```sh
cat source.tar.xz.b64.0[0-4] | base64 -d > source.tar.xz
sha256sum source.tar.xz
mkdir source
tar -xJf source.tar.xz -C source
cd source
python reproduce.py --base /path/to/a1-raw56-root-consumer --lean /path/to/lean
```

Archive SHA256 `bd70d009d0ca78be4eabe4efb47e4fed93a81c9dee56b999bc7ce7491d61d167`. The five parts are exact git blobs 5d02a6a4cbb8cb7ee814626a19632df8e676ab9d, 725ff7b98953718723e7f0fd222b103ae5ab82f6, 31692c09b5c3dad9c11083b6b6130f034f512e05, d86fab55ce8c620a764ad053fee128ea7953150d, 0bf71ccbe823e0a635fc9928aa69fce9e567af9a.

The bundle includes original C++ cut/FAR5 sources, generators, frozen discovery parameters, late leaves, the four growth modules, original TwoSidedAutomata checker, parent cut and parent consumer. It regenerates the certificate data instead of committing megabytes of generated Lean. The search is untrusted; all final claims depend on the original canonical checker and checked stack certificates. The accepted dependency closure is reused, not independently rebuilt. Use the compression patch before reproduction on memory-constrained runners.
